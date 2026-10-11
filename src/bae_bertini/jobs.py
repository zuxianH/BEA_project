"""Server-owned jobs survive Streamlit reruns and browser reconnections."""
from collections import Counter, deque
from dataclasses import dataclass, replace
from pathlib import Path
import threading
import time

from .paths import ROOT, STATE, local_path
from .config import parse_shape, preview
from .run_events import timestamp
from datetime import datetime
import os
import queue
import signal
import subprocess
import uuid
import json
import logging


def failure_hint(diagnostic):
    """Explain known failures without guessing the cause of unknown output."""
    text = diagnostic.lower()
    if 'bash 4.3' in text or 'declare: -a: invalid option' in text:
        return 'Install a newer Bash with `brew install bash` on macOS, then retry in Studio.'
    if any(word in text for word in ('not found', 'no such file or directory', 'filenotfounderror')):
        return 'Check the executable and file paths. Configure WOLFRAM_KERNEL if Mathematica is not on PATH.'
    if 'timeout' in text or 'timed out' in text:
        return 'The calculation timed out. Inspect the worker logs and consider increasing Backend timeout.'
    if any(word in text for word in ('tracking failed', 'tracker failed', 'non-success bertini status',
                                     'maxnumsteps', 'step limit', 'maximum number of steps')):
        return 'Inspect the tracking diagnostic before adjusting precision, tracking tolerance, or maximum steps.'
    return diagnostic.strip()[-4000:] or 'No diagnostic was produced. Inspect the full log and exit code.'


@dataclass(frozen=True)
class LogEntry:
    timestamp: str
    level: str
    source: str
    message: str
    entry_id: int | None = None

    def formatted(self):
        return f'{self.timestamp} {self.level:7} [{self.source}] {self.message.rstrip()}'


@dataclass(frozen=True)
class TableauState:
    entry_id: int
    tableau: str
    status: str = 'queued'
    job_id: str | None = None
    timestamp: str = ''
    exit_code: int | None = None
    reason: str = ''
    stdout_path: str | None = None
    stderr_path: str | None = None


class EventLogHandler(logging.Handler):
    def __init__(self, events):
        super().__init__()
        self.events = events

    def emit(self, record):
        self.events.put(('log', LogEntry(timestamp(), record.levelname, 'studio',
                                         record.getMessage()[-16000:], getattr(record, 'entry_id', None))))


@dataclass(frozen=True)
class Snapshot:
    running: bool
    cancelled: bool
    code: int | None
    elapsed: float
    output: str
    log_path: Path | None
    destination: str
    entries: tuple = ()
    tableaux: tuple = ()
    total: int | None = None
    counts: dict | None = None
    issues: tuple = ()


class RunManager:
    """One shared calculation per local server, with a bounded live log."""

    def __init__(self):
        self.lock = threading.RLock()
        self.job = None
        self.lines = deque(maxlen=2000)
        self.started = self.finished = None
        self.code = None
        self.destination = ''
        self.entries = deque(maxlen=2000)
        self.tableaux = {}
        self.total = None
        self.issues = []

    def start(self, args, env, log_directory=None):
        with self.lock:
            if self.job is not None and self.finished is None:
                raise ValueError('A calculation is already running. Stop it before starting another.')
            self.job = Job(args, env, log_directory)
            self.lines.clear()
            self.entries.clear()
            self.tableaux.clear()
            self.total = None
            self.issues.clear()
            if self.job.tableau:
                self.total = 1
                self.tableaux[1] = TableauState(1, self.job.tableau, status='running',
                                               stdout_path=str(self.job.log_path))
            self.started, self.finished, self.code = time.monotonic(), None, None
            self.destination = env.get('BERTINI_RESULT_SYT_DIR', '')
            self.job.start()
            threading.Thread(target=self._collect, args=(self.job,), daemon=True).start()

    def _collect(self, job):
        # Drain even when all browsers are closed, so queued output stays bounded.
        while True:
            kind, value = job.events.get()
            with self.lock:
                if kind == 'done':
                    self.code, self.finished = value, time.monotonic()
                    for entry_id, record in self.tableaux.items():
                        if record.status in {'queued', 'running'}:
                            status = ('not_run' if record.status == 'queued' else
                                      'cancelled' if job.cancelled.is_set() else
                                      'succeeded' if job.tableau and value == 0 else 'failed')
                            self.tableaux[entry_id] = replace(record, status=status,
                                exit_code=value if record.status == 'running' else None,
                                reason='' if status == 'succeeded' else
                                'Stopped by user.' if job.cancelled.is_set() else
                                'The batch ended before this entry finished.' if job.batch else
                                ''.join(self.lines)[-4000:])
                    return
                if kind == 'lifecycle':
                    if value['kind'] == 'total':
                        self.total = value['total']
                    elif value['kind'] == 'batch_error':
                        self.issues.append(value['reason'])
                    else:
                        entry_id = value['entry_id']
                        previous = self.tableaux.get(entry_id)
                        if previous and (previous.tableau != value['tableau'] or
                            previous.status not in {'queued', 'running'}):
                            job.logger.warning('Ignored inconsistent lifecycle event: %s', repr(value)[-16000:])
                            continue
                        fields = {key: value[key] for key in TableauState.__dataclass_fields__ if key in value}
                        self.tableaux[entry_id] = replace(previous, **fields) if previous else TableauState(**fields)
                elif kind == 'log':
                    self.entries.append(value)
                else:
                    line = str(value)[-16000:]
                    self.lines.append(line)
                    self.entries.append(LogEntry(timestamp(), 'RAW', 'backend', line,
                                                 1 if job.tableau else None))

    def stop(self):
        with self.lock:
            if self.job is not None and self.finished is None:
                self.job.cancel()

    def close(self):
        self.stop()
        if self.job is not None:
            self.job.done.wait(10)

    def snapshot(self):
        with self.lock:
            counts = dict.fromkeys(('running', 'succeeded', 'failed', 'skipped', 'cancelled', 'not_run'), 0)
            counts.update(Counter(record.status for record in self.tableaux.values()))
            pending = max(0, (self.total or 0) - sum(counts[key] for key in
                          ('running', 'succeeded', 'failed', 'skipped', 'cancelled', 'not_run')))
            counts['pending'] = pending if self.finished is None else 0
            if self.finished is not None:
                counts['not_run'] += pending
            return Snapshot(
                running=self.job is not None and self.finished is None,
                cancelled=self.job is not None and self.job.cancelled.is_set(),
                code=self.code,
                elapsed=(self.finished or time.monotonic()) - self.started if self.started else 0,
                output=''.join(self.lines)[-160000:],
                log_path=self.job.log_path if self.job else None,
                destination=self.destination,
                entries=tuple(self.entries), tableaux=tuple(self.tableaux.values()),
                total=self.total, counts=counts,
                issues=tuple(self.issues),
            )



class Job:
    """One process group; UI events are passed through a thread-safe queue."""
    def __init__(self, args, env, log_directory=None):
        self.args, self.env = list(args), dict(env)
        self.events = queue.Queue()
        self.process = None
        self.cancelled = threading.Event()
        self.done = threading.Event()
        self.lock = threading.Lock()
        self.log_directory = log_directory or STATE / 'logs'
        self.log_path = self.log_directory / (datetime.now().strftime('%Y%m%d-%H%M%S-') + uuid.uuid4().hex[:6] + '.log')
        self.thread = threading.Thread(target=self._run, daemon=True)
        self.batch = any(Path(str(arg)).name == 'submit_run_single_jobs.sh' for arg in args)
        self.tableau = None
        if not self.batch and args:
            try:
                self.tableau = parse_shape(str(args[-1]), True)
            except ValueError:
                pass
        self.event_path = self.log_path.with_suffix('.events.jsonl')
        self.event_offset = 0
        if self.batch:
            self.env['BAE_STUDIO_EVENTS_FILE'] = str(self.event_path)
            if '--no-logs' not in self.args and '--logs' not in self.args:
                self.args += ['--logs', str(self.log_path.with_suffix('') / 'workers')]
        self.logger = logging.Logger('studio.run.' + self.log_path.stem, logging.INFO)
        self.logger.addHandler(EventLogHandler(self.events))

    def _read_lifecycle(self):
        if not self.batch or not self.event_path.exists():
            return
        try:
            with self.event_path.open('rb') as stream:
                stream.seek(self.event_offset)
                while True:
                    raw = stream.readline()
                    if not raw or not raw.endswith(b'\n'):
                        break
                    self.event_offset = stream.tell()
                    try:
                        event = json.loads(raw)
                        if not isinstance(event, dict):
                            raise ValueError('Expected an event object.')
                        datetime.fromisoformat(event['timestamp'])
                        kind = event['kind']
                        if kind == 'total':
                            if type(event['total']) is not int or event['total'] < 0:
                                raise ValueError('Invalid batch total.')
                        elif kind == 'batch_error':
                            if not isinstance(event['reason'], str):
                                raise ValueError('Invalid batch diagnostic.')
                        elif kind == 'output':
                            if (type(event['entry_id']) is not int or event['entry_id'] < 1
                                or event['source'] not in ('stdout', 'stderr')
                                or not isinstance(event['message'], str)):
                                raise ValueError('Invalid worker output.')
                            entry = LogEntry(event['timestamp'], 'RAW',
                                f"entry {event['entry_id']} {event['source']}",
                                event['message'], event['entry_id'])
                            self.events.put(('log', replace(entry, message=entry.message[-16000:])))
                            with self.log_path.open('a', encoding='utf-8') as log:
                                log.write(entry.formatted() + '\n')
                            continue
                        else:
                            statuses = dict(queued='queued', started='running', finished=None, skipped='skipped')
                            if kind not in statuses or type(event['entry_id']) is not int or event['entry_id'] < 1:
                                raise ValueError('Invalid lifecycle event.')
                            event['tableau'] = parse_shape(event['tableau'], True)
                            if kind == 'finished':
                                if type(event['exit_code']) is not int:
                                    raise ValueError('Invalid worker exit code.')
                                expected = 'succeeded' if event['exit_code'] == 0 else 'failed'
                            else:
                                expected = statuses[kind]
                            if event['status'] != expected:
                                raise ValueError('Invalid worker status.')
                            if 'reason' in event and not isinstance(event['reason'], str):
                                raise ValueError('Invalid reason.')
                            for key in ('job_id', 'stdout_path', 'stderr_path'):
                                if key in event and event[key] is not None and not isinstance(event[key], str):
                                    raise ValueError(f'Invalid {key}.')
                        self.events.put(('lifecycle', event))
                        if kind == 'total':
                            self.logger.info('Batch contains %d selected entries.', event['total'])
                        elif kind == 'batch_error':
                            self.logger.error('Batch error: %s', event['reason'])
                        elif kind != 'queued':
                            level = logging.ERROR if event['status'] == 'failed' else logging.INFO
                            duration = event.get('elapsed_seconds')
                            timing = f' ({duration:.3f} s)' if type(duration) in (int, float) and duration >= 0 else ''
                            self.logger.log(level, 'Entry %s %s%s: %s%s', event['entry_id'], event['status'],
                                timing, event['tableau'], ' · ' + event.get('reason', '') if event.get('reason') else '',
                                extra={'entry_id': event['entry_id']})
                    except (ValueError, KeyError, TypeError, RecursionError) as exc:
                        self.logger.warning('Ignored malformed lifecycle event (%s): %s', exc,
                                            raw.decode('utf-8', errors='replace')[:16000].rstrip())
        except OSError as exc:
            self.logger.warning('Cannot read lifecycle journal: %s', exc)

    def start(self):
        self.thread.start()

    def _signal(self, sig):
        with self.lock:
            if self.process is not None:
                try:
                    os.killpg(self.process.pid, sig)
                except ProcessLookupError:
                    pass

    def cancel(self):
        self.cancelled.set()
        self._signal(signal.SIGTERM)

    def _run(self):
        code = -1
        file_handler = None
        try:
            self.log_directory.mkdir(parents=True, exist_ok=True)
            file_handler = logging.FileHandler(self.log_path, encoding='utf-8')
            file_handler.setFormatter(logging.Formatter('%(asctime)s %(levelname)s [studio] %(message)s'))
            self.logger.addHandler(file_handler)
            self.logger.info('Calculation starting.')
            with self.log_path.open('a', encoding='utf-8') as log:
                log.write(preview(self.args, self.env) + '\n\n')
                log.flush()
                # Clear inherited tracker overrides so the form fully defines this run.
                environment = {k: v for k, v in os.environ.items() if not k.startswith('BERTINI_')}
                environment.update(self.env)
                with self.lock:
                    if self.cancelled.is_set():
                        return
                    self.process = subprocess.Popen(self.args, cwd=ROOT, env=environment,
                                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                                    text=True, errors='replace', bufsize=1, start_new_session=True)
                def read_output():
                    for line in self.process.stdout:
                        log.write(line)
                        log.flush()
                        self.events.put(('output', line))
                reader = threading.Thread(target=read_output, daemon=True)
                reader.start()
                while self.process.poll() is None:
                    self._read_lifecycle()
                    if self.cancelled.wait(.1):
                        self._signal(signal.SIGTERM)
                        try:
                            self.process.wait(timeout=3)
                        except subprocess.TimeoutExpired:
                            pass
                        # Descendants may outlive a shell that already exited.
                        self._signal(signal.SIGKILL)
                        break
                code = self.process.wait()
                if self.cancelled.is_set():
                    self._signal(signal.SIGKILL)
                reader.join(timeout=5)
                if reader.is_alive():
                    self._signal(signal.SIGKILL)
                    reader.join(timeout=2)
                self.process.stdout.close()
                self._read_lifecycle()
                log.write(f'\nExit code: {code}; cancelled: {self.cancelled.is_set()}\n')
        except Exception as exc:
            self.events.put(('output', f'Could not run calculation: {exc}\n'))
            self.logger.exception('Could not run calculation: %s', exc)
        finally:
            if self.cancelled.is_set():
                self.logger.warning('Calculation stopped by user.')
            elif code == 0:
                self.logger.info('Calculation finished successfully.')
            else:
                self.logger.error('Calculation finished with exit code %s.', code)
            if file_handler:
                self.logger.removeHandler(file_handler)
                file_handler.close()
            self.done.set()
            self.events.put(('done', code))
