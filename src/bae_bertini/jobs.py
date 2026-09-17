"""Server-owned jobs survive Streamlit reruns and browser reconnections."""
from collections import deque
from dataclasses import dataclass
from pathlib import Path
import threading
import time

from .paths import ROOT, STATE, local_path
from .config import preview
from datetime import datetime
import os
import queue
import signal
import subprocess
import uuid


@dataclass(frozen=True)
class Snapshot:
    running: bool
    cancelled: bool
    code: int | None
    elapsed: float
    output: str
    log_path: Path | None
    destination: str


class RunManager:
    """One shared calculation per local server, with a bounded live log."""

    def __init__(self):
        self.lock = threading.RLock()
        self.job = None
        self.lines = deque(maxlen=2000)
        self.started = self.finished = None
        self.code = None
        self.destination = ''

    def start(self, args, env, log_directory=None):
        with self.lock:
            if self.job is not None and self.finished is None:
                raise ValueError('A calculation is already running. Stop it before starting another.')
            self.job = Job(args, env, log_directory)
            self.lines.clear()
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
                    return
                self.lines.append(str(value)[-16000:])

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
            return Snapshot(
                running=self.job is not None and self.finished is None,
                cancelled=self.job is not None and self.job.cancelled.is_set(),
                code=self.code,
                elapsed=(self.finished or time.monotonic()) - self.started if self.started else 0,
                output=''.join(self.lines)[-160000:],
                log_path=self.job.log_path if self.job else None,
                destination=self.destination,
            )



class Job:
    """One process group; UI events are passed through a thread-safe queue."""
    def __init__(self, args, env, log_directory=None):
        self.args, self.env = args, env
        self.events = queue.Queue()
        self.process = None
        self.cancelled = threading.Event()
        self.done = threading.Event()
        self.lock = threading.Lock()
        self.log_directory = log_directory or STATE / 'logs'
        self.log_path = self.log_directory / (datetime.now().strftime('%Y%m%d-%H%M%S-') + uuid.uuid4().hex[:6] + '.log')
        self.thread = threading.Thread(target=self._run, daemon=True)

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
        try:
            self.log_directory.mkdir(parents=True, exist_ok=True)
            with self.log_path.open('w', encoding='utf-8') as log:
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
                log.write(f'\nExit code: {code}; cancelled: {self.cancelled.is_set()}\n')
        except Exception as exc:
            self.events.put(('output', f'Could not run calculation: {exc}\n'))
        finally:
            self.done.set()
            self.events.put(('done', code))
