"""Optional Studio lifecycle journal shared by the batch shell and its workers."""
import argparse
from datetime import datetime
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import threading
import time

from .config import parse_shape


def timestamp():
    return datetime.now().astimezone().isoformat(timespec='milliseconds')


def emit(event):
    path = os.environ.get('BAE_STUDIO_EVENTS_FILE')
    if not path:
        return
    record = dict(event, timestamp=timestamp())
    try:
        with open(path, 'a', encoding='utf-8') as stream:
            fcntl.flock(stream, fcntl.LOCK_EX)
            stream.write(json.dumps(record, ensure_ascii=True) + '\n')
            stream.flush()
    except OSError as exc:
        print(f'Studio lifecycle journal unavailable: {exc}', file=sys.stderr, flush=True)


def log_tail(path, limit=16000):
    if not path:
        return ''
    try:
        with Path(path).open('rb') as stream:
            stream.seek(0, 2)
            stream.seek(max(0, stream.tell() - limit))
            return stream.read(limit).decode('utf-8', errors='replace')
    except OSError:
        return ''


def worker(entry_id, job_id, tableau, stdout_path, stderr_path, command):
    context = dict(entry_id=entry_id, job_id=job_id, tableau=parse_shape(tableau, True),
                   stdout_path=stdout_path or None, stderr_path=stderr_path or None)
    emit(dict(context, kind='started', status='running'))
    code = 1
    reason = ''
    started = time.monotonic()
    try:
        with open(stdout_path or os.devnull, 'w', encoding='utf-8') as stdout, \
             open(stderr_path or os.devnull, 'w', encoding='utf-8') as stderr:
            with subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                  text=True, errors='replace', bufsize=1) as process:
                def forward(stream, destination, source):
                    for line in stream:
                        destination.write(line)
                        destination.flush()
                        emit(dict(kind='output', entry_id=entry_id, source=source, message=line))
                    stream.close()
                readers = [threading.Thread(target=forward, args=args) for args in (
                    (process.stdout, stdout, 'stdout'), (process.stderr, stderr, 'stderr'))]
                for reader in readers:
                    reader.start()
                code = process.wait()
                for reader in readers:
                    reader.join()
    except OSError as exc:
        reason = str(exc)
        print(f'Could not start batch worker: {exc}', file=sys.stderr, flush=True)
    if code:
        diagnostic = '\n'.join(text[-2000:] for text in (log_tail(stdout_path), log_tail(stderr_path)) if text)
        reason = reason or diagnostic[-4000:] or f'Worker exited with code {code}.'
    emit(dict(context, kind='finished', status='succeeded' if code == 0 else 'failed',
              exit_code=code, reason=reason, elapsed_seconds=time.monotonic() - started))
    return code if code >= 0 else 128 - code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    plan = sub.add_parser('plan')
    plan.add_argument('list_file')
    plan.add_argument('start', type=int)
    plan.add_argument('end', type=int)
    skip = sub.add_parser('skip')
    skip.add_argument('entry_id', type=int)
    skip.add_argument('tableau')
    skip.add_argument('reason')
    error = sub.add_parser('error')
    error.add_argument('reason')
    run = sub.add_parser('worker')
    run.add_argument('entry_id', type=int)
    run.add_argument('job_id')
    run.add_argument('tableau')
    run.add_argument('stdout_path')
    run.add_argument('stderr_path')
    run.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.action == 'worker':
        command = args.command[1:] if args.command[:1] == ['--'] else args.command
        return worker(args.entry_id, args.job_id, args.tableau, args.stdout_path, args.stderr_path, command)
    if args.action == 'error':
        emit(dict(kind='batch_error', reason=args.reason))
    elif args.action == 'skip':
        emit(dict(kind='skipped', status='skipped', entry_id=args.entry_id,
                  tableau=parse_shape(args.tableau, True), reason=args.reason))
    else:
        emit(dict(kind='total', total=max(0, args.end - args.start + 1)))
        entry_id = 0
        with open(args.list_file, encoding='utf-8') as stream:
            for line in stream:
                if not line.strip() or line.lstrip().startswith('#'):
                    continue
                entry_id += 1
                if args.start <= entry_id <= args.end:
                    emit(dict(kind='queued', entry_id=entry_id, status='queued',
                              tableau=parse_shape(line, True)))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
