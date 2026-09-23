"""UI-independent validation and background execution for WBE Studio."""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from fractions import Fraction
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import uuid

from .paths import ROOT, STATE, PYTHON, RESULTS, WOLFRAM, SCRIPTS, local_path
PREDICTORS = ('Constant', 'Euler', 'Heun', 'HeunEuler', 'RK4', 'RKCashKarp45',
              'RKDormandPrince56', 'RKF45', 'RKNorsett34', 'RKVerner67')
# These values intentionally follow submit_run_single_jobs.sh and run.sh.
BATCH = dict(INITIAL_LAMBDA='500', TARGET_LAMBDA='0', WORKING_PRECISION='100',
             DEFAULT_PRECISION='100', TRACKING_TOLERANCE='1e-12', INFINITE_TOLERANCE='1e30',
             MAX_PRECISION='1200', MAX_NUM_STEPS='500000', MAX_STEP_SIZE='1/200',
             MAX_NEWTON_ITERATIONS='4', PREDICTOR='RKCashKarp45', INITIAL_STEP_SIZE='', TIMEOUT='900')
MODES = ('Single tableau', 'Batch: Young diagram', 'Batch: list file', 'Tableau + flip', 'Check saved flips',
         'Tableau + reverse continuation')


def parse_shape(text: str, tableau: bool = False) -> str:
    if not re.fullmatch(r'[\s\d{},\[\]]+', text):
        raise ValueError('Use only integers, commas and braces, for example {{1,3},{2}} or {3,2,1}.')
    try:
        value = ast.literal_eval(text.replace('{', '[').replace('}', ']'))
    except (ValueError, SyntaxError, RecursionError) as exc:
        raise ValueError('The tableau or Young diagram has invalid brackets.') from exc
    def integers(row):
        return isinstance(row, list) and bool(row) and all(type(x) is int and x > 0 for x in row)
    if tableau:
        if not isinstance(value, list) or not value or not all(integers(row) for row in value):
            raise ValueError('Enter a list of nonempty rows, for example {{1,3},{2}}.')
        lengths = list(map(len, value))
        flat = [x for row in value for x in row]
        if sorted(flat) != list(range(1, len(flat) + 1)):
            raise ValueError('A standard tableau must contain each integer from 1 to N exactly once.')
        if any(a >= b for row in value for a, b in zip(row, row[1:])):
            raise ValueError('Tableau entries must increase across each row.')
        if any(a[j] >= b[j] for a, b in zip(value, value[1:]) for j in range(min(len(a), len(b)))):
            raise ValueError('Tableau entries must increase down each column.')
    else:
        if not integers(value):
            raise ValueError('Enter positive row lengths, for example {3,2,1}.')
        lengths = value
    if lengths != sorted(lengths, reverse=True):
        raise ValueError('Row lengths must be in decreasing or equal order.')
    return str(value).replace('[', '{').replace(']', '}').replace(' ', '')


def positive_integer(value, label):
    if not re.fullmatch(r'[1-9][0-9]*', str(value).strip()):
        raise ValueError(f'{label} must be a positive integer.')
    return int(value)


def number(value, label, positive=False):
    value = value.strip()
    if not re.fullmatch(r'[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?(?:/[1-9]\d*)?', value):
        raise ValueError(f'{label}: use a number such as 500, 1e-12 or 1/200.')
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError(f'{label} is not a valid number.') from exc
    if positive and result <= 0:
        raise ValueError(f'{label} must be greater than zero.')
    return result


@dataclass
class Configuration:
    mode: str = MODES[0]
    input: str = '{{1,3},{2}}'
    output: str = str(RESULTS / 'studio')
    jobs: str = '1'
    partition: str = ''
    parts: str = '9'
    rerun: bool = False
    tolerance: str = '1e-5'
    settings: dict = field(default_factory=lambda: dict(BATCH))

    def command(self):
        if self.mode not in MODES:
            raise ValueError('Choose a calculation type.')
        if not self.output.strip():
            raise ValueError('Choose a results folder.')
        destination = local_path(self.output)
        if destination.exists() and not destination.is_dir():
            raise ValueError('The results destination must be a folder.')
        env = {}
        integer_keys = {'WORKING_PRECISION', 'DEFAULT_PRECISION', 'MAX_PRECISION',
                        'MAX_NUM_STEPS', 'MAX_NEWTON_ITERATIONS', 'TIMEOUT'}
        for key in BATCH:
            val = str(self.settings.get(key, BATCH[key])).strip()
            if key == 'INITIAL_STEP_SIZE' and not val:
                continue
            if key == 'PREDICTOR':
                if val not in PREDICTORS:
                    raise ValueError('Choose a supported predictor.')
            elif key in integer_keys:
                positive_integer(val, key.replace('_', ' ').title())
            else:
                number(val, key.replace('_', ' ').title(), key not in {'INITIAL_LAMBDA', 'TARGET_LAMBDA'})
                if key in {'TRACKING_TOLERANCE', 'INFINITE_TOLERANCE'} and '/' in val:
                    raise ValueError('Tolerances must use decimal or scientific notation.')
            env['BERTINI_' + key] = val
        if int(env['BERTINI_MAX_PRECISION']) < int(env['BERTINI_DEFAULT_PRECISION']):
            raise ValueError('Maximum precision must be at least the Bertini precision.')
        env.update(BERTINI_RESULT_SYT_DIR=str(destination), CROSSCHECK_RESULT_SYT_DIR=str(destination),
                   PYTHONUNBUFFERED='1',
                   PYTHONPATH=str(ROOT / 'src') + os.pathsep + os.environ.get('PYTHONPATH', ''))
        kernel = os.environ.get('WOLFRAM_KERNEL', 'WolframKernel')
        env['WOLFRAM_KERNEL'] = kernel
        if self.mode == MODES[0]:
            args = [kernel, '-noprompt', '-script', str(WOLFRAM / 'RunSingle.wl'), parse_shape(self.input, True)]
        elif self.mode in MODES[1:3]:
            args = ['bash', str(SCRIPTS / 'submit_run_single_jobs.sh')]
            if self.mode == MODES[1]:
                args += ['--yd', parse_shape(self.input)]
            else:
                source = local_path(self.input)
                if not source.is_file():
                    raise ValueError('Choose an existing tableau list file.')
                count = 0
                with source.open(encoding='utf-8') as stream:
                    for index, line in enumerate(stream, 1):
                        if not line.strip() or line.lstrip().startswith('#'):
                            continue
                        try:
                            parse_shape(line, True)
                        except ValueError as exc:
                            raise ValueError(f'List line {index}: {exc}') from exc
                        count += 1
                if not count:
                    raise ValueError('The tableau list is empty.')
                args += ['--list', str(source)]
            args += ['-j', str(positive_integer(self.jobs, 'Parallel jobs'))]
            if self.partition.strip():
                part = positive_integer(self.partition, 'Partition')
                total = positive_integer(self.parts, 'Number of partitions')
                if part > total:
                    raise ValueError('Partition cannot exceed the number of partitions.')
                args += ['--part', str(part), '--parts', str(total)]
            if self.rerun:
                args += ['--rerun-existing']
        else:
            number(self.tolerance, 'Comparison tolerance', True)
            if '/' in self.tolerance:
                raise ValueError('Comparison tolerance must use decimal or scientific notation.')
            if self.mode == MODES[3]:
                args = ['bash', str(SCRIPTS / 'crosscheck.sh'), '--tolerance', self.tolerance,
                        '--keep-workdir', parse_shape(self.input, True)]
            elif self.mode == MODES[5]:
                args = [str(PYTHON), '-m', 'bae_bertini.reverse_check', '--tolerance', self.tolerance,
                        parse_shape(self.input, True)]
            else:
                source = local_path(self.input)
                if not source.is_file():
                    raise ValueError('Choose an existing aggregate results CSV.')
                args = [str(PYTHON), '-m', 'bae_bertini.flip_checks', str(source),
                        '--tolerance', self.tolerance]
        return args, env


def preview(args, env):
    return '\n'.join(f'{k}={v}' for k, v in sorted(env.items())) + '\n\n' + shlex.join(args)


def load_config():
    try:
        data = json.loads((STATE / 'settings.json').read_text())
        if data.get('output'):
            data['output'] = str(local_path(data['output']))
        if data.get('mode') in (MODES[2], MODES[4]) and data.get('input'):
            data['input'] = str(local_path(data['input']))
        return Configuration(**data)
    except (OSError, ValueError, TypeError):
        return Configuration()


def save_config(config):
    from dataclasses import asdict
    STATE.mkdir(parents=True, exist_ok=True)
    temporary = STATE / ('settings-' + uuid.uuid4().hex + '.tmp')
    temporary.write_text(json.dumps(asdict(config), indent=2) + '\n')
    temporary.replace(STATE / 'settings.json')


def check_dependencies(require_wolfram=True):
    issues = []
    if require_wolfram and not shutil.which(os.environ.get('WOLFRAM_KERNEL', 'WolframKernel')):
        issues.append('WolframKernel is missing from PATH. Install or configure Mathematica.')
    try:
        result = subprocess.run(
            [str(PYTHON), str(SCRIPTS / 'continue_lambda0_to_zero.py'), '--help'],
            capture_output=True, text=True, timeout=20)
        if result.returncode:
            issues.append(
                'The project Python environment cannot load the Bertini continuation driver. '
                'This project is tested with bertini2==2.0.2. Repair it with: '
                f'{shlex.quote(str(PYTHON))} -m pip install --force-reinstall "bertini2==2.0.2"\n'
                + result.stderr[-1000:])
    except (OSError, subprocess.TimeoutExpired) as exc:
        issues.append(f'Cannot use {PYTHON}: {exc}')
    return issues
