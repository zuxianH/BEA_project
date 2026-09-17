"""Run with: .venv/bin/python -m streamlit run streamlit_app.py"""
from __future__ import annotations

import atexit
import csv
import hashlib

import streamlit as st

from bae_bertini import config as configuration
from bae_bertini.config import BATCH, MODES, PREDICTORS, Configuration, preview
from bae_bertini.paths import ROOT, STATE, REFERENCES
from bae_bertini.results import read_results
from bae_bertini.ui.plots import root_figure
from bae_bertini.jobs import RunManager, local_path


@st.cache_resource
def run_manager():
    manager = RunManager()
    atexit.register(manager.close)
    return manager


def initialize():
    if 'draft_config' not in st.session_state:
        st.session_state['draft_config'] = configuration.load_config()
    config = st.session_state['draft_config']
    for key in ('mode', 'output', 'jobs', 'partition', 'parts', 'rerun', 'tolerance'):
        # Reassign to detach temporarily hidden values from widget cleanup.
        st.session_state[key] = st.session_state.get(key, getattr(config, key))
    inputs = st.session_state.setdefault('draft_inputs', {})
    for mode in MODES:
        key = 'input_' + mode
        st.session_state[key] = st.session_state.get(key, inputs.get(mode, (
            config.input if mode == config.mode else
            '{3,2,1}' if mode == MODES[1] else
            '' if mode in (MODES[2], MODES[4]) else '{{1,3},{2}}'
        )))
    for key, value in BATCH.items():
        st.session_state.setdefault('setting_' + key, config.settings.get(key, value))
    st.session_state.setdefault('browse_folder', config.output)


def uploaded_path(upload):
    data = upload.getvalue()
    folder = STATE / 'uploads'
    folder.mkdir(parents=True, exist_ok=True)
    suffix = '.csv' if upload.name.lower().endswith('.csv') else '.txt'
    path = folder / (hashlib.sha256(data).hexdigest() + suffix)
    if not path.exists():
        path.write_bytes(data)
    return str(path)


def calculation_form():
    with st.sidebar:
        st.title('Calculation')
        mode = st.selectbox('Calculation type', MODES, key='mode')
        label = ('Young diagram' if mode == MODES[1] else 'Input file on this computer'
                 if mode in (MODES[2], MODES[4]) else 'Standard Young tableau')
        value = st.text_input(label, key='input_' + mode)
        if mode in (MODES[2], MODES[4]):
            upload = st.file_uploader('Or upload an input file',
                                      type=['csv'] if mode == MODES[4] else ['txt'],
                                      key='upload_' + mode)
            if upload is not None:
                value = uploaded_path(upload)
            elif value.strip():
                value = str(local_path(value))
        else:
            st.caption('Row lengths: {3,2,1}' if mode == MODES[1] else 'Rows: {{1,3},{2}}')
        if mode in MODES[1:3]:
            st.text_input('Parallel jobs', key='jobs', help='Each job needs an available Wolfram kernel and memory.')
            left, right = st.columns(2)
            left.text_input('Partition (optional)', key='partition')
            right.text_input('Total partitions', key='parts')
            st.checkbox('Rerun existing tableaux', key='rerun')
        if mode in MODES[3:]:
            st.text_input('Flip comparison tolerance', key='tolerance')
        st.divider()
        st.subheader('Numerical settings')
        left, right = st.columns(2)
        left.text_input('Starting λ', key='setting_INITIAL_LAMBDA')
        right.text_input('Target λ', key='setting_TARGET_LAMBDA')
        st.text_input('Working precision (digits)', key='setting_WORKING_PRECISION')
        st.text_input('Tracking tolerance', key='setting_TRACKING_TOLERANCE')
        with st.expander('Advanced settings'):
            for key, title in (
                ('DEFAULT_PRECISION', 'Bertini precision (digits)'),
                ('MAX_PRECISION', 'Maximum precision (digits)'),
                ('INFINITE_TOLERANCE', 'Infinite endpoint tolerance'),
                ('MAX_NUM_STEPS', 'Maximum tracking steps'),
                ('INITIAL_STEP_SIZE', 'Initial step size (blank = automatic)'),
                ('MAX_STEP_SIZE', 'Maximum step size'),
                ('MAX_NEWTON_ITERATIONS', 'Maximum Newton iterations'),
                ('TIMEOUT', 'Backend timeout (seconds)'),
            ):
                st.text_input(title, key='setting_' + key)
            st.selectbox('Predictor', PREDICTORS, key='setting_PREDICTOR')
        st.text_input('Results folder', key='output')
        config = Configuration(
            mode=mode, input=value.strip(),
            **{key: st.session_state[key] for key in
               ('output', 'jobs', 'partition', 'parts', 'rerun', 'tolerance')},
            settings={key: st.session_state['setting_' + key].strip() for key in BATCH},
        )
        # Streamlit removes hidden widgets; keep drafts independent of widget keys.
        st.session_state['draft_config'] = config
        st.session_state['draft_inputs'][mode] = st.session_state['input_' + mode]
        run = st.button('Run calculation', type='primary', width='stretch',
                        disabled=run_manager().snapshot().running)
        if run:
            try:
                args, env = config.command()
                with st.spinner('Checking calculation environment…'):
                    # Saved flip checks parse CSVs and do not need either solver.
                    issues = configuration.check_dependencies() if mode != MODES[4] else []
                if issues:
                    st.error('\n\n'.join(issues))
                else:
                    configuration.save_config(config)
                    run_manager().start(args, env)
                    st.session_state['browse_folder'] = config.output
                    st.rerun()
            except (ValueError, OSError) as exc:
                st.error(str(exc))
        if st.button('Save settings', width='stretch'):
            try:
                config.command()
                configuration.save_config(config)
                st.success('Settings saved.')
            except (ValueError, OSError) as exc:
                st.error(str(exc))
        st.caption('Runs continue if you close the browser. Reopen this server to see progress or stop a run.')
    return config


def live_run():
    manager = run_manager()
    state = manager.snapshot()
    if st.session_state.get('was_running', state.running) != state.running:
        st.session_state['was_running'] = state.running
        st.rerun()
    st.session_state['was_running'] = state.running
    if not state.running and st.button('Refresh run status'):
        st.rerun()
    if state.log_path is None:
        st.info('Ready. Set up a calculation in the sidebar, or explore saved results.')
        return
    left, right = st.columns([4, 1])
    elapsed = int(state.elapsed)
    if state.running:
        left.info(f'{"Stopping…" if state.cancelled else "Running"} · {elapsed // 60:02d}:{elapsed % 60:02d} elapsed')
    elif state.cancelled:
        left.warning('Stopped. Completed outputs and pending batch snapshots are retained.')
    elif state.code == 0:
        left.success(f'Finished successfully · {elapsed // 60:02d}:{elapsed % 60:02d}')
    else:
        left.error(f'Finished with exit code {state.code}. Check the log below.')
    if right.button('Stop calculation', disabled=not state.running or state.cancelled):
        manager.stop()
        st.rerun()
    st.caption(f'Results: {state.destination}')
    st.code(state.output or 'Starting calculation…', language='text', height=330)
    st.caption(f'Live view shows the recent log. Full log: {state.log_path}')
    if not state.running and state.log_path.exists():
        if st.checkbox('Prepare full log download', key='prepare_log_' + str(state.log_path)):
            st.download_button('Download full log', prepared_download(state.log_path, 'log'),
                               file_name=state.log_path.name, mime='text/plain', on_click='ignore')


def prepared_download(path, kind):
    """Keep only the selected download of each kind; reread only if it changes."""
    info = path.stat()
    identity = (str(path), info.st_mtime_ns, info.st_size)
    key = 'prepared_download_' + kind
    cached = st.session_state.get(key)
    if cached is None or cached[0] != identity:
        cached = (identity, path.read_bytes())
        st.session_state[key] = cached
    return cached[1]


@st.cache_data(max_entries=8, show_spinner=False)
def result_rows(path, modified, size):
    # File metadata invalidates previews after the solver atomically replaces a CSV.
    return read_results(path)


def choose_row(paths, prefix):
    path = st.selectbox('Result CSV' if prefix == 'a' else 'Comparison CSV', paths,
                        format_func=lambda p: p.name, key=prefix + '_file')
    info = path.stat()
    rows, truncated = result_rows(str(path), info.st_mtime_ns, info.st_size)
    if not rows:
        st.info('This CSV has no result rows.')
        return path, None, rows
    st.caption(f'{len(rows)} rows loaded' + (' · preview limited to the first 500 rows' if truncated else ''))
    index = st.selectbox(
        'Tableau' if prefix == 'a' else 'Comparison tableau', range(len(rows)),
        format_func=lambda i: f'{i + 1}. {rows[i].get("Tableau", "(no tableau)")} · {rows[i].get("SucceededQ", "unknown")}',
        key=prefix + '_row_' + str(path),
    )
    return path, rows[index], rows


def results_browser():
    st.subheader('Explore Bethe roots')
    st.text_input('Browse results folder', key='browse_folder')
    left, middle, right = st.columns(3)
    if left.button('Use calculation folder'):
        st.session_state['next_browse_folder'] = st.session_state['output']
        st.rerun()
    if middle.button('Open reference results'):
        st.session_state['next_browse_folder'] = str(REFERENCES)
        st.rerun()
    right.button('Refresh results')
    try:
        folder = local_path(st.session_state['browse_folder'])
        paths = sorted(folder.glob('*.csv'), key=lambda p: p.stat().st_mtime_ns, reverse=True)
        if not paths:
            st.info('No CSV files here yet. Choose an existing results folder or run a calculation.')
            return
        path, row, rows = choose_row(paths, 'a')
        if row is None:
            return
        a, b, c = st.columns(3)
        a.metric('Result files', len(paths))
        b.metric('Rows in preview', len(rows))
        c.metric('Selected result', 'Succeeded' if row.get('SucceededQ', '').lower() == 'true' else 'Not successful')
        comparison = None
        negate = False
        if st.checkbox('Compare with another result'):
            _, comparison_row, _ = choose_row(paths, 'b')
            comparison = comparison_row.get('BetheRoots', '') if comparison_row else None
            negate = st.checkbox('Negate A for a sign-flip comparison (−A vs B)', value=True)
        try:
            figure, omitted = root_figure(row.get('BetheRoots', ''), comparison, negate,
                                          revision=str(path) + str(row.get('Tableau', '')))
            if figure.data:
                st.plotly_chart(figure, width='stretch',
                                config={'scrollZoom': True, 'displaylogo': False,
                                        'toImageButtonOptions': {'format': 'svg', 'filename': 'bethe-roots'}})
                st.caption('Scroll to zoom, drag to pan, and click legend entries to hide levels. Plot coordinates use floating-point display values.')
            else:
                st.info('No finite Bethe roots available for this selection.')
            if omitted:
                st.warning(f'{omitted} non-finite roots omitted from the plot.')
        except (ValueError, TypeError, OverflowError) as exc:
            st.warning(f'Root plot unavailable: {exc}')
        with st.expander('Full precision row', expanded=True):
            st.code('\n\n'.join(f'{key}\n{value}' for key, value in row.items()), language='text')
        with st.expander('CSV preview'):
            st.dataframe(rows, width='stretch')
        # Avoid reading very large aggregate CSVs just to display the page.
        if st.checkbox('Prepare full CSV download', key='download_' + str(path)):
            st.download_button('Download CSV', prepared_download(path, 'csv'),
                               file_name=path.name, mime='text/csv', on_click='ignore')
    except (OSError, ValueError, csv.Error, UnicodeError) as exc:
        st.error(f'Cannot read results: {exc}')


def main():
    st.set_page_config(page_title='Bertini Calculation Studio', page_icon='🧮', layout='wide')
    initialize()
    if 'next_browse_folder' in st.session_state:
        st.session_state['browse_folder'] = st.session_state.pop('next_browse_folder')
    st.title('Bertini Calculation Studio')
    st.caption('Bethe continuation · calculations, progress, and interactive root exploration')
    config = calculation_form()
    live, results, details = st.tabs(['Live calculation', 'Results & roots', 'Run details'])
    with live:
        st.fragment(live_run, run_every=1 if run_manager().snapshot().running else None)()
    with results:
        results_browser()
    with details:
        st.subheader('Command preview')
        try:
            args, env = config.command()
            st.code(preview(args, env), language='bash')
        except (ValueError, OSError) as exc:
            st.info(str(exc))


if __name__ == '__main__':
    main()
