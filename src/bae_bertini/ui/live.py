"""A bounded terminal view for the current Studio calculation."""
import streamlit as st


def show_log(state):
    st.subheader('Calculation terminal')
    output = '\n'.join(entry.formatted() for entry in state.entries)[-160000:]
    st.code(output or 'Starting calculation…', language='text', height=600, wrap_lines=False)
