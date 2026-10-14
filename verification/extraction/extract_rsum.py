#!/usr/bin/env python3
"""Compatibility entry point; translation is implemented in frontend.py."""
from functools import partial
from extract import ROOT, Unsupported, extract_family, main

extract = partial(extract_family, 'rsum')

if __name__ == '__main__':
    main('rsum')
