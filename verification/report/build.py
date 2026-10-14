#!/usr/bin/env python3
"""Build the working report with LaTeX; keep auxiliary files out of outputs."""
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
latex = shutil.which('pdflatex')
if not latex and Path('/Library/TeX/texbin/pdflatex').exists():
    latex = '/Library/TeX/texbin/pdflatex'
if not latex: raise SystemExit('pdflatex is required to build the report')
with tempfile.TemporaryDirectory(prefix='salty-report-') as temporary:
    for _ in range(2):
        subprocess.run([latex, '-interaction=batchmode', '-halt-on-error',
                        '-output-directory=' + temporary,
                        str(ROOT / 'verification/report/report.tex')], check=True, cwd=ROOT)
    log = (Path(temporary) / 'report.log').read_text()
    if 'Overfull' in log: raise SystemExit('Report has overfull content; inspect the LaTeX layout')
    output = ROOT / 'output/pdf/report.pdf'
    output.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(Path(temporary) / 'report.pdf', output)
    print(output)
