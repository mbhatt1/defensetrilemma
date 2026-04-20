import subprocess, os, sys
os.chdir('/Users/mbhatt/stuff')
for tex in ['paper2_v2.tex', 'paper2_neurips.tex']:
    for run in range(2):
        r = subprocess.run(['pdflatex','-interaction=nonstopmode', tex], capture_output=True, text=True, timeout=240)
        # check for real errors only (startswith !)
        errs = [l for l in r.stdout.split('\n') if l.startswith('!')]
        print(f'{tex} pass {run+1} rc={r.returncode} errors={len(errs)}')
        for e in errs[:5]:
            print('  ', e)
# Count pages
import pypdf
for tex in ['paper2_v2.tex', 'paper2_neurips.tex']:
    pdf = tex.replace('.tex', '.pdf')
    p = pypdf.PdfReader(pdf)
    print(f'{pdf}: {len(p.pages)} pages')
