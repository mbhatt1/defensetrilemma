import subprocess, os, sys
os.chdir('/Users/mbhatt/stuff')
tex = sys.argv[1]
r = subprocess.run(['pdflatex','-interaction=nonstopmode', tex], capture_output=True, text=True, timeout=240)
print('rc:', r.returncode)
out = r.stdout
# find lines with ! (LaTeX errors)
lines = out.split('\n')
errors = []
for i, l in enumerate(lines):
    if l.startswith('!') or 'Emergency stop' in l or '! LaTeX Error' in l:
        errors.append((i, l))
print('errors:', len(errors))
for i, l in errors[:30]:
    ctx = '\n'.join(lines[max(0,i-2):i+5])
    print('---')
    print(ctx)
print('--- tail ---')
print(out[-2000:])
