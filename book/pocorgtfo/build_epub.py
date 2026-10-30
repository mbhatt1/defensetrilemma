#!/usr/bin/env python3
"""Build a clean, reflowable Kindle EPUB for "Pick Two" from the Verso html-single build."""
import re, sys, os
from bs4 import BeautifulSoup

SRC = os.path.join(os.path.dirname(__file__), '..', '_out', 'html-single', 'index.html')
OUT = os.path.join(os.path.dirname(__file__), 'picktwo-body.html')

soup = BeautifulSoup(open(SRC, encoding='utf-8').read(), 'lxml')
main = soup.find('main')
assert main, "no <main> found"

# 1. drop chrome + scripts/styles inside main
for sel in ('nav', 'header', 'script', 'style'):
    for el in main.find_all(sel):
        el.decompose()

# 2. drop interactive / decorative widgets
for css in ('.permalink-widget', '.tactic-state', '.tactic-toggle',
            '.section-toc', '.split-toc', '.nav', '.find'):
    for el in main.select(css):
        el.decompose()

# 3. remove the manual "Table of Contents" section (pandoc builds its own nav)
for h in main.find_all(['h2']):
    if h.get_text(strip=True).rstrip('🔗').strip().lower() == 'table of contents':
        sec = h.find_parent('section') or h.parent
        sec.decompose()
        break

# 4. flatten Lean code blocks -> real <pre><code>
for code in main.find_all('code'):
    classes = code.get('class') or []
    if 'block' in classes:
        text = code.get_text()
        text = re.sub(r'\n{3,}', '\n\n', text.strip('\n'))
        pre = soup.new_tag('pre'); c = soup.new_tag('code')
        c.string = text; pre.append(c)
        pre['class'] = ['lean']
        code.replace_with(pre)
    elif 'inline' in classes:
        new = soup.new_tag('code'); new.string = code.get_text()
        code.replace_with(new)

# 5. strip anchor-link glyphs left in headings
for h in main.find_all(['h1', 'h2', 'h3', 'h4']):
    for a in h.find_all('a'):
        if a.get_text(strip=True) in ('🔗', '§', ''):
            a.decompose()
    # clean trailing link glyph in text
    if h.string:
        h.string = h.get_text().replace('🔗', '').strip()

# 6. drop the redundant top title h1 (EPUB title page is generated from metadata),
#    then promote headings so chapters are h1 (clean per-chapter split).
t = main.find('h1')
if t:
    t.decompose()
for name_from, name_to in (('h2','h1'), ('h3','h2'), ('h4','h3')):
    for el in main.find_all(name_from):
        el.name = name_to

# 7. debloat: remove class/style/data-* from all tags (keep 'lean' on pre)
for tag in main.find_all(True):
    keep = {}
    if tag.name == 'pre' and tag.get('class') == ['lean']:
        keep['class'] = ['lean']
    tag.attrs = keep

# 7b. unwrap <section> and <div> wrappers so headings sit at top level (pandoc splits on them)
for sec in main.find_all('section'):
    sec.unwrap()
# remove a stray leading author byline span (title page comes from metadata)
first = main.find(['span'])
if first and first.get_text(strip=True) == 'Manish Bhatt':
    first.decompose()
for d in main.find_all('div'):
    d.unwrap()

# write cleaned body (inner HTML of main)
inner = ''.join(str(c) for c in main.contents)
with open(OUT, 'w', encoding='utf-8') as f:
    f.write('<!DOCTYPE html>\n<html><head><meta charset="utf-8"><title>Pick Two</title></head><body>\n')
    f.write(inner)
    f.write('\n</body></html>\n')

# quick stats
pre_n = inner.count('<pre')
h2_n = inner.count('<h2')
print(f'wrote {OUT}: {len(inner)} bytes, {h2_n} h2 (chapters), {pre_n} code blocks')
