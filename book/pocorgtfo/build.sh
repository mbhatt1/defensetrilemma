#!/usr/bin/env bash
# Build AI || PoC || GTFO, Issue 0x01: interior + KDP cover.
set -euo pipefail
cd "$(dirname "$0")"
export PATH="/Library/TeX/texbin:$HOME/Library/TinyTeX/bin/universal-darwin:$PATH"

echo "==> Regenerating interior from the book's Verso sources"
python3 convert.py

echo "==> Building interior (two passes via latexmk)"
latexmk -pdf -interaction=nonstopmode aipocorgtfo-book.tex >/dev/null

PAGES=$(pdfinfo aipocorgtfo-book.pdf | awk '/Pages/{print $2}')
echo "    interior pages: $PAGES"
python3 - "$PAGES" <<'PY'
import sys; p=int(sys.argv[1]); s=p*0.002252
print("    spine (white paper): %.4f in" % s)
print("    full cover: %.4f x 9.2500 in" % (0.25+12+s))
print("    (if this differs from cover.tex, update its constants and rebuild)")
PY

echo "==> Building cover (two passes for remember-picture)"
pdflatex -interaction=nonstopmode cover.tex >/dev/null
pdflatex -interaction=nonstopmode cover.tex >/dev/null

echo "==> Done:"
echo "    aipocorgtfo-book.pdf  (interior, upload to KDP)"
echo "    cover.pdf             (full-wrap cover, upload to KDP)"
