#!/usr/bin/env bash
#
# Build the thesis edition: HTML and PDF.
#
#   ./build-thesis.sh          HTML + PDF
#   ./build-thesis.sh --html   HTML only
#
# The thesis shares its theoretical chapters with the book, so the Lean in it
# is checked by the same elaboration; this script differs from build.sh only in
# which root document it renders and where the output lands.
set -euo pipefail

cd "$(dirname "$0")"

export PATH="$HOME/.elan/bin:/Library/TeX/texbin:$PATH"

echo "==> Checking theorem backing and library citations"
python3 check_citations.py

echo "==> Reproducing the empirical table from committed artifacts"
python3 Thesis/analysis/coupling_trend.py

echo "==> Elaborating thesis (Lean proofs are checked here)"
lake exe thesis

HTML="_out_thesis/html-single/index.html"
[ -f "$HTML" ] || { echo "error: expected $HTML" >&2; exit 1; }
echo "==> HTML: $HTML"

if [ "${1:-}" = "--html" ]; then
  exit 0
fi

command -v lualatex >/dev/null || {
  echo "error: lualatex not found (install MacTeX, or run with --html)" >&2
  exit 1
}

# Same generated-preamble patches as the book; see build.sh for why each is
# needed. main.tex is regenerated on every build, so patching it here is safe.
echo "==> Patching generated preamble for missing glyphs"
python3 - <<'PY'
import pathlib, sys

tex = pathlib.Path("_out_thesis/tex/main.tex")
src = tex.read_text(encoding="utf-8")

anchor = "\\begin{document}"
if anchor not in src:
    sys.exit("error: no \\begin{document} in generated main.tex")

patch = "\n".join([
    "% --- added by build-thesis.sh: glyph coverage and line breaking",
    "\\newunicodechar{∎}{\\leavevmode\\rule{0.5em}{0.5em}}",
    "\\newunicodechar{ε}{\\ensuremath{\\varepsilon}}",
    "\\newunicodechar{δ}{\\ensuremath{\\delta}}",
    "\\newunicodechar{Ε}{\\ensuremath{\\mathrm{E}}}",
    "\\newunicodechar{↔}{\\ensuremath{\\leftrightarrow}}",
    "\\directlua{luaotfload.add_fallback('versomonofallback',",
    "  {'DejaVuSans:mode=harf;', 'STIXTwoMath-Regular:mode=harf;'})}",
    "\\setmonofont{DejaVu Sans Mono}[RawFeature={fallback=versomonofallback}]",
    "\\RecustomVerbatimCommand{\\LeanVerb}{Verb}",
    "  {commandchars=\\\\\\{\\},fontsize=\\small,breaklines=true,",
    "   breakafter={_./},breakaftersymbolpre={},breakanywhere=true,",
    "   breakanywheresymbolpre={},breaksymbolleft={},breaksymbolright={}}",
    "\\emergencystretch=1em",
    "% ---",
    "",
])

if "added by build-thesis.sh" not in src:
    src = src.replace(anchor, patch + anchor, 1)
    tex.write_text(src, encoding="utf-8")
PY

echo "==> Running LaTeX (lualatex via latexmk)"
cd _out_thesis/tex
latexmk -lualatex -interaction=nonstopmode -halt-on-error main.tex >latexmk.out 2>&1 || {
  echo "error: LaTeX failed. Last errors:" >&2
  grep -n "^!" -A 5 main.log | head -40 >&2 || tail -30 latexmk.out >&2
  exit 1
}
cd ../..

if grep -q "Missing character" _out_thesis/tex/main.log; then
  echo "warning: LaTeX dropped characters with no glyph in the current font:" >&2
  grep -o "There is no .\{0,40\}" _out_thesis/tex/main.log | sort -u | head >&2
fi

cp _out_thesis/tex/main.pdf bhatt-thesis.pdf
PAGES=$(grep -o "Output written on main.pdf ([0-9]* pages" _out_thesis/tex/main.log | grep -o "[0-9]*" | head -1)
echo "==> PDF: $(pwd)/bhatt-thesis.pdf (${PAGES:-?} pages)"
