#!/usr/bin/env bash
#
# Build both editions of the book.
#
#   ./build.sh          HTML + PDF
#   ./build.sh --html   HTML only (skips LaTeX, which is the slow half)
#
# `lake exe trilemmabook` emits the single-page HTML and a LaTeX source tree,
# but nothing runs LaTeX, so the PDF was never actually produced. This script
# closes that gap and patches the two glyph problems in the generated preamble.
set -euo pipefail

cd "$(dirname "$0")"

export PATH="$HOME/.elan/bin:/Library/TeX/texbin:$PATH"

# Verso renders an inline code span as \LeanVerb|...|, and a verbatim argument
# cannot contain a newline. A span that wraps across two source lines therefore
# builds clean HTML and then kills LaTeX several thousand lines into the run,
# pointing at the generated main.tex rather than at the chapter. Catch it here.
echo "==> Checking for inline code spans that wrap across lines"
python3 - <<'PY'
import glob, sys

bad = []
for path in sorted(glob.glob("TrilemmaBook/*.lean")):
    in_fence = False
    for n, line in enumerate(open(path, encoding="utf-8").read().split("\n"), 1):
        if line.lstrip().startswith("```"):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        if line.count("`") % 2:
            bad.append((path, n, line.strip()))

if bad:
    print("error: inline code span left open at end of line (breaks \\LeanVerb):",
          file=sys.stderr)
    for path, n, line in bad:
        print(f"  {path}:{n}: {line[:90]}", file=sys.stderr)
    print("  Fix: keep the whole `...` span on one source line.", file=sys.stderr)
    sys.exit(1)
PY

# A prose theorem citing `foo_bar` in a companion library is checked by nothing:
# rename the library declaration and the book keeps asserting it. This gate
# verifies every citation resolves, and that every prose theorem is either
# proved in-book, cited to a real declaration, or explicitly marked unformalized.
echo "==> Checking theorem backing and library citations"
python3 check_citations.py

echo "==> Elaborating book (Lean proofs are checked here)"
lake exe trilemmabook

HTML="_out/html-single/index.html"
[ -f "$HTML" ] || { echo "error: expected $HTML" >&2; exit 1; }
echo "==> HTML: $HTML"

if [ "${1:-}" = "--html" ]; then
  exit 0
fi

command -v lualatex >/dev/null || {
  echo "error: lualatex not found (install MacTeX, or run with --html)" >&2
  exit 1
}

# Verso builds the preamble from its registered extensions only; there is no
# config hook for adding to it. Since main.tex is regenerated on every build,
# patching it here is safe -- it is a generated file, not a source file.
#
# lualatex drops a glyph its font lacks and carries on with only a warning in
# the log, so these losses are silent: 62 characters were vanishing from the
# PDF, including every one of the 38 layer subscripts in `Jℓ` in Chapter 8.
#
# There are two distinct causes and they need two distinct fixes:
#
#   * Prose. Source Serif Pro's italic has no Greek, which cost us the ε and δ
#     in the emphasized definitions of Chapter 6. `newunicodechar` maps those
#     onto the math font.
#   * Code. DejaVu Sans Mono lacks ℓ, ≫ and ⊬. `newunicodechar` cannot help
#     here, because verbatim reads characters with catcodes that stop macro
#     expansion, so the fix has to be a font fallback chain instead.
echo "==> Patching generated preamble for missing glyphs"
python3 - <<'PY'
import pathlib, sys

tex = pathlib.Path("_out/tex/main.tex")
src = tex.read_text(encoding="utf-8")

anchor = "\\begin{document}"
if anchor not in src:
    sys.exit("error: no \\begin{document} in generated main.tex")

patch = "\n".join([
    "% --- added by build.sh: glyph coverage fixes",
    "",
    "% Prose: glyphs absent from the Source Serif Pro text font, mapped onto",
    "% the math font. The tombstone is drawn with \\rule rather than",
    "% \\blacksquare because Verso's generated preamble does not load amssymb",
    "% and we do not control it.",
    "\\newunicodechar{∎}{\\leavevmode\\rule{0.5em}{0.5em}}",
    "\\newunicodechar{ε}{\\ensuremath{\\varepsilon}}",
    "\\newunicodechar{δ}{\\ensuremath{\\delta}}",
    "\\newunicodechar{Ε}{\\ensuremath{\\mathrm{E}}}",
    "",
    "% Code: give the monospace font a fallback chain, since newunicodechar",
    "% does not fire inside verbatim. Verso sets DejaVu Sans Mono above; this",
    "% re-declares it with fallbacks for the characters it lacks.",
    "\\directlua{luaotfload.add_fallback('versomonofallback',",
    "  {'DejaVuSans:mode=harf;', 'STIXTwoMath-Regular:mode=harf;'})}",
    "\\setmonofont{DejaVu Sans Mono}[RawFeature={fallback=versomonofallback}]",
    "% ---",
    "",
])

if "added by build.sh" not in src:
    src = src.replace(anchor, patch + anchor, 1)
    tex.write_text(src, encoding="utf-8")
PY

echo "==> Running LaTeX (lualatex via latexmk)"
cd _out/tex
latexmk -lualatex -interaction=nonstopmode -halt-on-error main.tex >latexmk.out 2>&1 || {
  echo "error: LaTeX failed. Last errors:" >&2
  grep -n "^!" -A 5 main.log | head -40 >&2 || tail -30 latexmk.out >&2
  exit 1
}
cd ../..

# Fail loudly on dropped glyphs. lualatex treats these as warnings, which is
# how the missing tombstones went unnoticed in the first place.
if grep -q "Missing character" _out/tex/main.log; then
  echo "warning: LaTeX dropped characters with no glyph in the current font:" >&2
  grep -o "There is no .\{0,40\}" _out/tex/main.log | sort -u | head >&2
fi

cp _out/tex/main.pdf trilemma-book.pdf
PAGES=$(grep -o "Output written on main.pdf ([0-9]* pages" _out/tex/main.log | grep -o "[0-9]*" | head -1)
echo "==> PDF: $(pwd)/trilemma-book.pdf (${PAGES:-?} pages)"
