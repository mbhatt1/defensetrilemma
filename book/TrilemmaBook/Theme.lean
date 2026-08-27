/-
Visual theme for the book.

Verso's default HTML is functional but generic: Helvetica everywhere, all-black
text, `monospace` for code, and a 47rem measure. This module overrides its CSS
variable layer and adds the layout rules that make the output read as a book.

The stylesheet is injected inline into every page's `<head>` (see `themeHead`)
rather than written as a separate file, so that the output stays correct when
opened directly from disk over `file://`, where root-relative asset paths do not
resolve.
-/

import Verso.Output.Html

namespace TrilemmaBook.Theme

open Verso.Output

/--
The book's stylesheet. Emitted verbatim (unescaped) into a `<style>` element.
-/
def css : String := r#"
/* ============================================================
   Palette and type
   ============================================================ */
:root {
  /* Book measure: 40rem at 18px is roughly 66 characters, the classic
     target for a serif text face. Verso's default 47rem at 16px is too
     wide to track comfortably. */
  --verso-content-max-width: 40rem;
  --verso-font-size: 18px;
  --verso-mobile-font-size: 17px;

  --verso-text-font-family: "Iowan Old Style", "Charter", "Palatino Linotype",
                            Palatino, Georgia, "Times New Roman", serif;
  --verso-structure-font-family: "Iowan Old Style", "Charter", Palatino,
                                 Georgia, serif;
  --verso-code-font-family: "SF Mono", "JetBrains Mono", "IBM Plex Mono",
                            Menlo, Consolas, monospace;

  /* Warm paper, warm ink: pure #fff/#000 is what makes the default look
     like a rendered document rather than a printed one. */
  --paper: #fbfaf7;
  --paper-sunk: #f3f1ea;
  --ink: #22201c;
  --ink-muted: #6b665c;
  --rule: #ddd8cc;
  --accent: #3a4a86;
  --accent-quiet: #7c86ad;

  --verso-text-color: var(--ink);
  --verso-structure-color: var(--ink);
  --verso-code-color: var(--ink);
  --verso-selected-color: #e6e9f5;
  --verso-toc-background-color: var(--paper-sunk);
  --verso-toc-width: 19rem;

  /* Syntax. Verso hands us these directly; the default is all-black, which
     wastes the one place in the book where color carries information. */
  --verso-code-keyword-color: #7a2f6d;
  --verso-code-keyword-weight: 600;
  --verso-code-const-color: #1f5d5a;
  --verso-code-var-color: #35507e;
  --verso-code-var-style: italic;
}

@media (prefers-color-scheme: dark) {
  :root {
    --paper: #17171a;
    --paper-sunk: #1e1e22;
    --ink: #e4e1d9;
    --ink-muted: #97928a;
    --rule: #34343a;
    --accent: #9db0ec;
    --accent-quiet: #6a75a0;
    --verso-selected-color: #2a2f45;

    --verso-code-keyword-color: #d59ac9;
    --verso-code-const-color: #7fc9c2;
    --verso-code-var-color: #a8bdea;
  }
}

html, body { background: var(--paper); color: var(--ink); }

body {
  -webkit-font-smoothing: antialiased;
  text-rendering: optimizeLegibility;
  font-variant-numeric: oldstyle-num proportional-nums;
}

::selection { background: var(--verso-selected-color); }

/* ============================================================
   Text
   ============================================================ */
p, dd, li {
  line-height: 1.62;
  hyphens: auto;
}

main p { margin: 0 0 1.15em; }

/* Opening paragraph of a section gets no indent; the rest of a run of
   paragraphs is separated by space, not indentation — mixing the two is the
   most common way a web book ends up looking wrong. */
main > section > p:first-of-type { margin-top: 0.4em; }

em { font-style: italic; }
strong { font-weight: 650; }

a, a:visited { color: var(--accent); text-decoration-thickness: 1px;
               text-underline-offset: 2px; }
a:hover { text-decoration-thickness: 2px; }

/* ============================================================
   Headings
   ============================================================ */
main h1, main h2, main h3, main h4, main h5, main h6 {
  font-weight: 600;
  letter-spacing: -0.011em;
  line-height: 1.22;
  color: var(--ink);
}

main h1 {
  font-size: 2.1rem;
  margin: 0 0 1.6rem;
  padding-bottom: 0.5rem;
  border-bottom: 1px solid var(--rule);
}

/* On a single page, `h2` is a chapter opening, not a subsection. Give it a
   rule and real space above so the reader can feel the break while scrolling. */
main h2 {
  font-size: 1.75rem;
  margin: 4.5rem 0 1.2rem;
  padding-top: 1.5rem;
  border-top: 1px solid var(--rule);
}

main h3 {
  font-size: 1.14rem;
  margin: 2.2rem 0 0.5rem;
}

/* The generated per-chapter numbering ("2.1.") reads better slightly quieter
   than the title it prefixes. */
main h2 .section-num, main h3 .section-num { color: var(--ink-muted); }

main h4 { font-size: 1rem; font-style: italic; font-weight: 600; }

/* Title page */
main .titlepage h1 {
  font-size: 2.6rem;
  line-height: 1.15;
  border-bottom: none;
  margin-bottom: 0.8rem;
  text-wrap: balance;
}

main .authors {
  font-family: var(--verso-structure-font-family);
  font-style: italic;
  color: var(--ink-muted);
  font-size: 1.05rem;
  margin-bottom: 2.5rem;
}

/* ============================================================
   Code
   ============================================================ */
code, pre { font-variant-numeric: normal; }

/* Inline code: tinted, not boxed-and-bordered. */
p code, li code, dd code, dt code, h1 code, h2 code, h3 code, h4 code {
  font-size: 0.855em;
  background: var(--paper-sunk);
  padding: 0.12em 0.32em;
  border-radius: 3px;
}

/* Elaborated Lean blocks. The left rule marks them as machine-checked
   artifacts rather than quoted listings. */
pre, .hl.lean.block {
  font-size: 0.855rem;
  line-height: 1.55;
  background: var(--paper-sunk);
  border: 1px solid var(--rule);
  border-left: 3px solid var(--accent-quiet);
  border-radius: 3px;
  padding: 0.85rem 1rem;
  margin: 1.35rem 0;
  overflow-x: auto;
}

/* Don't double-decorate inline code that lives inside a block. */
pre code, .hl.lean.block code { background: none; padding: 0; font-size: 1em; }

.hl.lean.inline { font-size: 0.855em; }

/* Hover tooltips (types, docstrings) — Verso's best feature, so make the
   affordance visible. */
.hl.lean .token:hover { background: var(--verso-selected-color); border-radius: 2px; }

/* ============================================================
   Description lists (the `: term` blocks)
   ============================================================ */
main dl { margin: 1.4rem 0; }

main dt {
  font-family: var(--verso-structure-font-family);
  font-weight: 600;
  font-size: 0.94rem;
  letter-spacing: 0.02em;
  color: var(--accent);
  margin-top: 1.1rem;
}

main dd {
  margin: 0.3rem 0 0 0;
  padding-left: 1rem;
  border-left: 2px solid var(--rule);
}

/* ============================================================
   Table of contents
   ============================================================ */
#toc {
  border-right: 1px solid var(--rule);
  font-family: var(--verso-structure-font-family);
}

#toc, #toc a, #toc a:visited { color: var(--ink); }
#toc a { text-decoration: none; }
#toc a:hover { text-decoration: underline; text-underline-offset: 2px; }

#toc .split-toc.book .title { font-weight: 600; }

#toc .split-toc {
  font-size: 0.9rem;
  line-height: 1.4;
  padding: 0.15rem 0;
}

#toc .split-toc .current td:not(.num),
#toc .split-toc .title.current {
  font-weight: 600;
  color: var(--accent);
}

#toc .split-toc td.num { color: var(--ink-muted); font-variant-numeric: tabular-nums; }

.toc-title h1 { font-size: 1rem; letter-spacing: 0.02em; }

/* In-page section list */
main .section-toc { font-family: var(--verso-structure-font-family); font-size: 0.94rem; }
main .section-toc a, main .section-toc a:visited { text-decoration: none; color: var(--accent); }
main .section-toc a:hover { text-decoration: underline; }

/* ============================================================
   Header and page furniture
   ============================================================ */
header {
  border-bottom: 1px solid var(--rule);
  background: var(--paper);
}

.header-title, .header-title h1 {
  font-family: var(--verso-structure-font-family);
  font-size: 0.95rem;
  font-weight: 600;
  letter-spacing: 0.01em;
}

.prev-next-buttons {
  margin-top: 3.5rem;
  padding-top: 1.2rem;
  border-top: 1px solid var(--rule);
  font-family: var(--verso-structure-font-family);
  font-size: 0.9rem;
}

.prev-next-buttons .where { color: var(--accent); text-decoration: none; }
.prev-next-buttons .local-button .where:hover { text-decoration: underline; }

/* Permalink anchors: present, but they shouldn't shout. */
.permalink-widget > a { color: var(--accent-quiet); text-decoration: none; }
.permalink-widget > a:hover { color: var(--accent); }

/* Give the text column room to breathe under the header. */
.content-wrapper { padding-top: 2.2rem; padding-bottom: 2rem; }
"#

/--
The `<style>` element carrying `css`, for `RenderConfig.extraHead`.

`Html.text false` emits the string raw: escaping it would turn CSS combinators
such as `>` into `&gt;` and silently break every rule that uses one.
-/
def head : Html := .tag "style" #[] (.text false css)

end TrilemmaBook.Theme
