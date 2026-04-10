# Defense Trilemma — Overleaf Upload Package

Two versions of the paper plus the figure they reference, ready to
upload to Overleaf as a single project.

## Contents

```
overleaf_package/
├── paper2_v2.tex            ← arXiv-style version (article + neurips_2025 layout)
├── paper2_neurips.tex       ← NeurIPS preprint version
├── neurips_2025.sty         ← NeurIPS 2025 style file (loaded by both)
├── figures/
│   └── theory_vs_reality_saturated.pdf  ← Figure 4: theory vs reality side-by-side
└── README.md
```

## How to use on Overleaf

1. Upload this entire directory (or the zip) to a new Overleaf project.
2. In the project menu, set the **Main document** to either
   `paper2_v2.tex` (19-page version) or `paper2_neurips.tex` (16-page
   version) depending on which one you want to compile.
3. Set the TeX Live version to 2023 or later.
4. Recompile.

Both `.tex` files are self-contained — bibliography is inline `\bibitem`
entries, no external `.bib`. The only asset they pull in is
`figures/theory_vs_reality_saturated.pdf`, which is included.

## Repository

Full source, validator, and live archives:
https://github.com/mbhatt1/defensetrilemma
