#!/usr/bin/env python3
"""Generate Figure-1-style classifier-gate maps as standalone PDFs.

This renderer avoids NumPy / Matplotlib entirely. It rebuilds the archive grid
from JSON, writes a tiny TikZ document for each gate, and compiles it with
pdflatex.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
from pathlib import Path


ROOT = Path("/Users/mbhatt/stuff")
ARCHIVE = ROOT / "trilemma_validator/live_runs/gpt35_turbo_t05_saturated/source_archive.json"
LLAMAGUARD = ROOT / "trilemma_validator/live_runs/llamaguard_thm83/records.json"
SHIELDGEMMA = ROOT / "trilemma_validator/live_runs/shieldgemma_thm83/records.json"
FIGURES = ROOT / "figures"

EMPTY = "empty"
SAFE = "safe"
UNSAFE = "unsafe"

CELL = 0.30
GRID = 25
PANEL_GAP = 5
TOP_Y = 30.5
X_LABEL_Y = -2.2
X_TICK_Y = -1.15
LEGEND_Y = -4.85


def _read_json(path: Path):
    with path.open("r") as f:
        return json.load(f)


def _escape_tex(text: str) -> str:
    repl = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    out = text
    for k, v in repl.items():
        out = out.replace(k, v)
    return out


def _load_archive(path: Path) -> tuple[int, dict[tuple[int, int], float]]:
    data = _read_json(path)
    cells = {
        tuple(cell["grid_position"]): float(cell["quality"])
        for cell in data["cells"]
    }
    return int(data["grid_size"]), cells


def _load_gate(path: Path) -> tuple[list[dict], set[str]]:
    records = _read_json(path)
    labels = {str(rec["label"]) for rec in records}
    return records, labels


def _find_boundary_cells(cells: dict[tuple[int, int], float], tau: float) -> list[tuple[int, int]]:
    boundary = []
    neigh = [(-1, 0), (1, 0), (0, -1), (0, 1)]
    for (i, j), q in cells.items():
        if q < tau:
            continue
        for di, dj in neigh:
            nb = (i + di, j + dj)
            if nb in cells and cells[nb] < tau:
                boundary.append((i, j))
                break
    return sorted(boundary)


def _build_original_grid(cells: dict[tuple[int, int], float], tau: float) -> dict[tuple[int, int], str]:
    return {
        pos: (UNSAFE if q >= tau else SAFE)
        for pos, q in cells.items()
    }


def _build_gate_grid(records: list[dict]) -> dict[tuple[int, int], str]:
    return {
        tuple(rec["grid_position"]): (UNSAFE if rec["verdict"] == "unsafe" else SAFE)
        for rec in records
    }


def _compute_stats(
    cells: dict[tuple[int, int], float], records: list[dict], tau: float
) -> dict[str, int]:
    tp = tn = fp = fn = 0
    for rec in records:
        pos = tuple(rec["grid_position"])
        archive_unsafe = cells[pos] >= tau
        gate_unsafe = rec["verdict"] == "unsafe"
        if archive_unsafe and gate_unsafe:
            tp += 1
        elif archive_unsafe and not gate_unsafe:
            fn += 1
        elif (not archive_unsafe) and gate_unsafe:
            fp += 1
        else:
            tn += 1
    return {"tp": tp, "fn": fn, "fp": fp, "tn": tn}


def _color_for(kind: str) -> str:
    if kind == SAFE:
        return "safegreen"
    if kind == UNSAFE:
        return "unsafered"
    return "emptyfill"


def _panel_tex(
    *,
    x0: int,
    title_line1: str,
    title_line2: str,
    grid: dict[tuple[int, int], str],
    boundary_cells: list[tuple[int, int]],
    grid_size: int,
) -> str:
    lines = [
        rf"\node[font=\normalsize\bfseries, align=center] at ({x0 + (grid_size - 1) / 2}, {grid_size + 2.8}) {{{title_line1}}};",
        rf"\node[font=\footnotesize, align=center] at ({x0 + (grid_size - 1) / 2}, {grid_size + 1.2}) {{{title_line2}}};",
    ]

    for i in range(grid_size):
        for j in range(grid_size):
            color = _color_for(grid.get((i, j), EMPTY))
            lines.append(
                rf"\fill[{color}] ({x0 + i - 0.5}, {j - 0.5}) rectangle ({x0 + i + 0.5}, {j + 0.5});"
            )

    for (i, j) in boundary_cells:
        lines.append(
            rf"\draw[boundaryline, line width=0.45pt] ({x0 + i - 0.5}, {j - 0.5}) rectangle ({x0 + i + 0.5}, {j + 0.5});"
        )

    lines.extend(
        [
            rf"\draw[black, line width=0.3pt] ({x0 - 0.5}, {-0.5}) rectangle ({x0 + grid_size - 0.5}, {grid_size - 0.5});",
            rf"\node[font=\footnotesize] at ({x0 + (grid_size - 1) / 2}, {X_LABEL_Y}) {{indirection}};",
            rf"\node[font=\footnotesize, rotate=90] at ({x0 - 3.4}, {(grid_size - 1) / 2}) {{authority}};",
        ]
    )
    for tick in [0, grid_size // 2, grid_size - 1]:
        lines.append(rf"\node[font=\scriptsize] at ({x0 + tick}, {X_TICK_Y}) {{{tick}}};")
        lines.append(rf"\node[font=\scriptsize] at ({x0 - 1.7}, {tick}) {{{tick}}};")
    return "\n".join(lines)


def _document_tex(
    *,
    model_title: str,
    records: list[dict],
    cells: dict[tuple[int, int], float],
    tau: float,
    out_pdf_name: str,
    grid_size: int,
) -> str:
    labels = sorted({str(rec["label"]) for rec in records})
    boundary_cells = _find_boundary_cells(cells, tau)
    original_grid = _build_original_grid(cells, tau)
    gate_grid = _build_gate_grid(records)
    stats = _compute_stats(cells, records, tau)

    n_filled = len(cells)
    n_archive_unsafe = sum(q >= tau for q in cells.values())
    n_gate_unsafe = sum(rec["verdict"] == "unsafe" for rec in records)

    panel1 = _panel_tex(
        x0=0,
        title_line1="Original archive",
        title_line2=rf"$f(x)\geq\tau$ unsafe cells: $n={n_archive_unsafe}$",
        grid=original_grid,
        boundary_cells=boundary_cells,
        grid_size=grid_size,
    )
    panel2 = _panel_tex(
        x0=grid_size + PANEL_GAP,
        title_line1=f"{_escape_tex(model_title)} verdicts",
        title_line2=rf"$D(x)=\mathrm{{unsafe}}$: $n={n_gate_unsafe}$",
        grid=gate_grid,
        boundary_cells=boundary_cells,
        grid_size=grid_size,
    )

    title = (
        rf"{_escape_tex(model_title)} on the saturated archive ($n={n_filled}$ cells, $\tau={tau}$)"
        "\n"
        rf"TP={stats['tp']} $\bullet$ FN={stats['fn']} $\bullet$ FP={stats['fp']} $\bullet$ TN={stats['tn']} $\bullet$ labels={len(labels)}"
    )

    return rf"""
\documentclass[10pt]{{article}}
\usepackage[paperwidth=8.0in,paperheight=5.25in,margin=0.08in]{{geometry}}
\usepackage{{tikz}}
\pagestyle{{empty}}
\definecolor{{emptyfill}}{{HTML}}{{F7FAFC}}
\definecolor{{safegreen}}{{HTML}}{{BFE7CC}}
\definecolor{{unsafered}}{{HTML}}{{F2AAA2}}
\definecolor{{boundaryline}}{{HTML}}{{1A202C}}
\begin{{document}}
\centering
\begin{{tikzpicture}}[x={CELL}cm, y={CELL}cm]
\node[font=\normalsize\bfseries, align=center] at ({(grid_size + PANEL_GAP + grid_size - 1) / 2}, {TOP_Y}) {{{title}}};
{panel1}
{panel2}
\node[draw, rounded corners=1pt, fill=white, fill opacity=0.96, text opacity=1,
      align=left, inner sep=4pt, anchor=center] at ({(2 * grid_size + PANEL_GAP - 1) / 2}, {LEGEND_Y}) {{
  \begin{{tikzpicture}}[x=1em,y=1em,baseline]
    \fill[unsafered] (0,0) rectangle +(1,1); \draw[black, line width=0.25pt] (0,0) rectangle +(1,1);
    \node[anchor=west,font=\scriptsize] at (1.4,0.5) {{unsafe}};
    \fill[safegreen] (0,-1.8) rectangle +(1,1); \draw[black, line width=0.25pt] (0,-1.8) rectangle +(1,1);
    \node[anchor=west,font=\scriptsize] at (1.4,-1.3) {{safe / passed}};
    \fill[emptyfill] (0,-3.6) rectangle +(1,1); \draw[black, line width=0.25pt] (0,-3.6) rectangle +(1,1);
    \node[anchor=west,font=\scriptsize] at (1.4,-3.1) {{not sampled}};
    \fill[white] (0,-5.4) rectangle +(1,1); \draw[boundaryline, line width=0.45pt] (0,-5.4) rectangle +(1,1);
    \node[anchor=west,font=\scriptsize] at (1.4,-4.9) {{boundary ($n={len(boundary_cells)}$)}};
  \end{{tikzpicture}}
}};
\end{{tikzpicture}}
\end{{document}}
"""


def _compile_tex(tex_path: Path) -> None:
    cmd = [
        "/usr/local/bin/pdflatex",
        "-interaction=nonstopmode",
        "-halt-on-error",
        f"-output-directory={tex_path.parent}",
        str(tex_path),
    ]
    subprocess.run(cmd, check=True, capture_output=True, text=True)


def _keep_last_pdf_page(pdf_path: Path) -> None:
    stem = pdf_path.with_suffix("")
    pattern = stem.parent / f"{stem.name}-page-%d.pdf"
    subprocess.run(
        ["/usr/local/bin/pdfseparate", str(pdf_path), str(pattern)],
        check=True,
        capture_output=True,
        text=True,
    )
    pages = sorted(stem.parent.glob(f"{stem.name}-page-*.pdf"))
    if not pages:
        raise RuntimeError(f"pdfseparate produced no pages for {pdf_path}")
    shutil.move(str(pages[-1]), str(pdf_path))
    for page in pages[:-1]:
        page.unlink()


def render_gate_map(
    *,
    archive_path: Path,
    records_path: Path,
    out_path: Path,
    model_title: str,
    tau: float,
) -> None:
    grid_size, cells = _load_archive(archive_path)
    records, _labels = _load_gate(records_path)

    tex_body = _document_tex(
        model_title=model_title,
        records=records,
        cells=cells,
        tau=tau,
        out_pdf_name=out_path.name,
        grid_size=grid_size,
    )

    tex_path = out_path.with_suffix(".tex")
    tex_path.write_text(tex_body)
    _compile_tex(tex_path)
    _keep_last_pdf_page(out_path)

    for suffix in [".aux", ".log", ".tex"]:
        sidecar = out_path.with_suffix(suffix)
        if sidecar.exists():
            sidecar.unlink()
    print(f"Wrote {out_path}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tau", type=float, default=0.5)
    parser.add_argument("--archive", type=Path, default=ARCHIVE)
    args = parser.parse_args()

    FIGURES.mkdir(parents=True, exist_ok=True)
    render_gate_map(
        archive_path=args.archive,
        records_path=LLAMAGUARD,
        out_path=FIGURES / "llamaguard_gate_map.pdf",
        model_title="Llama-Guard-3-1B",
        tau=args.tau,
    )
    render_gate_map(
        archive_path=args.archive,
        records_path=SHIELDGEMMA,
        out_path=FIGURES / "shieldgemma_gate_map.pdf",
        model_title="ShieldGemma-2B",
        tau=args.tau,
    )


if __name__ == "__main__":
    main()
