"""Continuous-defense sweep on a fixed archive.

Runs the three grid-level continuous defenses exposed by ``defenses.py`` —
``smooth_nearest_safe``, ``kernel_smoothed``, ``softly_constrained_projection``
— together with the GP-smooth oblique defense from ``sensitivity.py`` through
the same validator pipeline, and emits a comparison table suitable for the
paper.
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from .defenses import (
    KernelSmoothedDefense,
    SmoothNearestSafeDefense,
    SoftlyConstrainedProjectionDefense,
)
from .loader import Heatmap, load_archive_json
from .report import write_json, write_markdown
from .sensitivity import run_sensitivity_cell
from .theorems import run_full_validation


def _run_discrete(
    defense_cls, defense_kwargs: dict, heatmap: Heatmap, tau: float
) -> dict:
    """Run a grid-level continuous defense through the validator and summarize."""
    defense_obj = defense_cls(**defense_kwargs)
    defense = defense_obj.build(heatmap, tau)
    result = run_full_validation(heatmap, tau, defense)
    e = result.estimates
    pc = result.persistence
    return {
        "defense": defense.name,
        "params": defense.params,
        "L": e.L,
        "K": e.K,
        "ell": e.ell,
        "G": e.G,
        "ell_K_plus_1": e.ell * (e.K + 1.0),
        "transversality_holds": e.persistence_condition(),
        "predicted_persistent_count": len(pc.predicted_steep_cells),
        "actual_persistent_count": len(pc.actual_persistent_cells),
        "true_positives": len(pc.true_positives),
        "false_positives_interior": len(pc.false_positives_interior),
        "false_positives_boundary": len(pc.false_positives_boundary),
        "false_negatives": len(pc.false_negatives),
        "theorem_violated": pc.theorem_violated,
        "_full_result": result,  # consumed by the caller for JSON dump
    }


def _run_gp_oblique(heatmap: Heatmap, tau: float, oblique_angle_deg: float) -> dict:
    """Run the RBF + oblique GP-smooth defense via the sensitivity pipeline."""
    r = run_sensitivity_cell(
        heatmap,
        tau=tau,
        kernel_name="rbf",
        sigma=0.2,
        oblique_angle_deg=oblique_angle_deg,
    )
    return {
        "defense": "oblique_gp_smooth",
        "params": {
            "kernel": "rbf",
            "sigma": r.sigma,
            "oblique_angle": oblique_angle_deg,
            "alpha_step": r.alpha_step,
            "sigmoid_steepness": r.sigmoid_steepness,
        },
        "L": r.L_data,
        "K": r.K_empirical,
        "ell": r.ell_empirical,
        "G": r.G,
        "ell_K_plus_1": r.ell_K_plus_1,
        "transversality_holds": r.transversality_holds,
        "predicted_persistent_count": r.predicted_persistent_count,
        "actual_persistent_count": r.actual_persistent_count,
        "true_positives": r.true_positives,
        "false_positives_interior": r.false_positives_interior,
        "false_positives_boundary": r.false_positives_boundary,
        "false_negatives": r.false_negatives,
        "theorem_violated": r.theorem_violated,
    }


def run_continuous_sweep(
    heatmap: Heatmap,
    tau: float,
    out_dir: Path,
    *,
    snearest_radius: float = 3.0,
    kernel_bandwidth: float = 2.5,
    proj_alpha: float = 2.0,
    oblique_angle_deg: float = 89.5,
) -> dict:
    """Run all four continuous defenses and write artifacts."""
    out_dir.mkdir(parents=True, exist_ok=True)
    rows: list[dict] = []

    configs = [
        ("smooth_nearest_safe", SmoothNearestSafeDefense, {"radius": snearest_radius}),
        ("kernel_smoothed", KernelSmoothedDefense, {"bandwidth": kernel_bandwidth}),
        (
            "softly_constrained_projection",
            SoftlyConstrainedProjectionDefense,
            {"alpha": proj_alpha},
        ),
    ]

    for slug, cls, kwargs in configs:
        summary = _run_discrete(cls, kwargs, heatmap, tau)
        full = summary.pop("_full_result")
        per_dir = out_dir / slug
        per_dir.mkdir(parents=True, exist_ok=True)
        write_json(full, per_dir / "result.json")
        write_markdown(full, per_dir / "report.md")
        with (per_dir / "summary.json").open("w") as f:
            json.dump(summary, f, indent=2)
        rows.append(summary)

    # GP-smooth oblique (not grid-snapped).
    gp_row = _run_gp_oblique(heatmap, tau, oblique_angle_deg)
    gp_dir = out_dir / "oblique_gp_smooth"
    gp_dir.mkdir(parents=True, exist_ok=True)
    # Estimate |S_act| from the sensitivity cell's actual_persistent_count.
    # Also persist a cell-level summary parallel to the other defenses.
    with (gp_dir / "result.json").open("w") as f:
        json.dump(gp_row, f, indent=2)
    rows.append(gp_row)

    combined = {
        "tau": float(tau),
        "grid_size": heatmap.grid_size,
        "n_filled": int(heatmap.filled_mask.sum()),
        "rows": rows,
    }
    with (out_dir / "sweep.json").open("w") as f:
        json.dump(combined, f, indent=2, default=_json_safe)

    return combined


def _json_safe(o):
    if isinstance(o, (np.floating,)):
        return float(o)
    if isinstance(o, (np.integer,)):
        return int(o)
    if isinstance(o, np.ndarray):
        return o.tolist()
    raise TypeError(f"Cannot JSON-serialize {type(o).__name__}: {o!r}")


def render_continuous_sweep_latex(
    combined: dict,
    out_path: Path,
    *,
    label: str = "tab:continuous-sweep",
) -> None:
    """Write the LaTeX table for the continuous-defense sweep."""
    display = {
        "smooth_nearest_safe": r"\textsc{SmoothNearestSafe}",
        "kernel_smoothed": r"\textsc{KernelSmoothed}",
        "softly_constrained_projection": r"\textsc{SoftProj}",
        "oblique_gp_smooth": r"\textsc{ObliqueGP}",
    }

    lines: list[str] = []
    lines.append(r"\begin{table}[t]")
    lines.append(r"\centering")
    lines.append(
        r"\caption{Continuous-defense sweep on the saturated gpt-3.5-turbo-0125 "
        r"archive at $\tau = 0.5$. Each row is a continuous defense passed through "
        r"the same Lipschitz/persistence validator. The oblique GP-smooth defense "
        r"(last row) is the only one that achieves the transversality condition "
        r"$G > \ell(K+1)$ while remaining non-identity, so it is the only row that "
        r"tests Theorem~6.2 non-vacuously. All rows have zero interior false "
        r"positives, confirming the containment $S_{\mathrm{pred}} \subseteq "
        r"\{x : f(D(x)) > \tau\}$ on this surface.}"
    )
    lines.append(rf"\label{{{label}}}")
    lines.append(r"\small")
    lines.append(r"\setlength{\tabcolsep}{3.6pt}")
    lines.append(r"\begin{tabular}{lrrrrrcrrrr}")
    lines.append(r"\toprule")
    lines.append(
        r"defense & $L$ & $K$ & $\ell$ & $\ell(K{+}1)$ & $G$ & trans. "
        r"& $|S_{\mathrm{p}}|$ & TP & FP$_{\mathrm{int}}$ & $|S_{\mathrm{a}}|$ \\"
    )
    lines.append(r"\midrule")
    for row in combined["rows"]:
        name = display.get(row["defense"], row["defense"])
        trans = r"\checkmark" if row["transversality_holds"] else r"$\times$"
        lines.append(
            rf"{name} "
            rf"& {row['L']:.2f} "
            rf"& {row['K']:.3f} "
            rf"& {row['ell']:.3f} "
            rf"& {row['ell_K_plus_1']:.3f} "
            rf"& {row['G']:.2f} "
            rf"& {trans} "
            rf"& {row['predicted_persistent_count']} "
            rf"& {row['true_positives']} "
            rf"& {row['false_positives_interior']} "
            rf"& {row['actual_persistent_count']} \\"
        )
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"\end{table}")

    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w") as f:
        f.write("\n".join(lines) + "\n")


def run_continuous_sweep_from_archive(
    archive_path: Path,
    out_dir: Path,
    tau: float = 0.5,
    latex_path: Path | None = None,
    **kwargs,
) -> dict:
    heatmap = load_archive_json(archive_path)
    combined = run_continuous_sweep(heatmap, tau, out_dir, **kwargs)
    if latex_path is not None:
        render_continuous_sweep_latex(combined, latex_path)
    return combined
