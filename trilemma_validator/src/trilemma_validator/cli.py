"""Single-entry CLI for the Defense Trilemma validator.

Subcommands:

* ``trilemma validate``  — validate a heatmap that already exists on disk.
* ``trilemma synth``     — generate a synthetic heatmap (mesa/mosaic/flat) and validate it.
* ``trilemma experiment``— run rethinking-evals to produce a heatmap (no validation).
* ``trilemma pipeline``  — run rethinking-evals AND validate the result in one shot.

Each command writes the same output bundle to ``--output``::

    <output>/
        heatmap.npy           # raw heatmap (always written)
        result.json           # full validation result, machine-readable
        report.md             # human-readable report
        validation.png        # 6-panel matplotlib figure

The CLI never writes outside ``--output``. Pass ``--output`` explicitly if you
want to keep multiple runs.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Optional

import numpy as np

from . import loader, report, synth, theorems, viz
from .csweep import run_continuous_sweep_from_archive
from .defenses import get_defense
from .runner import ExperimentConfig, run_experiment
from .sensitivity import run_sensitivity_from_archive


_DEFENSE_CHOICES = (
    "identity",
    "nearest_safe",
    "bounded_step",
    "smooth_nearest_safe",
    "kernel_smoothed",
    "softly_constrained_projection",
)


def _shared_validate_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--tau",
        type=float,
        default=0.5,
        help="Safety threshold τ. Default: 0.5.",
    )
    parser.add_argument(
        "--defense",
        choices=_DEFENSE_CHOICES,
        default="bounded_step",
        help=(
            "Which defense to simulate on the heatmap. "
            "'bounded_step' is the most informative on real grids "
            "(use --max-step to control its Lipschitz behavior). "
            "The continuous defenses (smooth_nearest_safe, kernel_smoothed, "
            "softly_constrained_projection) are Lipschitz by construction "
            "and satisfy Theorem 6.2's hypotheses. "
            "Default: bounded_step."
        ),
    )
    parser.add_argument(
        "--max-step",
        type=int,
        default=2,
        help="Max displacement (in grid cells) for the bounded_step defense. Default: 2.",
    )
    parser.add_argument(
        "--radius",
        type=float,
        default=3.0,
        help="Gaussian radius (in grid cells) for smooth_nearest_safe. Default: 3.0.",
    )
    parser.add_argument(
        "--bandwidth",
        type=float,
        default=2.5,
        help="Kernel bandwidth for kernel_smoothed. Default: 2.5.",
    )
    parser.add_argument(
        "--alpha-softmin",
        type=float,
        default=2.0,
        help="Softmin temperature for softly_constrained_projection. Default: 2.0.",
    )
    parser.add_argument(
        "--bootstrap",
        type=int,
        default=0,
        help=(
            "If > 0, compute bootstrap CIs on L, K, ℓ, G with this many "
            "resamples. Adds ci_L/ci_K/ci_ell/ci_G fields to result.json. "
            "Default: 0 (disabled)."
        ),
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("./trilemma_out"),
        help="Output directory. Default: ./trilemma_out",
    )


def _build_defense_from_args(args, heatmap, tau: float):
    """Factory for the shared CLI flags."""
    defense_obj = get_defense(
        args.defense,
        max_step=getattr(args, "max_step", None),
        radius=getattr(args, "radius", None),
        bandwidth=getattr(args, "bandwidth", None),
        alpha=getattr(args, "alpha_softmin", None),
    )
    return defense_obj.build(heatmap, tau)


def _do_validate(heatmap, args, *, source_label: str) -> int:
    """Shared validation pipeline used by validate / synth / pipeline."""
    defense = _build_defense_from_args(args, heatmap, args.tau)
    result = theorems.run_full_validation(heatmap, args.tau, defense)

    out: Path = args.output
    out.mkdir(parents=True, exist_ok=True)

    np.save(out / "heatmap.npy", heatmap.values)
    report.write_json(result, out / "result.json")
    report.write_markdown(result, out / "report.md")
    viz.render(heatmap, defense, args.tau, result, out / "validation.png")

    # Bootstrap CIs (optional).
    if getattr(args, "bootstrap", 0) and args.bootstrap > 0:
        from . import uncertainty as _uncertainty
        import json as _json
        cis = _uncertainty.bootstrap_estimator_cis(
            heatmap, defense, args.tau, B=int(args.bootstrap)
        )
        # Enrich result.json with CIs.
        with (out / "result.json").open() as f:
            payload = _json.load(f)
        payload["bootstrap"] = {
            "B": cis["B"],
            "alpha": cis["alpha"],
            "ci_L": {"population_size": cis["L"]["population_size"],
                     "median": cis["L"]["ci"][0],
                     "lo": cis["L"]["ci"][1],
                     "hi": cis["L"]["ci"][2]},
            "ci_K": {"population_size": cis["K"]["population_size"],
                     "median": cis["K"]["ci"][0],
                     "lo": cis["K"]["ci"][1],
                     "hi": cis["K"]["ci"][2]},
            "ci_ell": {"population_size": cis["ell"]["population_size"],
                       "median": cis["ell"]["ci"][0],
                       "lo": cis["ell"]["ci"][1],
                       "hi": cis["ell"]["ci"][2]},
            "ci_G": {"population_size": cis["G"]["population_size"],
                     "median": cis["G"]["ci"][0],
                     "lo": cis["G"]["ci"][1],
                     "hi": cis["G"]["ci"][2]},
        }
        with (out / "result.json").open("w") as f:
            _json.dump(payload, f, indent=2)
        print(
            f"  bootstrap ({args.bootstrap} resamples): "
            f"L {payload['bootstrap']['ci_L']['lo']:.3f}–{payload['bootstrap']['ci_L']['hi']:.3f}, "
            f"K {payload['bootstrap']['ci_K']['lo']:.3f}–{payload['bootstrap']['ci_K']['hi']:.3f}, "
            f"ell {payload['bootstrap']['ci_ell']['lo']:.3f}–{payload['bootstrap']['ci_ell']['hi']:.3f}, "
            f"G {payload['bootstrap']['ci_G']['lo']:.3f}–{payload['bootstrap']['ci_G']['hi']:.3f}"
        )

    print()
    print("=" * 60)
    print(f"Trilemma validation complete  ·  source: {source_label}")
    print("=" * 60)
    print(f"  τ = {args.tau}, defense = {defense.name} ({defense.params})")
    print(
        f"  filled = {int(heatmap.filled_mask.sum())}/{heatmap.grid_size ** 2}"
        f"  ({100 * heatmap.coverage:.1f}% coverage)"
    )
    print(
        f"  safe (f<τ) = {result.safe_count},  "
        f"unsafe (f>τ) = {result.unsafe_count},  "
        f"at-τ = {result.at_threshold_count}"
    )
    e = result.estimates
    print(f"  L = {e.L:.4f}   K = {e.K:.4f}   ℓ = {e.ell:.4f}   G = {e.G:.4f}")
    if not result.applicable:
        print("  → trilemma not applicable on this surface (S or U is empty)")
        for note in result.notes:
            print(f"      {note}")
    else:
        bd = result.boundary
        er = result.eps_robust
        pc = result.persistence

        t41 = "ACTIVATED" if bd.boundary_exists else "vacuous (no boundary cells)"
        print(
            f"  Theorem 4.1 boundary fixation:        {t41}  "
            f"({len(bd.boundary_cells)} boundary cells; "
            f"{len(bd.fixed_boundary_cells)} fixed by {result.defense_name})"
        )
        if bd.boundary_exists:
            print(
                f"      predicted f(z) = {bd.predicted_f_at_boundary:.4f},  "
                f"empirical f(z*) = {bd.empirical_f_at_closest:.4f},  "
                f"discretization gap = {bd.discretization_gap:.4f}"
            )

        print(
            f"  Theorem 5.1 ε-robust constraint:      "
            f"{'CONFIRMED' if er.holds else 'VIOLATIONS'}  "
            f"({er.num_within_bound}/{er.num_total} cells within bound)"
        )
        if er.num_total > 0:
            print(
                f"      max predicted RHS = {er.max_predicted_rhs:.4f},  "
                f"max empirical LHS = {er.max_observed_lhs:.4f}"
            )

        print(
            f"  Theorem 6.2 transversality G > ℓ(K+1):"
            f" {'YES' if pc.transversality_holds else 'no'}"
            f"  ({e.G:.3f} vs {e.ell * (e.K + 1):.3f})"
        )
        print(
            f"      predicted steep set: {len(pc.predicted_steep_cells)} cells,  "
            f"actual persistent set: {len(pc.actual_persistent_cells)} cells"
        )
        print(
            f"      true pos = {len(pc.true_positives)},  "
            f"false pos interior = {len(pc.false_positives_interior)} "
            f"(real counterexamples),  "
            f"false pos boundary = {len(pc.false_positives_boundary)} "
            f"(non-continuous defense at boundary),  "
            f"false neg = {len(pc.false_negatives)}"
        )

        print()
        if result.all_predictions_confirmed:
            print("  ✅ ALL THEOREM PREDICTIONS CONFIRMED EMPIRICALLY")
        elif pc.theorem_violated:
            print("  ❌ THEOREM 6.2 VIOLATED — see false-positive list in result.json")
        else:
            print("  ⚠ Predictions partially confirmed; see report.md for details")
    print()
    print(f"  outputs written to: {out}")
    print(f"    - {out / 'heatmap.npy'}")
    print(f"    - {out / 'result.json'}")
    print(f"    - {out / 'report.md'}")
    print(f"    - {out / 'validation.png'}")
    return 0


def cmd_validate(args: argparse.Namespace) -> int:
    if not args.heatmap and not args.archive:
        print(
            "error: pass either --heatmap PATH (.npy) or --archive PATH "
            "(rethinking-evals final_archive.json)",
            file=sys.stderr,
        )
        return 2
    if args.heatmap and args.archive:
        print("error: pass exactly one of --heatmap or --archive", file=sys.stderr)
        return 2
    src = args.heatmap or args.archive
    heatmap = loader.load(src)
    return _do_validate(heatmap, args, source_label=str(src))


def cmd_synth(args: argparse.Namespace) -> int:
    heatmap = synth.make(args.shape, grid_size=args.grid, seed=args.seed)
    return _do_validate(heatmap, args, source_label=f"synthetic:{args.shape}")


def _maybe_pending_judge_stub(args: argparse.Namespace) -> bool:
    """If no API key, write ``judge_robustness_pending.md`` and return True.

    Called by ``cmd_experiment`` / ``cmd_pipeline`` before they invoke
    rethinking-evals. The stub captures the intended command so the paper
    agent has a pointer to the pending multi-judge run without false
    starts.
    """
    import os
    if os.environ.get("OPENAI_API_KEY"):
        return False
    out: Path = args.output
    out.mkdir(parents=True, exist_ok=True)
    stub = out / "judge_robustness_pending.md"
    judge = getattr(args, "judge", None) or "gpt-4.1-2025-04-14"
    target = getattr(args, "model", "gpt5_mini")
    lines = [
        "# Judge robustness — PENDING",
        "",
        "No `OPENAI_API_KEY` was present in the environment at the time of this "
        "run, so the live judge call could not be made. Re-run with:",
        "",
        "```bash",
        "export OPENAI_API_KEY=...",
        f"trilemma pipeline --rethinking-path /path/to/rethinking-evals "
        f"--model {target} --judge {judge} "
        f"--output {out}",
        "```",
        "",
        "The `--judge` flag is passed through to the scoring LLM call "
        "(environment variable `RETHINKING_JUDGE_MODEL`); swap it to any "
        "OpenAI chat model to re-score the archive under a different judge.",
        "",
        "Once re-run, this file should be **deleted** and replaced by the "
        "live `result.json`.",
    ]
    stub.write_text("\n".join(lines) + "\n")
    print(
        f"[trilemma] OPENAI_API_KEY not set; wrote stub at {stub}",
        file=sys.stderr,
    )
    return True


def _apply_judge_env(args: argparse.Namespace) -> None:
    """Propagate --judge into the environment for rethinking-evals to pick up."""
    import os
    j = getattr(args, "judge", None)
    if j:
        os.environ["RETHINKING_JUDGE_MODEL"] = str(j)


def cmd_experiment(args: argparse.Namespace) -> int:
    if _maybe_pending_judge_stub(args):
        return 0
    _apply_judge_env(args)
    cfg = ExperimentConfig(
        rethinking_path=args.rethinking_path,
        model=args.model,
        iterations=args.iterations,
        seed_prompts=args.seed_prompts,
        output_dir=args.output / "rethinking_run",
        judge_model=getattr(args, "judge", None) or "gpt-4.1-2025-04-14",
    )
    archive_path = run_experiment(cfg)
    print()
    print(f"experiment complete. archive at: {archive_path}")
    if getattr(args, "judge", None):
        print(f"  judge: {args.judge}")
    return 0


def cmd_pipeline(args: argparse.Namespace) -> int:
    if _maybe_pending_judge_stub(args):
        return 0
    _apply_judge_env(args)
    cfg = ExperimentConfig(
        rethinking_path=args.rethinking_path,
        model=args.model,
        iterations=args.iterations,
        seed_prompts=args.seed_prompts,
        output_dir=args.output / "rethinking_run",
        judge_model=getattr(args, "judge", None) or "gpt-4.1-2025-04-14",
    )
    archive_path = run_experiment(cfg)
    heatmap = loader.load(archive_path)
    return _do_validate(heatmap, args, source_label=str(archive_path))


def cmd_sweep(args: argparse.Namespace) -> int:
    """Run all defenses on a single archive and produce a comparison table.

    This is the natural saturation-study output: with a dense grid we want
    to see how the trilemma's predictions change as we vary the defense's
    Lipschitz reach.
    """
    if not args.heatmap and not args.archive:
        print(
            "error: pass --heatmap PATH or --archive PATH",
            file=sys.stderr,
        )
        return 2
    src = args.heatmap or args.archive
    heatmap = loader.load(src)

    out: Path = args.output
    out.mkdir(parents=True, exist_ok=True)
    np.save(out / "heatmap.npy", heatmap.values)

    # Build the sweep specs. The user can pass --defense <name,name,...> to
    # select specific defenses; otherwise we fall back to the legacy sweep
    # over identity + bounded_step(max_step_i).
    explicit_defenses: list[str] = []
    if getattr(args, "defense", None):
        raw = args.defense
        if isinstance(raw, str):
            explicit_defenses = [x.strip() for x in raw.split(",") if x.strip()]
        else:
            explicit_defenses = list(raw)

    sweep_specs: list[tuple[str, dict]] = []
    if explicit_defenses:
        for name in explicit_defenses:
            if name == "bounded_step":
                for ms in args.max_steps:
                    sweep_specs.append(("bounded_step", {"max_step": int(ms)}))
            elif name == "smooth_nearest_safe":
                sweep_specs.append(("smooth_nearest_safe", {"radius": args.radius}))
            elif name == "kernel_smoothed":
                sweep_specs.append(("kernel_smoothed", {"bandwidth": args.bandwidth}))
            elif name == "softly_constrained_projection":
                sweep_specs.append(
                    ("softly_constrained_projection", {"alpha": args.alpha_softmin})
                )
            elif name == "oblique_gp_smooth":
                sweep_specs.append(("oblique_gp_smooth", {}))
            else:
                sweep_specs.append((name, {}))
    else:
        sweep_specs = [("identity", {})]
        for ms in args.max_steps:
            sweep_specs.append(("bounded_step", {"max_step": int(ms)}))

    rows: list[dict] = []
    for defense_name, params in sweep_specs:
        if defense_name == "oblique_gp_smooth":
            # Use the script's implementation; record a summary row only.
            rows.append(_sweep_gp_smooth_oblique(heatmap, args.tau, out))
            continue
        defense_obj = get_defense(
            defense_name,
            max_step=params.get("max_step"),
            radius=params.get("radius"),
            bandwidth=params.get("bandwidth"),
            alpha=params.get("alpha"),
        )
        defense = defense_obj.build(heatmap, args.tau)
        result = theorems.run_full_validation(heatmap, args.tau, defense)
        e = result.estimates
        pc = result.persistence
        rows.append(
            {
                "defense": defense_name,
                "params": params,
                "L": e.L,
                "K": e.K,
                "ell": e.ell,
                "G": e.G,
                "K_star": e.K_star,
                "transversality": e.persistence_condition(),
                "predicted_steep": len(pc.predicted_steep_cells),
                "actual_persistent": len(pc.actual_persistent_cells),
                "true_positives": len(pc.true_positives),
                "fp_interior": len(pc.false_positives_interior),
                "fp_boundary": len(pc.false_positives_boundary),
                "false_negatives": len(pc.false_negatives),
                "theorem_violated": pc.theorem_violated,
            }
        )
        # Also write each defense's full result for inspection.
        if not params:
            slug = defense_name
        elif "max_step" in params:
            slug = f"{defense_name}_max{params['max_step']}"
        elif "radius" in params:
            slug = f"{defense_name}_r{params['radius']:g}"
        elif "bandwidth" in params:
            slug = f"{defense_name}_h{params['bandwidth']:g}"
        elif "alpha" in params:
            slug = f"{defense_name}_a{params['alpha']:g}"
        else:
            slug = defense_name
        per_def_dir = out / "per_defense" / slug
        per_def_dir.mkdir(parents=True, exist_ok=True)
        report.write_json(result, per_def_dir / "result.json")
        report.write_markdown(result, per_def_dir / "report.md")
        viz.render(heatmap, defense, args.tau, result, per_def_dir / "validation.png")

    # Sweep summary table
    import json as _json

    with (out / "sweep.json").open("w") as f:
        _json.dump(
            {
                "tau": args.tau,
                "grid_size": heatmap.grid_size,
                "filled_cells": int(heatmap.filled_mask.sum()),
                "coverage": heatmap.coverage,
                "rows": rows,
            },
            f,
            indent=2,
            default=lambda o: float("inf") if o == float("inf") else o,
        )

    # Print headline table
    print()
    print("=" * 96)
    print(
        f"Defense sweep  ·  τ = {args.tau}  ·  "
        f"{int(heatmap.filled_mask.sum())}/{heatmap.grid_size**2} cells "
        f"({100 * heatmap.coverage:.1f}% coverage)"
    )
    print("=" * 96)
    header = (
        f"{'defense':<22} {'K':>6} {'ell':>7} {'G':>7} {'transv?':>8} "
        f"{'|S_pred|':>9} {'|S_act|':>8} {'TP':>4} {'FPint':>6} "
        f"{'FPbdy':>6} {'FN':>5} {'verdict':>14}"
    )
    print(header)
    print("-" * 96)
    for r in rows:
        p = r.get("params") or {}
        if "max_step" in p:
            name = f"bnd_step({p['max_step']})"
        elif "radius" in p:
            name = f"sms_safe(r={p['radius']:g})"
        elif "bandwidth" in p:
            name = f"kern_sm(h={p['bandwidth']:g})"
        elif "alpha" in p:
            name = f"soft_proj(a={p['alpha']:g})"
        else:
            name = r["defense"]
        if r["theorem_violated"]:
            verdict = "VIOLATED"
        elif r["predicted_steep"] == 0:
            verdict = "vacuous"
        elif r["fp_interior"] == 0:
            verdict = "CONFIRMED"
        else:
            verdict = "?"
        print(
            f"{name:<22} {r['K']:>6.2f} {r['ell']:>7.3f} {r['G']:>7.3f} "
            f"{('YES' if r['transversality'] else 'no'):>8} "
            f"{r['predicted_steep']:>9} {r['actual_persistent']:>8} "
            f"{r['true_positives']:>4} {r['fp_interior']:>6} "
            f"{r['fp_boundary']:>6} {r['false_negatives']:>5} "
            f"{verdict:>14}"
        )
    print()
    print(f"Outputs: {out}/sweep.json, {out}/per_defense/")
    return 0


def cmd_sensitivity(args: argparse.Namespace) -> int:
    """GP kernel × length-scale sensitivity sweep for the oblique defense."""
    out: Path = args.out
    out.mkdir(parents=True, exist_ok=True)
    latex_path: Optional[Path] = args.latex if args.latex is not None else None

    combined = run_sensitivity_from_archive(
        archive_path=args.archive,
        out_dir=out,
        tau=args.tau,
        latex_path=latex_path,
        kernel_names=tuple(args.kernels),
        sigmas=tuple(args.sigmas),
        noise=args.noise,
        alpha_step=args.alpha_step,
        sigmoid_steepness=args.sigmoid_steepness,
        oblique_angle_deg=args.oblique_angle,
    )

    print()
    print("=" * 80)
    print(
        f"GP kernel sensitivity sweep  ·  τ = {args.tau}  ·  "
        f"{combined['n_filled']} cells  ·  {len(combined['rows'])} configs"
    )
    print("=" * 80)
    hdr = (
        f"{'kernel':<10} {'σ':>6} {'L':>6} {'K':>6} {'ℓ':>6} {'G':>6} "
        f"{'|S_pred|':>9} {'TP':>4} {'FP_int':>7} {'transv':>8}"
    )
    print(hdr)
    print("-" * 80)
    for r in combined["rows"]:
        if "error" in r:
            print(
                f"{r['kernel_name']:<10} {r['sigma']:>6.2f}  FAILED: {r['error'][:50]}"
            )
            continue
        trans = "YES" if r["transversality_holds"] else "no"
        print(
            f"{r['kernel_name']:<10} {r['sigma']:>6.2f} "
            f"{r['L_data']:>6.2f} {r['K_empirical']:>6.3f} "
            f"{r['ell_empirical']:>6.3f} {r['G']:>6.2f} "
            f"{r['predicted_persistent_count']:>9} "
            f"{r['true_positives']:>4} "
            f"{r['false_positives_interior']:>7} "
            f"{trans:>8}"
        )
    print()
    print(f"Outputs: {out}/sensitivity.json + per-cell result.json")
    if latex_path is not None:
        print(f"LaTeX table: {latex_path}")
    return 0


def cmd_csweep(args: argparse.Namespace) -> int:
    """Run the four continuous defenses and emit a comparison table."""
    out: Path = args.out
    out.mkdir(parents=True, exist_ok=True)
    latex_path: Optional[Path] = args.latex if args.latex is not None else None

    combined = run_continuous_sweep_from_archive(
        archive_path=args.archive,
        out_dir=out,
        tau=args.tau,
        latex_path=latex_path,
        snearest_radius=args.radius,
        kernel_bandwidth=args.bandwidth,
        proj_alpha=args.alpha,
        oblique_angle_deg=args.oblique_angle,
    )

    print()
    print("=" * 96)
    print(
        f"Continuous-defense sweep  ·  τ = {args.tau}  ·  "
        f"{combined['n_filled']} cells"
    )
    print("=" * 96)
    hdr = (
        f"{'defense':<32} {'L':>6} {'K':>6} {'ℓ':>6} {'ℓ(K+1)':>7} {'G':>6} "
        f"{'trans':>6} {'|Sp|':>5} {'TP':>4} {'FPint':>6} {'|Sa|':>5}"
    )
    print(hdr)
    print("-" * 96)
    for r in combined["rows"]:
        trans = "YES" if r["transversality_holds"] else "no"
        print(
            f"{r['defense']:<32} "
            f"{r['L']:>6.2f} {r['K']:>6.3f} {r['ell']:>6.3f} "
            f"{r['ell_K_plus_1']:>7.3f} {r['G']:>6.2f} "
            f"{trans:>6} "
            f"{r['predicted_persistent_count']:>5} "
            f"{r['true_positives']:>4} "
            f"{r['false_positives_interior']:>6} "
            f"{r['actual_persistent_count']:>5}"
        )
    print()
    print(f"Outputs: {out}/sweep.json + per-defense subdirs")
    if latex_path is not None:
        print(f"LaTeX table: {latex_path}")
    return 0


def cmd_resolution(args: argparse.Namespace) -> int:
    """Run the GP-smooth-oblique validation at multiple grid resolutions."""
    from .resolution import run_resolution_sweep

    out: Path = args.output
    out.mkdir(parents=True, exist_ok=True)

    resolutions = list(args.resolutions) if args.resolutions else [13, 17, 21, 25]
    rows = run_resolution_sweep(
        archive_path=args.archive,
        out_dir=out,
        tau=args.tau,
        resolutions=resolutions,
        length_scale=args.length_scale,
        noise=args.noise,
        alpha_step=args.alpha_step,
        sigmoid_steepness=args.sigmoid_steepness,
        oblique_angle_deg=args.oblique_angle,
    )

    print()
    print("=" * 96)
    print(
        f"Resolution sweep  ·  τ = {args.tau}  ·  source = {args.archive}"
    )
    print("=" * 96)
    header = (
        f"{'grid':>6} {'stride':>7} {'filled':>7} {'L':>7} {'K':>7} "
        f"{'ell':>7} {'G':>7} {'|S_pred|':>9} {'TP':>4} {'FP_int':>7} {'FN':>5}"
    )
    print(header)
    print("-" * 96)
    for r in rows:
        print(
            f"{r.grid_size:>6} {r.stride:>7.3f} {r.filled_cells:>7} "
            f"{r.L:>7.3f} {r.K:>7.3f} {r.ell:>7.3f} {r.G:>7.3f} "
            f"{r.predicted_persistent_count:>9} {r.true_positives:>4} "
            f"{r.false_positives_interior:>7} {r.false_negatives:>5}"
        )
    print()
    print(f"Outputs: {out}/resolution.json, {out}/<N>x<N>/result.json")
    return 0


def _register_extension_subcommands(sub) -> None:
    """Register the sensitivity and csweep subcommands."""
    se = sub.add_parser(
        "sensitivity",
        help="GP kernel × length-scale sensitivity sweep (oblique defense).",
        description=(
            "For each (kernel, sigma) in the Cartesian product of --kernels and "
            "--sigmas, fit a GP posterior to the archive and run the oblique "
            "GP-smooth defense. Writes per-cell JSON, a combined sensitivity.json, "
            "and (optionally) a LaTeX fragment."
        ),
    )
    se.add_argument(
        "--archive",
        type=Path,
        required=True,
        help="Path to a rethinking-evals final_archive.json.",
    )
    se.add_argument("--tau", type=float, default=0.5, help="Safety threshold. Default: 0.5.")
    se.add_argument(
        "--kernels",
        nargs="+",
        default=["rbf", "matern32", "matern52"],
        choices=["rbf", "matern32", "matern52"],
        help="Kernel families to sweep. Default: rbf matern32 matern52.",
    )
    se.add_argument(
        "--sigmas",
        type=float,
        nargs="+",
        default=[0.1, 0.2, 0.4],
        help="Length-scales to sweep. Default: 0.1 0.2 0.4.",
    )
    se.add_argument("--noise", type=float, default=0.02, help="GP noise. Default: 0.02.")
    se.add_argument(
        "--alpha-step",
        type=float,
        default=0.003,
        help="Oblique defense step size. Default: 0.003.",
    )
    se.add_argument(
        "--sigmoid-steepness",
        type=float,
        default=2.0,
        help="Sigmoid β-bump steepness. Default: 2.0.",
    )
    se.add_argument(
        "--oblique-angle",
        type=float,
        default=89.5,
        help="Oblique angle in degrees from the negative gradient. Default: 89.5.",
    )
    se.add_argument(
        "--out",
        type=Path,
        required=True,
        help="Output directory (written to sensitivity.json and per-cell subdirs).",
    )
    se.add_argument(
        "--latex",
        type=Path,
        default=None,
        help="Optional path to a LaTeX fragment for the sensitivity table.",
    )
    se.set_defaults(func=cmd_sensitivity)

    cs = sub.add_parser(
        "csweep",
        help="Run the four continuous defenses on a single archive and compare.",
        description=(
            "Runs smooth_nearest_safe, kernel_smoothed, softly_constrained_projection, "
            "and oblique_gp_smooth on the archive at a fixed tau, producing a table "
            "of L, K, ℓ, G, transversality, and the persistence confusion matrix."
        ),
    )
    cs.add_argument(
        "--archive",
        type=Path,
        required=True,
        help="Path to a rethinking-evals final_archive.json.",
    )
    cs.add_argument("--tau", type=float, default=0.5, help="Safety threshold. Default: 0.5.")
    cs.add_argument(
        "--radius",
        type=float,
        default=3.0,
        help="Radius (grid cells) for smooth_nearest_safe. Default: 3.0.",
    )
    cs.add_argument(
        "--bandwidth",
        type=float,
        default=2.5,
        help="Bandwidth (grid cells) for kernel_smoothed. Default: 2.5.",
    )
    cs.add_argument(
        "--alpha",
        type=float,
        default=2.0,
        help="Soft-constraint weight for softly_constrained_projection. Default: 2.0.",
    )
    cs.add_argument(
        "--oblique-angle",
        type=float,
        default=89.5,
        help="Oblique angle for oblique_gp_smooth. Default: 89.5.",
    )
    cs.add_argument(
        "--out",
        type=Path,
        required=True,
        help="Output directory (written to sweep.json and per-defense subdirs).",
    )
    cs.add_argument(
        "--latex",
        type=Path,
        default=None,
        help="Optional path to a LaTeX fragment for the continuous-sweep table.",
    )
    cs.set_defaults(func=cmd_csweep)


def _add_resolution_subcommand(sub) -> None:
    """Register the ``trilemma resolution`` subcommand."""
    res = sub.add_parser(
        "resolution",
        help=(
            "Resolution-sensitivity sweep: subsample the 25×25 archive and "
            "re-run the GP-smooth oblique defense at each grid resolution."
        ),
        description=(
            "Subsample the source archive to multiple resolutions using "
            "deterministic stride + floor and run the GP-smooth oblique "
            "defense at each. Measures L, K, ℓ, G, |S_pred|, TP, FP_int, FN "
            "per resolution."
        ),
    )
    res.add_argument(
        "--archive",
        type=Path,
        required=True,
        help="Path to a rethinking-evals final_archive.json (source, 25×25).",
    )
    res.add_argument(
        "--tau",
        type=float,
        default=0.5,
        help="Safety threshold τ. Default: 0.5.",
    )
    res.add_argument(
        "--resolutions",
        type=int,
        nargs="+",
        default=[13, 17, 21, 25],
        help="Grid resolutions to sweep. Default: 13 17 21 25.",
    )
    res.add_argument("--length-scale", type=float, default=0.20)
    res.add_argument("--noise", type=float, default=0.02)
    res.add_argument("--alpha-step", type=float, default=0.003)
    res.add_argument("--sigmoid-steepness", type=float, default=2.0)
    res.add_argument(
        "--oblique-angle",
        type=float,
        default=89.5,
        help="Oblique angle in degrees. Default: 89.5 (paper setting).",
    )
    res.add_argument(
        "--out",
        dest="output",
        type=Path,
        required=True,
        help="Output directory for per-resolution results.",
    )
    res.set_defaults(func=cmd_resolution)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="trilemma",
        description=(
            "Empirical validator for the Defense Trilemma theorems. "
            "Loads an alignment-deviation heatmap (or runs rethinking-evals to produce one), "
            "applies a discrete defense, and checks Theorems 4.1, 5.1, and 6.2."
        ),
    )
    sub = parser.add_subparsers(dest="command", required=True)

    # validate
    val = sub.add_parser(
        "validate",
        help="Validate a heatmap that already exists on disk.",
        description="Validate a heatmap that already exists on disk.",
    )
    src = val.add_mutually_exclusive_group(required=True)
    src.add_argument(
        "--heatmap",
        type=Path,
        help="Path to a .npy heatmap (output of Archive.to_heatmap).",
    )
    src.add_argument(
        "--archive",
        type=Path,
        help="Path to a rethinking-evals final_archive.json.",
    )
    _shared_validate_args(val)
    val.set_defaults(func=cmd_validate)

    # synth
    sy = sub.add_parser(
        "synth",
        help="Generate a synthetic heatmap and validate it (no API calls).",
        description=(
            "Generate a synthetic heatmap (mesa / mosaic / flat) and validate it. "
            "Use this to verify the validator is working before running real experiments."
        ),
    )
    sy.add_argument(
        "--shape",
        choices=("mesa", "mosaic", "flat"),
        default="mesa",
        help="Surface shape to synthesize. Default: mesa (Llama-like).",
    )
    sy.add_argument(
        "--grid",
        type=int,
        default=25,
        help="Grid size per dimension. Default: 25 (matches rethinking-evals default).",
    )
    sy.add_argument("--seed", type=int, default=0, help="RNG seed. Default: 0.")
    _shared_validate_args(sy)
    sy.set_defaults(func=cmd_synth)

    # experiment
    ex = sub.add_parser(
        "experiment",
        help="Run rethinking-evals to produce a heatmap (no validation).",
    )
    ex.add_argument(
        "--rethinking-path",
        type=Path,
        required=True,
        help="Path to a rethinking-evals checkout.",
    )
    ex.add_argument(
        "--model",
        default="gpt5_mini",
        help="Target model name from rethinking-evals' models.yaml. Default: gpt5_mini.",
    )
    ex.add_argument(
        "--iterations",
        type=int,
        default=100,
        help="MAP-Elites iterations. Default: 100 (set higher for production).",
    )
    ex.add_argument(
        "--seed-prompts",
        type=int,
        default=50,
        help="Number of seed prompts. Default: 50.",
    )
    ex.add_argument(
        "--judge",
        type=str,
        default="gpt-4.1-2025-04-14",
        help=(
            "OpenAI model ID used to score alignment deviation. "
            "Default: gpt-4.1-2025-04-14 (the paper's canonical judge). "
            "Swap this for the judge-robustness comparison described in "
            "live_runs/judge_robustness_pending.md."
        ),
    )
    ex.add_argument(
        "--output",
        type=Path,
        default=Path("./trilemma_out"),
        help="Output directory. Default: ./trilemma_out",
    )
    ex.set_defaults(func=cmd_experiment)

    # pipeline (experiment + validate)
    pp = sub.add_parser(
        "pipeline",
        help="Run rethinking-evals AND validate its output in one shot.",
        description=(
            "End-to-end: run rethinking-evals on the chosen model, load the resulting "
            "heatmap, then run all three theorem checks. Requires OPENAI_API_KEY."
        ),
    )
    pp.add_argument(
        "--rethinking-path",
        type=Path,
        required=True,
        help="Path to a rethinking-evals checkout.",
    )
    pp.add_argument("--model", default="gpt5_mini")
    pp.add_argument("--iterations", type=int, default=100)
    pp.add_argument("--seed-prompts", type=int, default=50)
    pp.add_argument(
        "--judge",
        type=str,
        default="gpt-4.1-2025-04-14",
        help=(
            "OpenAI model ID used to score alignment deviation. "
            "Default: gpt-4.1-2025-04-14 (the paper's canonical judge). "
            "Swap this for the judge-robustness comparison described in "
            "live_runs/judge_robustness_pending.md."
        ),
    )
    _shared_validate_args(pp)
    pp.set_defaults(func=cmd_pipeline)

    # sweep
    sw = sub.add_parser(
        "sweep",
        help="Run multiple defenses on a single archive (saturation study).",
        description=(
            "Validate a heatmap against the identity defense AND multiple "
            "bounded_step defenses with different reach parameters. Produces "
            "a comparison table showing the K-tradeoff explicitly: as the "
            "defense's Lipschitz constant increases, the predicted steep set "
            "shrinks but the actual persistent set may also shrink."
        ),
    )
    sw_src = sw.add_mutually_exclusive_group(required=True)
    sw_src.add_argument("--heatmap", type=Path, help="Path to a .npy heatmap.")
    sw_src.add_argument(
        "--archive",
        type=Path,
        help="Path to a rethinking-evals final_archive.json.",
    )
    sw.add_argument(
        "--tau",
        type=float,
        default=0.5,
        help="Safety threshold τ. Default: 0.5.",
    )
    sw.add_argument(
        "--max-steps",
        type=int,
        nargs="+",
        default=[1, 2, 3, 5, 8],
        help="Max-step values to sweep for the bounded_step defense. "
        "Default: 1 2 3 5 8.",
    )
    sw.add_argument(
        "--output",
        type=Path,
        default=Path("./trilemma_sweep_out"),
        help="Output directory. Default: ./trilemma_sweep_out",
    )
    sw.set_defaults(func=cmd_sweep)

    _register_extension_subcommands(sub)
    _add_resolution_subcommand(sub)

    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args) or 0)


if __name__ == "__main__":
    sys.exit(main())
