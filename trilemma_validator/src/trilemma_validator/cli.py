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

import numpy as np

from . import loader, report, synth, theorems, viz
from .defenses import get_defense
from .runner import ExperimentConfig, run_experiment


def _shared_validate_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--tau",
        type=float,
        default=0.5,
        help="Safety threshold τ. Default: 0.5.",
    )
    parser.add_argument(
        "--defense",
        choices=("identity", "nearest_safe", "bounded_step"),
        default="bounded_step",
        help=(
            "Which defense to simulate on the heatmap. "
            "'bounded_step' is the most informative on real grids "
            "(use --max-step to control its Lipschitz behavior). "
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
        "--output",
        type=Path,
        default=Path("./trilemma_out"),
        help="Output directory. Default: ./trilemma_out",
    )


def _do_validate(heatmap, args, *, source_label: str) -> int:
    """Shared validation pipeline used by validate / synth / pipeline."""
    defense_obj = get_defense(args.defense, max_step=args.max_step)
    defense = defense_obj.build(heatmap, args.tau)
    result = theorems.run_full_validation(heatmap, args.tau, defense)

    out: Path = args.output
    out.mkdir(parents=True, exist_ok=True)

    np.save(out / "heatmap.npy", heatmap.values)
    report.write_json(result, out / "result.json")
    report.write_markdown(result, out / "report.md")
    viz.render(heatmap, defense, args.tau, result, out / "validation.png")

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


def cmd_experiment(args: argparse.Namespace) -> int:
    cfg = ExperimentConfig(
        rethinking_path=args.rethinking_path,
        model=args.model,
        iterations=args.iterations,
        seed_prompts=args.seed_prompts,
        output_dir=args.output / "rethinking_run",
    )
    archive_path = run_experiment(cfg)
    print()
    print(f"experiment complete. archive at: {archive_path}")
    return 0


def cmd_pipeline(args: argparse.Namespace) -> int:
    cfg = ExperimentConfig(
        rethinking_path=args.rethinking_path,
        model=args.model,
        iterations=args.iterations,
        seed_prompts=args.seed_prompts,
        output_dir=args.output / "rethinking_run",
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

    # Defenses to compare: identity, then bounded_step at several max_step values.
    sweep_specs: list[tuple[str, dict]] = [("identity", {})]
    for ms in args.max_steps:
        sweep_specs.append(("bounded_step", {"max_step": int(ms)}))

    rows: list[dict] = []
    for defense_name, params in sweep_specs:
        defense_obj = get_defense(defense_name, max_step=params.get("max_step"))
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
        slug = (
            defense_name
            if not params
            else f"{defense_name}_max{params['max_step']}"
        )
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
        f"{'defense':<18} {'K':>6} {'ell':>7} {'G':>7} {'transv?':>8} "
        f"{'|S_pred|':>9} {'|S_act|':>8} {'TP':>4} {'FPint':>6} "
        f"{'FPbdy':>6} {'FN':>5} {'verdict':>14}"
    )
    print(header)
    print("-" * 96)
    for r in rows:
        if r["params"]:
            name = f"bounded_step({r['params']['max_step']})"
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
            f"{name:<18} {r['K']:>6.2f} {r['ell']:>7.3f} {r['G']:>7.3f} "
            f"{('YES' if r['transversality'] else 'no'):>8} "
            f"{r['predicted_steep']:>9} {r['actual_persistent']:>8} "
            f"{r['true_positives']:>4} {r['fp_interior']:>6} "
            f"{r['fp_boundary']:>6} {r['false_negatives']:>5} "
            f"{verdict:>14}"
        )
    print()
    print(f"Outputs: {out}/sweep.json, {out}/per_defense/")
    return 0


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

    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args) or 0)


if __name__ == "__main__":
    sys.exit(main())
