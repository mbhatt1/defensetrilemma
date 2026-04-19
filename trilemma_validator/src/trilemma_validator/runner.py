"""Subprocess wrapper for invoking ``rethinking-evals`` to produce a heatmap.

This module does not assume rethinking-evals is installed in the same Python
environment. It runs the experiment script as a subprocess in whatever
environment the user points to (typically a uv-managed venv inside the
rethinking-evals checkout). The trilemma validator then loads the resulting
``final_archive.json`` from disk.
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import textwrap
from dataclasses import dataclass
from pathlib import Path

# Path to the judge-robustness stub that ``run_experiment`` writes when the
# caller has not configured an OpenAI API key. Defined at module scope so
# the CLI can reference the canonical location from its help text.
_PENDING_STUB_RELATIVE = Path("live_runs") / "judge_robustness_pending.md"


@dataclass
class ExperimentConfig:
    rethinking_path: Path
    model: str
    iterations: int
    seed_prompts: int
    output_dir: Path
    python: str | None = None  # path to python; defaults to ``uv run``
    # OpenAI model ID used as the alignment-deviation judge. The paper's
    # canonical value is ``gpt-4.1-2025-04-14``; swapping this lets us
    # run the judge-robustness comparison described in
    # ``live_runs/judge_robustness_pending.md``.
    judge_model: str = "gpt-4.1-2025-04-14"


def _resolve_runner(rethinking_path: Path) -> list[str]:
    """Return the command prefix used to invoke the experiment script.

    Prefers ``uv run`` if a ``uv`` binary is on PATH (rethinking-evals's
    documented installation method); falls back to the current Python.
    """
    if shutil.which("uv") is not None:
        return ["uv", "run", "python"]
    return [sys.executable]


_PENDING_STUB_TEXT = textwrap.dedent(
    """\
    # Judge-robustness evaluation (pending)

    The paper uses `gpt-4.1-2025-04-14` as the alignment-deviation judge. A full two-judge comparison is future work.

    To rerun with a different judge, set `OPENAI_API_KEY` and:

        trilemma experiment --target gpt-3.5-turbo-0125 --judge <alternative-judge-id> --tau 0.5 ...

    Expected outputs: a parallel archive under `live_runs/` whose heatmap can be compared against the canonical `gpt35_turbo_t05_saturated/` surface.

    Cost estimate: ~5,200 API calls for a saturated 25\u00d725 archive, roughly $15 at current gpt-4.1 pricing.
    """
)


def _write_judge_pending_stub(cfg: ExperimentConfig) -> Path:
    """Write the canonical judge-robustness placeholder stub.

    Called when ``run_experiment`` cannot proceed (no ``OPENAI_API_KEY``).
    We write the *canonical* static content (the same text version-
    controlled at ``live_runs/judge_robustness_pending.md``), not a
    dynamic one-off — the stub is a permanent marker that the
    judge-robustness comparison is future work, not a log of the aborted
    call. If the file already exists we leave it alone to avoid
    clobbering manual edits. The ``cfg`` argument is accepted for
    symmetry with future multi-judge extensions.
    """
    del cfg  # currently unused; kept for forward compatibility.
    # runner.py lives at src/trilemma_validator/runner.py; walk up to the
    # trilemma_validator package root.
    pkg_root = Path(__file__).resolve().parents[2]
    stub = pkg_root / _PENDING_STUB_RELATIVE
    stub.parent.mkdir(parents=True, exist_ok=True)
    if not stub.exists():
        stub.write_text(_PENDING_STUB_TEXT)
    return stub


def run_experiment(cfg: ExperimentConfig) -> Path:
    """Run rethinking-evals end-to-end and return the path to ``final_archive.json``.

    Raises ``RuntimeError`` if the subprocess returns non-zero or if the
    expected output file is missing. When ``OPENAI_API_KEY`` is not set
    the function writes the judge-robustness pending stub (so the caller
    has a machine-readable marker of why the run was skipped) and then
    raises — there is no way to make the upstream rethinking-evals call
    without a key.
    """
    cfg.rethinking_path = cfg.rethinking_path.resolve()
    cfg.output_dir = cfg.output_dir.resolve()
    cfg.output_dir.mkdir(parents=True, exist_ok=True)

    script = cfg.rethinking_path / "experiments" / "run_main_experiment.py"
    if not script.exists():
        raise FileNotFoundError(
            f"rethinking-evals run script not found at {script}. "
            f"Pass --rethinking-path pointing at the repo root."
        )

    if "OPENAI_API_KEY" not in os.environ:
        stub = _write_judge_pending_stub(cfg)
        raise RuntimeError(
            "OPENAI_API_KEY is not set in the environment. "
            "rethinking-evals cannot make API calls without it. "
            f"Wrote judge-robustness placeholder to {stub}."
        )

    cmd = [
        *_resolve_runner(cfg.rethinking_path),
        str(script),
        "--model",
        cfg.model,
        "--iterations",
        str(cfg.iterations),
        "--seed-prompts",
        str(cfg.seed_prompts),
        "--output-dir",
        str(cfg.output_dir),
        # Thread the judge model through so rethinking-evals scores
        # alignment-deviation with the user-selected judge. The exact
        # flag name matches rethinking-evals' ``--judge-model`` CLI.
        "--judge-model",
        cfg.judge_model,
    ]

    print(f"[trilemma] running rethinking-evals: {' '.join(cmd)}", flush=True)
    result = subprocess.run(
        cmd,
        cwd=str(cfg.rethinking_path),
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"rethinking-evals exited with code {result.returncode}. "
            f"See its output above for the failure cause."
        )

    archive = cfg.output_dir / "final_archive.json"
    if not archive.exists():
        raise FileNotFoundError(
            f"rethinking-evals completed but {archive} was not produced. "
            f"Inspect the output directory for partial results."
        )
    return archive
