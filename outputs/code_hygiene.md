# Code Hygiene Audit — `trilemma_validator/src/trilemma_validator/`

Static audit as of the merge that added `csweep.py`, `kernels.py`,
`resolution.py`, and `sensitivity.py`. Read-only — any fix belongs to
the owning code agent.

## Top-level modules audited

```
__init__.py       3 LOC
__main__.py       4 LOC
cli.py          703 LOC
csweep.py       231 LOC
defenses.py     587 LOC
kernels.py      159 LOC
lipschitz.py    406 LOC
loader.py       101 LOC
report.py       356 LOC
resolution.py   488 LOC
runner.py       157 LOC
sensitivity.py  454 LOC
synth.py        106 LOC
theorems.py     746 LOC
uncertainty.py  127 LOC
viz.py          180 LOC
```

Plus `scripts/make_paper_figure.py` (out of package but in the same
tree).

## 1. Duplicate functions across modules

The paper's GP-smooth oblique defense is implemented in **three
separate places**, with subtly divergent kernel, gradient, and Lipschitz
estimation code:

| Name | Location | Lines | Status |
|---|---|---|---|
| `_rbf` | `scripts/make_paper_figure.py` | 45–48 | duplicate; hard-coded RBF |
| `_rbf` | `resolution.py` | 145 | duplicate; hard-coded RBF |
| `rbf_kernel` | `kernels.py` | 39 | canonical; generic-signature version |
| `fit_gp_2d` / `gp_predict` / `gp_gradient` (module-local `gp` dict) | `scripts/make_paper_figure.py` | 51, 72, 78 | duplicate implementation |
| `_fit_gp` / `_gp_predict` / `_gp_gradient` (private module-local `gp` dict) | `resolution.py` | 150, 163, 168 | duplicate implementation |
| `fit_gp` / `gp_predict` / `gp_gradient` (uses `GPFit` dataclass + `kernels.py`) | `sensitivity.py` | 48, 67, 73 | canonical; uses swappable kernel |
| `_smooth_bump` | `sensitivity.py` | 96 | canonical |
| `_smooth_bump` | `resolution.py` | 176 | duplicate |
| `oblique_target` | `sensitivity.py` | 100 | canonical |
| `_oblique_target` | `resolution.py` | 180 | duplicate |
| `gp_max_grad_norm` | `scripts/make_paper_figure.py` | 91 | duplicate |
| `gp_max_grad_norm` | `sensitivity.py` | 79 | canonical |

**Impact:** three of the paper's tables (`tab:gp-sensitivity`,
`tab:continuous-sweep`, `tab:resolution`) depend on the continuous
defense behavior, and each table exercises a different implementation.
A mismatch in the GP kernel/gradient math across implementations could
silently produce inconsistent numbers across tables.

**Recommendation (for the owning code agent):** replace the private
`_rbf` / `_fit_gp` / `_gp_*` / `_smooth_bump` / `_oblique_target` in
`resolution.py` with imports from `sensitivity.py`; replace the
module-local GP in `scripts/make_paper_figure.py` similarly. After
consolidation, all three tables share exactly one GP implementation.

No `bootstrap_ci` duplication — only one copy, in `uncertainty.py`.
No duplicate Lipschitz estimators — `lipschitz.py` is the single
source of truth (sensitivity.py's ad-hoc per-pair `K_emp` / `ell_emp`
computation inside `run_sensitivity_cell` does duplicate the logic
but uses raw-index coordinates rather than normalized `[0,1]^2`, so it
is not a drop-in use of `estimate_defense_K` / `estimate_defense_path_ell`;
this is intentional, not a bug).

## 2. Undefined / dead references

**HIGH-SEVERITY BUG.** `cli.py:422`:

```python
rows.append(_sweep_gp_smooth_oblique(heatmap, args.tau, out))
```

`_sweep_gp_smooth_oblique` is referenced but **never defined** anywhere
in the package. This branch is taken when the user passes
`--defense oblique_gp_smooth` to `trilemma sweep`; the command will
raise `NameError` at runtime. The CLI registered a user-visible name
(`oblique_gp_smooth`) in `cli.py:409–411` so a user following the
paper's command examples can trip this.

**Fix (for the code agent):** route the `oblique_gp_smooth` branch
through `csweep._run_gp_oblique` or `sensitivity.run_sensitivity_cell`.

## 3. Dead imports / unused symbols (top ~10)

Ripgrep + a hand audit of each module. These are read-only — the
owning agent should act on them.

| # | Symbol | Module | Line | Notes |
|---|---|---|---|---|
| 1 | `from .theorems import ..., _post_defense_values` | `viz.py` | 13 | Uses a **private** (underscore) function from `theorems.py`. Not strictly dead, but a layering violation: `viz` reaches into `theorems`'s private API rather than importing the public `run_full_validation` output. |
| 2 | `import textwrap` | `runner.py` | 16 | Never used in the module body. |
| 3 | `from typing import Callable, Iterable` | `sensitivity.py` | 21 | `Callable` used in `GPFit` dataclass; `Iterable` used for hints. Both are live. (**Not dead** — listed so the owning agent knows the audit checked it.) |
| 4 | `import numpy as np` in `csweep.py` | `csweep.py` | 15 | only used via `_json_safe` for `np.floating`/`np.integer`/`np.ndarray` isinstance checks. Live but narrow. |
| 5 | `Optional` from `typing` | `resolution.py` | 47 | Used in `ResolutionResult`; live. |
| 6 | `field` from `dataclasses` | `resolution.py` | 45 | Used in `ResolutionResult`; live. |
| 7 | `Tuple` from `typing` | `uncertainty.py` | 27 | Used in return type annotation; live. |
| 8 | `np` in `report.py` | `report.py` | 8 | Never actually used inside the module body (only `json`, path operations, and string formatting are used). Dead. |
| 9 | `NearestSafeDefense` factory branch | `defenses.py` | 484 | Exposed via `get_defense("nearest_safe")` but `_DEFENSE_CHOICES` in `cli.py:35–42` **does not include** `nearest_safe`. Effectively unreachable from the CLI; only reachable via the Python API. Either add to `_DEFENSE_CHOICES` (documented in the README) or drop from `get_defense`. |
| 10 | `args.judge` access before `add_argument` | `cli.py:344` | 344 | `cmd_experiment` reads `args.judge` via `getattr` — defensive and live, but confusing because the `--judge` argument was only added after the stub-emission logic. Style nit. |

Of these, only (1) the private-API import in `viz.py`, (2) the
`textwrap` import in `runner.py`, (8) the `np` import in `report.py`,
and (9) the unexposed `nearest_safe` route are genuinely dead or
unwelcome. The rest are live.

## 4. `print()` statements that should be `logging`

45 `print()` calls live in `cli.py`; 1 in `runner.py`.

`cli.py`:

- Lines 165–171, 173–253, 258, 314, 341–344, 372, 491–535: **all 45 are
  user-facing output of a CLI tool.** They belong on `stdout` (the
  command's whole purpose is to summarize a validation result), so they
  are arguably correct as `print()`. However:
  - Line 258, 265: `print(..., file=sys.stderr)` is correct for error
    messaging.
  - Line 314: `print(..., file=sys.stderr)` for the "API key not set"
    notice, also correct.
  - The other 42 prints would be cleaner as a logger-backed printer so
    library users (tests, notebooks, automation) can suppress them. Not
    urgent.

`runner.py:139`:

```python
print(f"[trilemma] running rethinking-evals: {' '.join(cmd)}", flush=True)
```

This fires from inside what is otherwise a library function
(`run_experiment`). It should be a `logging.info(...)` call — callers
that build a pipeline on top of `run_experiment` have no way to silence
it. **Recommended conversion** for the owning agent: move to
`logger.info(...)` with a module-level `logger = logging.getLogger(__name__)`.

## 5. Docstring coverage on public functions

A quick audit: every public top-level function in every module has a
docstring. Highlights:

- `lipschitz.py`: 6/6 public functions have full docstrings including
  formulas, pair-count conventions, and symmetry notes.
- `theorems.py`: every dataclass, `run_full_validation`,
  `check_boundary_fixation`, `check_eps_robust`, `check_persistence`,
  `find_boundary_cells` have docstrings.
- `defenses.py`: every `Defense` subclass and every builder function
  has a docstring, most with the formal formula and Lipschitz argument.
- `uncertainty.py`: both public functions have docstrings.
- `loader.py`, `report.py`, `viz.py`, `synth.py`, `kernels.py`: every
  public function/class has a docstring.
- `csweep.py`: `run_continuous_sweep`, `render_continuous_sweep_latex`,
  `run_continuous_sweep_from_archive` are documented. The `_run_*`
  helpers have brief docstrings.
- `sensitivity.py`: every public function has a docstring.
- `resolution.py`: every public function has a docstring.

**No missing docstrings on public API.** A handful of private helpers
(`_rbf`, `_pairwise_dist` in `kernels.py`, `_json_safe` in `csweep.py`)
have one-line descriptions; acceptable.

## 6. Miscellaneous observations

- **Magic number consistency.** The oblique angle `89.5°` is
  hard-coded in `sensitivity.py::run_sensitivity_cell` (default) and
  `resolution.py::run_gp_smooth_oblique` (private). Both match the
  paper; once the GP code is consolidated, the constant should live in
  one place.
- **No type stubs.** The package uses PEP 585 / 604 syntax (`list[...]`,
  `X | None`) which requires Python 3.10. `pyproject.toml` declares
  `requires-python = ">=3.9"` — on 3.9, imports will fail. Either bump
  the floor to 3.10 or switch to `typing.List` / `Optional[X]`.
- **`args.judge` threading in `cmd_pipeline`.** `--judge` is registered
  on the `pipeline` subparser (cli.py:666) but the `_apply_judge_env`
  call at `cli.py:352` is the only propagation to
  `RETHINKING_JUDGE_MODEL`. Works, but note the judge isn't written
  into `result.json` — downstream judge-robustness analysis has no
  in-band record of which judge scored each archive. Flag for Agent 4
  if a judge-robustness comparison is desired.

## Priority list for the code agent

1. **Fix the `NameError` at `cli.py:422`** — user-visible CLI crash.
2. Consolidate the three GP implementations behind
   `sensitivity.py`'s `GPFit` / `fit_gp` API; drop the `_rbf` /
   `_fit_gp` / `_gp_predict` / `_gp_gradient` duplicates in
   `resolution.py` and `scripts/make_paper_figure.py`.
3. Convert `runner.py:139` `print` to `logging.info`.
4. Remove the dead `import textwrap` in `runner.py` and unused
   `import numpy as np` in `report.py`.
5. Either expose `nearest_safe` in `_DEFENSE_CHOICES` or drop it from
   `get_defense`.
