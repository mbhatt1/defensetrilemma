"""Package-level smoke tests for the trilemma validator.

These tests are deliberately small, have no external dependencies beyond
``numpy`` and the package itself, and finish in a few seconds. They
exist to catch regressions in

* the CLI wiring (``trilemma synth`` / ``trilemma validate``),
* every continuous defense building cleanly on a synthetic heatmap,
* the bootstrap-CI routine returning sensible ordering on random input.

The tests are written against the Python ``unittest`` framework so they
run under both ``pytest`` (if available) and the stdlib runner. The
``pyproject.toml`` lists ``pytest`` under the ``dev`` optional
dependency group; we do not require it at test time.

Run with either::

    python -m pytest trilemma_validator/tests/
    python -m unittest trilemma_validator.tests.test_smoke

or, from the package directory::

    python -m unittest tests.test_smoke
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


# --------------------------------------------------------------------
# Test 1: ``trilemma synth --help`` exits 0.
# --------------------------------------------------------------------


class TestCLIHelp(unittest.TestCase):
    """``trilemma synth --help`` should exit 0 and mention 'shape'."""

    def test_synth_help_exits_zero(self) -> None:
        proc = subprocess.run(
            [sys.executable, "-m", "trilemma_validator", "synth", "--help"],
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(
            proc.returncode,
            0,
            msg=f"trilemma synth --help exited {proc.returncode}\n"
            f"stdout: {proc.stdout}\nstderr: {proc.stderr}",
        )
        # Sanity: the help text mentions the shape argument.
        self.assertIn("shape", (proc.stdout + proc.stderr).lower())


# --------------------------------------------------------------------
# Test 2: ``trilemma synth`` (default args) produces a heatmap.
# --------------------------------------------------------------------


class TestSynthProducesHeatmap(unittest.TestCase):
    """``trilemma synth`` should produce a 25x25 heatmap.npy and result.json."""

    def test_synth_mesa_default(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "synth_out"
            proc = subprocess.run(
                [
                    sys.executable,
                    "-m",
                    "trilemma_validator",
                    "synth",
                    "--shape",
                    "mesa",
                    "--output",
                    str(out),
                ],
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(
                proc.returncode,
                0,
                msg=f"trilemma synth exited {proc.returncode}\n"
                f"stdout: {proc.stdout}\nstderr: {proc.stderr}",
            )
            self.assertTrue((out / "heatmap.npy").exists())
            self.assertTrue((out / "result.json").exists())
            self.assertTrue((out / "report.md").exists())
            # validation.png is the paper's figure-panel; produced too.
            self.assertTrue((out / "validation.png").exists())

            import numpy as np

            arr = np.load(out / "heatmap.npy")
            self.assertEqual(arr.ndim, 2)
            self.assertEqual(arr.shape[0], arr.shape[1])
            self.assertEqual(arr.shape[0], 25)  # default grid size


# --------------------------------------------------------------------
# Test 3: ``trilemma validate`` on the synth heatmap produces result.json
# with expected keys.
# --------------------------------------------------------------------


_EXPECTED_TOP_LEVEL_KEYS = {
    "tau",
    "grid_size",
    "coverage",
    "safe_count",
    "unsafe_count",
    "applicable",
    "estimates",
    "defense",
    "theorem_4_1_boundary_fixation",
    "theorem_5_1_eps_robust",
    "theorem_6_2_persistent_unsafe_region",
    "cell_observations",
}


class TestValidateRoundTrip(unittest.TestCase):
    """Run ``synth`` then ``validate --heatmap`` and check the JSON schema."""

    def test_validate_on_synth_heatmap(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            synth_out = Path(tmp) / "synth"
            proc = subprocess.run(
                [
                    sys.executable,
                    "-m",
                    "trilemma_validator",
                    "synth",
                    "--shape",
                    "mesa",
                    "--output",
                    str(synth_out),
                ],
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(proc.returncode, 0, msg=proc.stderr)

            validate_out = Path(tmp) / "validate"
            proc = subprocess.run(
                [
                    sys.executable,
                    "-m",
                    "trilemma_validator",
                    "validate",
                    "--heatmap",
                    str(synth_out / "heatmap.npy"),
                    "--defense",
                    "identity",
                    "--tau",
                    "0.5",
                    "--bootstrap",
                    "20",
                    "--output",
                    str(validate_out),
                ],
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(
                proc.returncode,
                0,
                msg=f"trilemma validate exited {proc.returncode}\n"
                f"stderr: {proc.stderr}",
            )

            result_path = validate_out / "result.json"
            self.assertTrue(result_path.exists())
            with result_path.open() as f:
                payload = json.load(f)

            missing = _EXPECTED_TOP_LEVEL_KEYS - set(payload.keys())
            self.assertFalse(
                missing,
                msg=f"result.json missing expected keys: {missing}",
            )

            # Per-cell records exist.
            self.assertIsInstance(payload["cell_observations"], list)
            if payload["cell_observations"]:
                first = payload["cell_observations"][0]
                for key in ("cell", "f", "D_x", "f_D_x", "dist_to_anchor"):
                    self.assertIn(key, first)

            # Bootstrap enrichment under a small B.
            self.assertIn("bootstrap", payload)
            for name in ("ci_L", "ci_K", "ci_ell", "ci_G"):
                self.assertIn(name, payload["bootstrap"])
                ci = payload["bootstrap"][name]
                # Each CI has median, lo, hi (allow lo==hi==median when population is
                # degenerate, e.g. identity defense on a flat surface giving ell=0).
                self.assertIn("median", ci)
                self.assertIn("lo", ci)
                self.assertIn("hi", ci)


# --------------------------------------------------------------------
# Test 4: every continuous defense can be built on a synthetic heatmap.
# --------------------------------------------------------------------


class TestContinuousDefensesBuild(unittest.TestCase):
    """Each continuous defense factory must build a DefenseMap without error."""

    def setUp(self) -> None:
        from trilemma_validator.synth import make

        self.heatmap = make("mesa", grid_size=15, seed=0)  # small for speed
        self.tau = 0.5

    def test_smooth_nearest_safe_builds(self) -> None:
        from trilemma_validator.defenses import get_defense

        defense = get_defense("smooth_nearest_safe", radius=3.0).build(
            self.heatmap, self.tau
        )
        self.assertEqual(defense.name, "smooth_nearest_safe")
        self.assertEqual(defense.targets.shape, (15, 15, 2))

    def test_kernel_smoothed_builds(self) -> None:
        from trilemma_validator.defenses import get_defense

        defense = get_defense("kernel_smoothed", bandwidth=2.5).build(
            self.heatmap, self.tau
        )
        self.assertEqual(defense.name, "kernel_smoothed")
        self.assertEqual(defense.targets.shape, (15, 15, 2))

    def test_softly_constrained_projection_builds(self) -> None:
        from trilemma_validator.defenses import get_defense

        defense = get_defense(
            "softly_constrained_projection", alpha=2.0
        ).build(self.heatmap, self.tau)
        self.assertEqual(defense.name, "softly_constrained_projection")
        self.assertEqual(defense.targets.shape, (15, 15, 2))

    def test_identity_and_bounded_step_build(self) -> None:
        from trilemma_validator.defenses import get_defense

        identity = get_defense("identity").build(self.heatmap, self.tau)
        self.assertEqual(identity.name, "identity")
        bounded = get_defense("bounded_step", max_step=2).build(
            self.heatmap, self.tau
        )
        self.assertEqual(bounded.name, "bounded_step")
        self.assertEqual(bounded.params, {"max_step": 2})

    def test_continuous_defenses_run_full_validation(self) -> None:
        """Smoke test: every continuous defense runs through run_full_validation."""
        from trilemma_validator.defenses import get_defense
        from trilemma_validator.theorems import run_full_validation

        for name, kwargs in [
            ("smooth_nearest_safe", {"radius": 3.0}),
            ("kernel_smoothed", {"bandwidth": 2.5}),
            ("softly_constrained_projection", {"alpha": 2.0}),
        ]:
            with self.subTest(defense=name):
                defense = get_defense(name, **kwargs).build(
                    self.heatmap, self.tau
                )
                result = run_full_validation(self.heatmap, self.tau, defense)
                self.assertEqual(result.defense_name, name)
                # Theorem objects are all populated.
                self.assertIsNotNone(result.boundary)
                self.assertIsNotNone(result.eps_robust)
                self.assertIsNotNone(result.persistence)


# --------------------------------------------------------------------
# Test 5: bootstrap CI returns sensible values on random inputs.
# --------------------------------------------------------------------


class TestBootstrapCI(unittest.TestCase):
    """``bootstrap_ci`` must return (median, lo, hi) with lo <= median <= hi."""

    def test_monotone_quantiles_on_uniform(self) -> None:
        import numpy as np

        from trilemma_validator.uncertainty import bootstrap_ci

        rng = np.random.default_rng(42)
        values = rng.uniform(0.0, 10.0, size=500)
        median, lo, hi = bootstrap_ci(values, B=200, alpha=0.10, seed=0)
        self.assertFalse(np.isnan(median))
        self.assertLessEqual(lo, median + 1e-9)
        self.assertLessEqual(median, hi + 1e-9)
        # Max of uniform(0, 10) is close to 10.
        self.assertGreater(median, 8.0)

    def test_nan_population_returns_nan(self) -> None:
        import numpy as np

        from trilemma_validator.uncertainty import bootstrap_ci

        median, lo, hi = bootstrap_ci(np.array([], dtype=float), B=50)
        self.assertTrue(np.isnan(median))
        self.assertTrue(np.isnan(lo))
        self.assertTrue(np.isnan(hi))

    def test_mean_statistic(self) -> None:
        import numpy as np

        from trilemma_validator.uncertainty import bootstrap_ci

        rng = np.random.default_rng(1)
        values = rng.normal(5.0, 1.0, size=400)
        median, lo, hi = bootstrap_ci(
            values, B=200, alpha=0.10, seed=0, statistic="mean"
        )
        # Sample mean ~ 5.0 with bootstrap CI narrower than the data.
        self.assertLessEqual(lo, 5.0)
        self.assertGreaterEqual(hi, 5.0)
        self.assertLess(hi - lo, 1.0)  # CI narrower than the 1-sigma of the data

    def test_bootstrap_estimator_cis_shape(self) -> None:
        """End-to-end: bootstrap_estimator_cis returns dicts for L/K/ell/G."""
        from trilemma_validator.defenses import get_defense
        from trilemma_validator.synth import make
        from trilemma_validator.uncertainty import bootstrap_estimator_cis

        heatmap = make("mesa", grid_size=12, seed=0)
        defense = get_defense("bounded_step", max_step=2).build(heatmap, 0.5)
        out = bootstrap_estimator_cis(heatmap, defense, tau=0.5, B=50)
        for key in ("L", "K", "ell", "G"):
            self.assertIn(key, out)
            self.assertIn("population_size", out[key])
            self.assertIn("ci", out[key])
            median, lo, hi = out[key]["ci"]
            if out[key]["population_size"] > 0:
                # lo <= median <= hi for any non-empty population.
                self.assertTrue(
                    (lo != lo) or (lo <= median + 1e-9),
                    msg=f"{key}: lo={lo}, median={median}",
                )
                self.assertTrue(
                    (hi != hi) or (median <= hi + 1e-9),
                    msg=f"{key}: median={median}, hi={hi}",
                )


if __name__ == "__main__":
    unittest.main()
