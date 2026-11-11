/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import FrohmanianTether.Pillars.Uniqueness
import FrohmanianTether.Pillars.BKMContinuation

/-!
# Proved classical pillars wired into `frohmanian-tether-sdiff`

Root of the library `FrohmanianTetherPillars`. These files are ordinary (non-`module`) Lean
files, because they import proved companion repositories that are not written in the module
system; a `module` file may only import modules.

* `FrohmanianTether.Pillars.Uniqueness`: uniqueness of classical `ℤ³`-periodic solutions
  (`BenFrohman/periodic-navier-stokes-smooth-uniqueness` @ `de92662`), transported to the sdiff
  classes `IsPeriodicSmoothSolutionOn` and `IsPeriodicSmoothSolution` by `rfl`.
* `FrohmanianTether.Pillars.BKMContinuation`: the classical periodic BKM continuation
  (`PeriodicBKMContinuation ν`, `ν > 0`) proved from Kato local existence, the maximal solution and
  the Beale–Kato–Majda criterion of `BenFrohman/periodic-ns-classical-continuation` @ `502ff17`
  (vendored, namespace-renamed, in `vendor/BKMPillar`). Headline:
  `clay_B_exact_unique_of_periodic_tether_closing_bound`, conditional only on the OPEN
  `PeriodicTetherClosingBound`.
-/
