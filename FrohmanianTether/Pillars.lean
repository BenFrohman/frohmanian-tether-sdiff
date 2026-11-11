/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import FrohmanianTether.Pillars.Uniqueness

/-!
# Proved classical pillars wired into `frohmanian-tether-sdiff`

Root of the library `FrohmanianTetherPillars`. These files are ordinary (non-`module`) Lean
files, because they import proved companion repositories that are not written in the module
system; a `module` file may only import modules.

* `FrohmanianTether.Pillars.Uniqueness`: uniqueness of classical `ℤ³`-periodic solutions
  (`BenFrohman/periodic-navier-stokes-smooth-uniqueness` @ `de92662`), transported to the sdiff
  classes `IsPeriodicSmoothSolutionOn` and `IsPeriodicSmoothSolution` by `rfl`.
-/
