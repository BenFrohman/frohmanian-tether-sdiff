/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import Scratch.KatoMaximal
import Scratch.LogBoundLocal

/-!
 # Classical BKM continuation on ℝ³ from the Kato maximal solution

`KatoMaximal.katoMaximalSolution_of_feffermanDecay` proves
`R3BKM.KatoMaximalSolution ν u₀` for `ν > 0` and smooth, divergence-free,
Fefferman-decaying data, and `LogBoundLocal.bkmLogInequality` proves
`R3BKM.BKMLogInequality`. Feeding both into
`R3BKM.r3BKMContinuation_of_kato_of_log` gives `R3BKMContinuation ν` for
every `ν > 0`.

`R3BKMContinuation ν` is a *conditional continuation* statement: if one
ceiling `Y` bounds `‖ω‖_∞` along every local Fefferman-class solution from
`u₀`, then `u₀` has a global solution. It does not assert that such a
ceiling exists, and it is not a regularity theorem for Navier–Stokes.

`clay_A_fefferman_of_rate` is the remaining conditional form of
`R3BKM.clay_A_fefferman_of_rate_of_kato_of_log`: its only hypothesis is the
tether rate `FrohmanianTetherRateSmooth u₀ ν` for all admissible `ν, u₀`,
which is not proved in this repository.
-/

open NavierStokes3D FrohmanianTether RepairedTether R3BKM
open scoped ContDiff

noncomputable section
namespace KatoContinuation

/-- `R3BKMContinuation ν` for every `ν > 0`, with both named inputs
(`KatoMaximalSolution`, `BKMLogInequality`) discharged. Conditional
continuation only: a uniform vorticity ceiling is still a hypothesis inside
`R3BKMContinuationAt`. -/
theorem r3BKMContinuation_of_pos {ν : ℝ} (hν : 0 < ν) : R3BKMContinuation ν :=
  r3BKMContinuation_of_kato_of_log LogBoundLocal.bkmLogInequality
    fun _u₀ hs hd hdec =>
      KatoMaximal.katoMaximalSolution_of_feffermanDecay hs hdec hν hd

/-- **Conditional.** `Clay_A_Fefferman` from the tether rate
`FrohmanianTetherRateSmooth` alone. The rate hypothesis is NOT proved in this
repository, so this does not establish `Clay_A_Fefferman`. -/
theorem clay_A_fefferman_of_rate
    (hrate : ∀ ν > (0 : ℝ), ∀ u₀ : VelocityField, ContDiff ℝ ∞ u₀ →
      (∀ x, div u₀ x = 0) → FeffermanDecay u₀ → FrohmanianTetherRateSmooth u₀ ν) :
    Clay_A_Fefferman :=
  clay_A_fefferman_of_rate_of_kato_of_log hrate LogBoundLocal.bkmLogInequality
    fun _ν hν _u₀ hs hd hdec =>
      KatoMaximal.katoMaximalSolution_of_feffermanDecay hs hdec hν hd

end KatoContinuation

#print axioms KatoContinuation.r3BKMContinuation_of_pos
#print axioms KatoContinuation.clay_A_fefferman_of_rate
