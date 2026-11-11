/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import FrohmanianTether.ExplicitFlows
import FrohmanianTether.TetherDefinitionAudit

/-! # `FrohmanianTetherRate` is vacuous on nonzero periodic data
`FrohmanianTetherRate` quantifies over `IsPhysicalNSSolution` paths, which require
`Integrable (‖u t‖²)` on ℝ³. A continuous nonzero `ℤ³`-periodic datum is never `L²(ℝ³)`, so no
such path starts there and the Prop holds *vacuously* for every periodic datum. Hence
"FrohmanianTetherRate holds on 𝕋³" is provable and carries no information about
`PeriodicTetherClosingBound` / `Clay_B_exact`. -/

open MeasureTheory NavierStokes3D FrohmanianTether

namespace TetherRatePeriodicVacuity

theorem frohmanianTetherRate_of_periodic_ne_zero {u₀ : VelocityField} (ν : ℝ)
    (hc : Continuous u₀) (hp : FrohmanianTether.ClayStatements.IsZ3Periodic u₀) (hne : u₀ ≠ 0) :
    FrohmanianTetherRate u₀ ν := by
  intro u p _hν _hNS hu0 hphys
  exact absurd (hu0 ▸ hphys.2.2.1 0 le_rfl)
    (ExplicitFlows.not_integrable_sq_of_periodic hc hp hne)

/-- Every continuous `ℤ³`-periodic datum satisfies `FrohmanianTetherRate` (zero datum: real
witness; nonzero datum: vacuously). -/
theorem frohmanianTetherRate_of_periodic {u₀ : VelocityField} (ν : ℝ)
    (hc : Continuous u₀) (hp : FrohmanianTether.ClayStatements.IsZ3Periodic u₀) :
    FrohmanianTetherRate u₀ ν := by
  by_cases h : u₀ = 0
  · subst h; exact FrohmanianTether.ClayStatements.frohmanianTetherRate_zero ν
  · exact frohmanianTetherRate_of_periodic_ne_zero ν hc hp h

/-- Same for the `FrohmanianTetherBound` companion. -/
theorem frohmanianTetherBound_of_periodic_ne_zero {u₀ : VelocityField} (ν : ℝ)
    (hc : Continuous u₀) (hp : FrohmanianTether.ClayStatements.IsZ3Periodic u₀) (hne : u₀ ≠ 0) :
    FrohmanianTetherBound u₀ ν := by
  intro u p _hNS hu0 hphys
  exact absurd (hu0 ▸ hphys.2.2.1 0 le_rfl)
    (ExplicitFlows.not_integrable_sq_of_periodic hc hp hne)

end TetherRatePeriodicVacuity

#print axioms TetherRatePeriodicVacuity.frohmanianTetherRate_of_periodic_ne_zero
#print axioms TetherRatePeriodicVacuity.frohmanianTetherRate_of_periodic
#print axioms TetherRatePeriodicVacuity.frohmanianTetherBound_of_periodic_ne_zero
