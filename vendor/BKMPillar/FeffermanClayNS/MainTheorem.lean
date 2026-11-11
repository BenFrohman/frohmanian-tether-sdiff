/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
module

public import BKMPillar.FeffermanClayNS.HighSetDepletionAndBKM

/-!
# Main Theorem (reduction), following Mathlib 4 naming & style conventions
-/

@[expose] public section

namespace FeffermanClayNS

/-- **Single named open estimate (`HasDirectionCurvatureCoercivity` / `DirectionCurvatureBound`).**
High-set direction-curvature / cubic depletion bound `M' ≤ C_CZ M² − κ'' M³` along every local
periodic smooth Navier–Stokes solution. **OPEN conjecture** (not proved). -/
abbrev HasDirectionCurvatureCoercivity (ν : ℝ) : Prop := PeriodicDirectionDepletionBound ν

/-- Alias in the headline statement. -/
abbrev DirectionCurvatureBound (ν : ℝ) : Prop := HasDirectionCurvatureCoercivity ν

/-- Dot-notation projection: `h.periodicTetherClosingBound` extracts the uniform vorticity ceiling
`Y = max ‖ω₀‖_∞ (C_CZ / κ'')` from `HasDirectionCurvatureCoercivity ν`. -/
theorem HasDirectionCurvatureCoercivity.periodicTetherClosingBound {ν : ℝ}
    (h : HasDirectionCurvatureCoercivity ν) : PeriodicTetherClosingBound ν :=
  periodicTetherClosingBound_of_directionDepletion ν h

/-- Dot-notation reduction: `h.clay_B_exact hBKM` deduces `Clay_B_exact ν` from
`h : HasDirectionCurvatureCoercivity ν` and `hBKM : PeriodicBKMContinuation ν`. -/
theorem HasDirectionCurvatureCoercivity.clay_B_exact {ν : ℝ}
    (h : HasDirectionCurvatureCoercivity ν) (hBKM : PeriodicBKMContinuation ν) :
    Clay_B_exact ν :=
  clay_B_exact_of_torus_direction_depletion ν h hBKM

/-- **Main Theorem (`clay_B_exact_of_hasDirectionCurvatureCoercivity`, Mathlib `conclusion_of_hypothesis` style).** -/
theorem clay_B_exact_of_hasDirectionCurvatureCoercivity (ν : ℝ) (_hν : 0 < ν)
    (hBKM : PeriodicBKMContinuation ν) (hDCB : HasDirectionCurvatureCoercivity ν) :
    Clay_B_exact ν :=
  hDCB.clay_B_exact hBKM

/-- **Headline Main Theorem (`clay_reduces_to_direction_curvature_bound`).**
Unconditional Lean reduction theorem: for all `ν > 0`, given `PeriodicBKMContinuation ν`,
`DirectionCurvatureBound ν → Clay_B_exact ν`. Converse is NOT proved. -/
theorem clay_reduces_to_direction_curvature_bound :
    ∀ ν : ℝ, 0 < ν → PeriodicBKMContinuation ν →
      (DirectionCurvatureBound ν → Clay_B_exact ν) :=
  clay_B_exact_of_hasDirectionCurvatureCoercivity

end FeffermanClayNS

end
