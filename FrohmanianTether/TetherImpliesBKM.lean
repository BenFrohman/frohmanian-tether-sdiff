/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.ClayStatements

/-!
# The periodic tether bound implies Beale–Kato–Majda integrability (0.1.5)

On the periodic class `IsPeriodicSmoothSolutionOn` (classical smooth `ℤ³`-periodic solutions on
`[0, T)`), for one datum `u₀`:

* `PeriodicTetherBound ν u₀`: one ceiling `Y` for `‖ω(t)‖_∞` along every such solution from
  `u₀`, for every `T`; this is exactly the body of `ClayStatements.PeriodicTetherClosingBound`
  at `u₀` (`periodicTetherClosingBound_iff`).
* `PeriodicBKMIntegrability ν u₀`: for every horizon `T₀` one finite constant bounds the
  Beale–Kato–Majda integral `∫_{[0,T)} ‖ω(t)‖_∞ dt` (a lower Lebesgue integral in `ℝ≥0∞`, so no
  measurability side condition is hidden) along every such solution with `T ≤ T₀`.

**Theorem** (`periodicBKMIntegrability_of_periodicTetherBound`, kernel-checked): the first
implies the second, with the explicit constant `max Y 0 · max T₀ 0`. Corollary
(`periodicBKMIntegrability_of_periodicTetherClosingBound`): the closing bound gives BKM
integrability for every smooth divergence-free periodic datum.

The converse (BKM integrability ⇒ the time-uniform tether ceiling, for `ν > 0`) is **not**
proved here; it needs the Beale–Kato–Majda continuation theorem, uniqueness of classical
periodic solutions and long-time decay, none of which is formalized.
-/

open MeasureTheory NavierStokes3D
open scoped ENNReal

noncomputable section

namespace FrohmanianTether.TetherImpliesBKM

open FrohmanianTether.ClayStatements

/-- **Periodic tether bound for one datum**: one `‖ω‖_∞` ceiling `Y` along every classical smooth
periodic solution from `u₀` on every `[0, T)`. -/
@[expose] public def PeriodicTetherBound (ν : ℝ) (u₀ : VelocityField) : Prop :=
  ∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
    IsPeriodicSmoothSolutionOn ν T u₀ u p →
      ∀ t ∈ Set.Ico (0 : ℝ) T, vorticity_sup_norm (vorticity (u t)) ≤ Y

/-- **Periodic Beale–Kato–Majda integrability for one datum**: for every horizon `T₀` there is
one finite `C` with `∫_{[0,T)} ‖ω(t)‖_∞ dt ≤ C` along every classical smooth periodic solution
from `u₀` on `[0, T)`, `T ≤ T₀`. -/
@[expose] public def PeriodicBKMIntegrability (ν : ℝ) (u₀ : VelocityField) : Prop :=
  ∀ T₀ : ℝ, ∃ C : ℝ≥0∞, C < ⊤ ∧
    ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      T ≤ T₀ → IsPeriodicSmoothSolutionOn ν T u₀ u p →
        ∫⁻ t in Set.Ico (0 : ℝ) T, ENNReal.ofReal (vorticity_sup_norm (vorticity (u t))) ≤ C

/-- `PeriodicTetherClosingBound` is `PeriodicTetherBound` for every admissible periodic datum
(definitional). -/
public theorem periodicTetherClosingBound_iff (ν : ℝ) :
    PeriodicTetherClosingBound ν ↔
      ∀ u₀ : VelocityField, (∀ x, div u₀ x = 0) → ContDiff ℝ (⊤ : ℕ∞) u₀ → IsZ3Periodic u₀ →
        PeriodicTetherBound ν u₀ :=
  Iff.rfl

/-- **Theorem (tether ⇒ BKM).** The periodic tether bound implies periodic Beale–Kato–Majda
integrability, with `C = max Y 0 · max T₀ 0`. -/
public theorem periodicBKMIntegrability_of_periodicTetherBound {ν : ℝ} {u₀ : VelocityField}
    (h : PeriodicTetherBound ν u₀) : PeriodicBKMIntegrability ν u₀ := by
  obtain ⟨Y, hY⟩ := h
  intro T₀
  refine ⟨ENNReal.ofReal (max Y 0 * max T₀ 0), ENNReal.ofReal_lt_top, ?_⟩
  intro T u p hT hsol
  calc ∫⁻ t in Set.Ico (0 : ℝ) T, ENNReal.ofReal (vorticity_sup_norm (vorticity (u t)))
      ≤ ∫⁻ _ in Set.Ico (0 : ℝ) T, ENNReal.ofReal (max Y 0) :=
        setLIntegral_mono' measurableSet_Ico fun t ht =>
          ENNReal.ofReal_le_ofReal ((hY T u p hsol t ht).trans (le_max_left Y 0))
    _ = ENNReal.ofReal (max Y 0) * ENNReal.ofReal (T - 0) := by
        rw [setLIntegral_const, Real.volume_Ico]
    _ ≤ ENNReal.ofReal (max Y 0) * ENNReal.ofReal (max T₀ 0) := by
        gcongr
        rw [sub_zero]
        exact hT.trans (le_max_left T₀ 0)
    _ = ENNReal.ofReal (max Y 0 * max T₀ 0) :=
        (ENNReal.ofReal_mul (le_max_right Y 0)).symm

/-- **Corollary.** The periodic tether closing bound implies periodic BKM integrability for every
smooth divergence-free `ℤ³`-periodic datum. -/
public theorem periodicBKMIntegrability_of_periodicTetherClosingBound {ν : ℝ}
    (h : PeriodicTetherClosingBound ν) (u₀ : VelocityField) (hdiv : ∀ x, div u₀ x = 0)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) u₀) (hper : IsZ3Periodic u₀) :
    PeriodicBKMIntegrability ν u₀ :=
  periodicBKMIntegrability_of_periodicTetherBound
    ((periodicTetherClosingBound_iff ν).1 h u₀ hdiv hsm hper)

#print axioms periodicTetherClosingBound_iff
#print axioms periodicBKMIntegrability_of_periodicTetherBound
#print axioms periodicBKMIntegrability_of_periodicTetherClosingBound

end FrohmanianTether.TetherImpliesBKM
