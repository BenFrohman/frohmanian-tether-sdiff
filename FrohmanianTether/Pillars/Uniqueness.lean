/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import NSTorusUniqueness
import FrohmanianTether.ClayStatements

/-!
# Uniqueness pillar: classical periodic solutions are unique (proved)

**Source.** `NSTorus.IsPeriodicSmoothSolutionOn.eq_of_same_data` from
`BenFrohman/periodic-navier-stokes-smooth-uniqueness` at commit
`de92662d45e8a0f47ce0c196f6dbcfe44ddb4b3b` (Lake dependency `NSTorusUniqueness`; same toolchain
`leanprover/lean4:v4.30.0-rc1` and Mathlib `0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`).
Energy method and Grönwall (`le_gronwallBound_of_liminf_deriv_right_le`); standard axioms only.

**Definitions match by `rfl`.** The mirrored definitions of the uniqueness repository are checked
against the compiled sdiff definitions (`convective`, `laplacian`, `div`, `pressureGradient`,
`latticeVec`, `unitCube`, `IsZ3Periodic`, `IsPeriodicSmoothSolutionOn`). So the theorem applies to
the sdiff class `ClayStatements.IsPeriodicSmoothSolutionOn` (classical solutions on `[0, T)`) with
no conversion.

**What this gives.**
* `periodicSmoothSolutionOn_unique`: two classical periodic solutions on `[0, T)` with the same
  initial velocity have the same velocity on `[0, T)` (for every `ν ≥ 0`), the same pressure
  gradient, and pressures differing by a function of `t` only.
* `isPeriodicSmoothSolutionOn_of_global` and `periodicSmoothSolution_unique`: the same for the
  global class `IsPeriodicSmoothSolution` of Statement (B), on `[0, ∞)`.
* `Clay_B_exact_unique` (Statement (B) with uniqueness of the velocity) is equivalent to
  `Clay_B_exact` (`clay_B_exact_unique_iff`), and the Main Theorem is restated with the uniqueness
  conclusion in `clay_B_exact_unique_of_periodic_tether_bound`.

**What this does not give.** It discharges no hypothesis of the Main Theorem: the hypothesis
`PeriodicBKMContinuation` (classical BKM continuation) and the open `PeriodicTetherClosingBound`
are unchanged. The Beale–Kato–Majda criterion and Kato local existence proved in
`BenFrohman/periodic-ns-classical-continuation` are stated over a different copy of the
`NavierStokes3D` definitions (package `FeffermanClayNS`), which cannot be imported next to this
library; see `CERTIFICATE.md`, section "Pillars". Nothing here proves Statement (B).
-/

open NavierStokes3D FrohmanianTether.ClayStatements

namespace FrohmanianTether.Pillars

/-! ### The mirrored definitions are the sdiff definitions (`rfl`) -/

theorem velocityField_eq_sdiff : NSTorus.VelocityField = NavierStokes3D.VelocityField := rfl
theorem convective_eq_sdiff : NSTorus.convective = NavierStokes3D.convective := rfl
theorem laplacian_eq_sdiff : NSTorus.laplacian = NavierStokes3D.laplacian := rfl
theorem div_eq_sdiff : NSTorus.div = NavierStokes3D.div := rfl
theorem pressureGradient_eq_sdiff :
    NSTorus.pressureGradient = NavierStokes3D.pressureGradient := rfl
theorem latticeVec_eq_sdiff : NSTorus.latticeVec = ClayStatements.latticeVec := rfl
theorem unitCube_eq_sdiff : NSTorus.unitCube = ClayStatements.unitCube := rfl
theorem isZ3Periodic_eq_sdiff {α : Type*} :
    @NSTorus.IsZ3Periodic α = @ClayStatements.IsZ3Periodic α := rfl
theorem isPeriodicSmoothSolutionOn_eq_sdiff :
    NSTorus.IsPeriodicSmoothSolutionOn = ClayStatements.IsPeriodicSmoothSolutionOn := rfl

/-! ### Uniqueness on `[0, T)` for the sdiff class -/

/-- **Proved (pillar).** Two classical `ℤ³`-periodic solutions on `[0, T)` with the same initial
velocity have the same velocity on `[0, T)`. -/
theorem periodicSmoothSolutionOn_unique {ν T : ℝ} {u₀ : VelocityField}
    {u v : TimeDependentVelocity} {p q : TimeDependentPressure} (hν : 0 ≤ ν)
    (hu : IsPeriodicSmoothSolutionOn ν T u₀ u p) (hv : IsPeriodicSmoothSolutionOn ν T u₀ v q) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, u t = v t :=
  NSTorus.IsPeriodicSmoothSolutionOn.eq_of_same_data hν hu hv

/-- **Proved (pillar).** Same initial velocity gives the same pressure gradient on `[0, T)`. -/
theorem periodicSmoothSolutionOn_pressureGradient_unique {ν T : ℝ} {u₀ : VelocityField}
    {u v : TimeDependentVelocity} {p q : TimeDependentPressure} (hν : 0 ≤ ν)
    (hu : IsPeriodicSmoothSolutionOn ν T u₀ u p) (hv : IsPeriodicSmoothSolutionOn ν T u₀ v q) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, pressureGradient (p t) x = pressureGradient (q t) x :=
  NSTorus.IsPeriodicSmoothSolutionOn.pressureGradient_eq_of_same_data hν hu hv

/-- **Proved (pillar).** Same initial velocity: the pressures differ by a function of `t` only. -/
theorem periodicSmoothSolutionOn_pressure_sub_const {ν T : ℝ} {u₀ : VelocityField}
    {u v : TimeDependentVelocity} {p q : TimeDependentPressure} (hν : 0 ≤ ν)
    (hu : IsPeriodicSmoothSolutionOn ν T u₀ u p) (hv : IsPeriodicSmoothSolutionOn ν T u₀ v q) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x y, p t x - q t x = p t y - q t y :=
  NSTorus.IsPeriodicSmoothSolutionOn.pressure_sub_const_of_same_data hν hu hv

/-! ### Global solutions (Statement (B) class) -/

/-- **Proved.** A global periodic smooth solution (zero force) restricts to a classical solution
on every `[0, T)`. -/
theorem isPeriodicSmoothSolutionOn_of_global {ν : ℝ} {u₀ : VelocityField}
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (h : IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p) (T : ℝ) :
    IsPeriodicSmoothSolutionOn ν T u₀ u p := by
  obtain ⟨hu, hp, hNS, h0, hper⟩ := h
  refine ⟨hu.mono (Set.prod_mono Set.Ico_subset_Ici_self subset_rfl),
    hp.mono (Set.prod_mono Set.Ico_subset_Ici_self subset_rfl), fun t ht x => ?_, h0,
    fun t ht => hper t ht.1⟩
  obtain ⟨h1, h2⟩ := hNS t ht.1 x
  exact ⟨by simpa only [add_zero] using h1, h2⟩

/-- **Proved (pillar).** Two global periodic smooth solutions (zero force) with the same initial
velocity have the same velocity for all `t ≥ 0`. -/
theorem periodicSmoothSolution_unique {ν : ℝ} {u₀ : VelocityField}
    {u v : TimeDependentVelocity} {p q : TimeDependentPressure} (hν : 0 ≤ ν)
    (hu : IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p)
    (hv : IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) v q) :
    ∀ t ≥ (0 : ℝ), u t = v t := fun t ht =>
  periodicSmoothSolutionOn_unique hν (isPeriodicSmoothSolutionOn_of_global hu (t + 1))
    (isPeriodicSmoothSolutionOn_of_global hv (t + 1)) t ⟨ht, by linarith⟩

/-- Statement (B) together with uniqueness of the velocity among global periodic smooth
solutions (a `Prop`; OPEN, like `Clay_B_exact`). -/
def Clay_B_exact_unique : Prop :=
  ∀ (ν : ℝ) (u₀ : VelocityField),
    0 < ν →
    ContDiff ℝ (⊤ : ℕ∞) u₀ →
    (∀ x, div u₀ x = 0) →
    IsZ3Periodic u₀ →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p ∧
      ∀ (v : TimeDependentVelocity) (q : TimeDependentPressure),
        IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) v q → ∀ t ≥ (0 : ℝ), v t = u t

/-- **Proved (pillar).** With uniqueness proved, Statement (B) with uniqueness is equivalent to
`Clay_B_exact`. (Both sides remain OPEN.) -/
theorem clay_B_exact_unique_iff : Clay_B_exact_unique ↔ Clay_B_exact := by
  constructor
  · intro h ν u₀ hν hs hd hp
    obtain ⟨u, p, hsol, -⟩ := h ν u₀ hν hs hd hp
    exact ⟨u, p, hsol⟩
  · intro h ν u₀ hν hs hd hp
    obtain ⟨u, p, hsol⟩ := h ν u₀ hν hs hd hp
    exact ⟨u, p, hsol, fun v q hv t ht => periodicSmoothSolution_unique hν.le hv hsol t ht⟩

/-- **Main Theorem with the uniqueness pillar (proved; CONDITIONAL).** The same two hypotheses as
`clay_B_exact_of_periodic_tether_bound`: the OPEN periodic tether closing bound and the classical
(not formalized here) periodic BKM continuation. The conclusion adds uniqueness of the global
velocity, which is proved unconditionally (`periodicSmoothSolution_unique`). This is not a proof
of Statement (B). -/
theorem clay_B_exact_unique_of_periodic_tether_bound
    (hclose : ∀ ν > (0 : ℝ), PeriodicTetherClosingBound ν)
    (hBKM : ∀ ν > (0 : ℝ), PeriodicBKMContinuation ν) : Clay_B_exact_unique :=
  clay_B_exact_unique_iff.2 (clay_B_exact_of_periodic_tether_bound hclose hBKM)

end FrohmanianTether.Pillars
