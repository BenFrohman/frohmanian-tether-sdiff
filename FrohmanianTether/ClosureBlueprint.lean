/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.NS_Equations
public import FrohmanianTether.ArnoldGeometric
public import FrohmanianTether.SymplecticTether
public import FrohmanianTether.Uniqueness
public import FrohmanianTether.AnalyticPipeline
public import FrohmanianTether.TetheredLyapunov
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Analytic and geometric closure blueprint

Maps the Millennium logical trajectory onto the kernel-checked modules.

**Closed (no `sorryAx`):** Young absorption of the quartic factor `4`, the
Riccati phase-plane upper bound, and integrability of a continuous time
majorant on compact intervals.

**Gates transcribed from the paper:** Kato local existence, BKM smoothness,
uniqueness classification,
Picard existence of the majorant ODE.

`kappa` is `C_CZ(3) = (3/(8 π)) · 4 π = 3/2` from the strain kernel, not an axiom and not the stand-in `1`.
`IsSmoothAtTime` is `ContDiff ℝ (⊤ : ℕ∞)`, not a `constant`.
Admissible corrections use the real predicates C1–C3, not `True`.
-/

open FrohmanianTether AnalyticPipeline NavierStokes3D ArnoldGeometric
open MeasureTheory

namespace ClosureBlueprint

/-! ## Admissible phase-space corrections (real C1–C3) -/

/-- Pointwise integrand of the tether kernel (after `Π_u`):
`-κ ⟨δF, δG⟩ |ω|²`. The assembled object is `TetherKernel`. -/
public noncomputable def frohmanian_tether_integrand
    (ω : CoadjointOrbit) (δF δG : T3 → EuclideanSpace ℝ (Fin 3)) (x : T3) : ℝ :=
  -kappa * inner ℝ (δF x) (δG x) * ‖ω.val x‖ ^ 2

/-! ## Section 1 — closed analytic theorems -/

/-- Coefficient match after Young with `ε_abs = κ/4`. Residual `-(3/4)κ I₆`. -/
public theorem youngs_absorption_elimination
    (M I₄ I₆ phi_norm C_abs : ℝ)
    (hI6 : 0 ≤ I₆)
    (hYoung :
      4 * CalderonZygmundConstant3D * M * I₄ ≤
        (kappa / 4) * I₆ + C_abs * (M ^ 3 * phi_norm ^ ((3 : ℝ) / 2))) :
    4 * CalderonZygmundConstant3D * M * I₄ - kappa * I₆ ≤
      C_abs * (M ^ 3 * phi_norm ^ ((3 : ℝ) / 2)) -
        (3 / 4 : ℝ) * kappa * I₆ :=
  AnalyticPipeline.youngs_absorption_elimination M I₄ I₆ phi_norm C_abs hI6 hYoung

/-- Any differentiable trajectory majorized by `f(y) = y²(C − κ'' y)` stays
at or below `max(y(0), C/κ'')`. -/
public theorem comparison_ode_stability
    (C κ'' : ℝ) (hC : 0 < C) (hκ : 0 < κ'')
    (y : ℝ → ℝ)
    (hdiff : ∀ s ≥ (0 : ℝ), DifferentiableAt ℝ y s)
    (hy_dot : ∀ s ≥ (0 : ℝ), deriv y s ≤ C * (y s) ^ 2 - κ'' * (y s) ^ 3)
    (t : ℝ) (ht : 0 ≤ t) :
    y t ≤ max (y 0) (C / κ'') :=
  AnalyticPipeline.comparison_ode_stability C κ'' hC hκ y hdiff hy_dot t ht

/-- Equality solutions of the Riccati ODE inherit the same ceiling. -/
public theorem comparison_ode_bound_of_equality
    (C κ'' : ℝ) (hC : 0 < C) (hκ : 0 < κ'')
    (y : ℝ → ℝ)
    (hdiff : ∀ s ≥ (0 : ℝ), DifferentiableAt ℝ y s)
    (hode : ∀ s ≥ (0 : ℝ), deriv y s = C * (y s) ^ 2 - κ'' * (y s) ^ 3)
    (t : ℝ) (ht : 0 ≤ t) :
    y t ≤ max (y 0) (C / κ'') :=
  comparison_ode_stability C κ'' hC hκ y hdiff (fun s hs => le_of_eq (hode s hs)) t ht

/-! ## Section 2 — geometric and PDE theorems (paper statements, Lean types) -/

/-- Kato / Leray local existence on a short interval (equations on `[0, T]` only). Classical. -/
public theorem local_existence_kato
    (u₀ : VelocityField) (ν : ℝ)
    (h_smooth : ContDiff ℝ (⊤ : ℕ∞) u₀)
    (h_divfree : ∀ x, div u₀ x = 0)
    (h_finite : Integrable (fun x : T3 => ‖u₀ x‖ ^ 2))
    (hν : 0 < ν)
    (w : KatoLocalWitness u₀ ν) :
    ∃ T > (0 : ℝ), ∃ u : ℝ → VelocityField,
      (∀ t ∈ Set.Icc 0 T, ContDiff ℝ (⊤ : ℕ∞) (u t)) ∧
      u 0 = u₀ ∧
      IsPhysicalNSSolutionOn u T ∧
      ∃ p : ℝ → PressureField, NS_PDE_On u p ν T :=
  NavierStokes3D.local_existence u₀ ν h_smooth h_divfree h_finite hν w

/-- Beale–Kato–Majda: integrable `‖ω‖_∞` on compact time intervals ⇒ smoothness. -/
public theorem beale_kato_majda_criterion
    (u : TimeDependentVelocity) (p : TimeDependentPressure) (ν : ℝ)
    (hν : 0 < ν) (hNS : NS_PDE u p ν)
    (hloc : LocalExistenceTime u ν)
    (hcrit : BKMContinuationCriterion u ν)
    (h_bkm : PathBKMIntegrable u)
    (hbelow : SmoothBelowTstar u ν) :
    ∀ t ≥ (0 : ℝ), ContDiff ℝ (⊤ : ℕ∞) (u t) :=
  NavierStokes3D.beale_kato_majda u p ν hν hNS hloc hcrit h_bkm hbelow

/-- Density-form uniqueness: substitution of `α = -κ |ω|²` into the
projected pairing recovers `TetherKernel`. -/
public theorem uniqueness_of_kernel_density
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (α : CoadjointOrbit → T3 → ℝ)
    (h_repr : HasTetherKernelDensity B α)
    (hα : ∀ ω x, α ω x = canonicalTetherDensity ω x) :
    ∀ ω F G, B ω F G = TetherKernel ω F G :=
  FrohmanianTether.uniqueness_of_kernel_density B α h_repr hα

/-- Picard existence for `y' = C y² − κ'' y³`. Classical ODE. -/
public theorem comparison_ode_solution_existence
    (C κ'' y0 : ℝ) (hC : 0 < C) (hκ : 0 < κ'') (hy0 : 0 ≤ y0) :
    ∃ y : ℝ → ℝ,
      y 0 = y0 ∧
        (∀ t ≥ (0 : ℝ), DifferentiableAt ℝ y t) ∧
        (∀ t ≥ (0 : ℝ), deriv y t = C * (y t) ^ 2 - κ'' * (y t) ^ 3) := by
  obtain ⟨y, hsol⟩ :=
    TetheredLyapunov.comparison_ode_exists C κ'' y0 hC hκ hy0
  refine ⟨y, hsol.init, ?_, ?_⟩
  · intro t ht
    exact (hsol.deriv t ht).differentiableAt
  · intro t ht
    simpa [TetheredLyapunov.majorantField] using (hsol.deriv t ht).deriv

/-! ## Section 3 — regularity pipeline -/

/-- Continuous time majorant ⇒ integrable on `[0, T]` (no `∞` comparison on `ℝ`). -/
public theorem bkm_integrableOn_of_uniform_bound
    (Y : ℝ) (M : ℝ → ℝ)
    (hM : ∀ τ ≥ (0 : ℝ), M τ ≤ Y)
    (hcont : Continuous M)
    (T : ℝ) :
    IntegrableOn M (Set.Icc (0 : ℝ) T) :=
  AnalyticPipeline.bkm_integrableOn_of_uniform_bound Y M hM hcont T

/-- Uniform `‖ω(t)‖_∞` bound + continuity ⇒ global smoothness, via BKM. -/
public theorem bkm_regularity_pipeline
    (u : TimeDependentVelocity) (p : TimeDependentPressure) (ν : ℝ)
    (hν : 0 < ν) (hNS : NS_PDE u p ν)
    (Y : ℝ)
    (hbound : ∀ τ ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u τ)) ≤ Y)
    (hcont : Continuous fun τ : ℝ => vorticity_sup_norm (vorticity (u τ)))
    (hloc : LocalExistenceTime u ν)
    (hcrit : BKMContinuationCriterion u ν)
    (hbelow : SmoothBelowTstar u ν) :
    ∀ τ ≥ (0 : ℝ), ContDiff ℝ (⊤ : ℕ∞) (u τ) :=
  AnalyticPipeline.bkm_regularity_pipeline u p ν hν hNS Y hbound hcont hloc hcrit hbelow

/-- If a differentiable scalar majorant of `‖ω(t)‖_∞` obeys the Riccati
inequality `y' ≤ C y² − κ'' y³`, the closed comparison theorem supplies the
uniform ceiling `max(y 0, C/κ'')`, which is the exact input of
`bkm_regularity_pipeline`. No `True`, no `constant`, no `∫ < ∞` on `ℝ`. -/
public theorem regularity_from_riccati_majorant
    (u : TimeDependentVelocity) (p : TimeDependentPressure) (ν : ℝ)
    (hν : 0 < ν) (hNS : NS_PDE u p ν)
    (C κ'' : ℝ) (hC : 0 < C) (hκ : 0 < κ'')
    (y : ℝ → ℝ)
    (hdiff : ∀ s ≥ (0 : ℝ), DifferentiableAt ℝ y s)
    (hy_dot : ∀ s ≥ (0 : ℝ), deriv y s ≤ C * (y s) ^ 2 - κ'' * (y s) ^ 3)
    (hmaj : ∀ t ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u t)) ≤ y t)
    (hcont : Continuous fun τ : ℝ => vorticity_sup_norm (vorticity (u τ)))
    (hloc : LocalExistenceTime u ν)
    (hcrit : BKMContinuationCriterion u ν)
    (hbelow : SmoothBelowTstar u ν) :
    ∀ t ≥ (0 : ℝ), ContDiff ℝ (⊤ : ℕ∞) (u t) := by
  have hceil : ∀ τ ≥ (0 : ℝ), y τ ≤ max (y 0) (C / κ'') :=
    fun τ hτ => comparison_ode_stability C κ'' hC hκ y hdiff hy_dot τ hτ
  have hbound :
      ∀ τ ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u τ)) ≤ max (y 0) (C / κ'') :=
    fun τ hτ => (hmaj τ hτ).trans (hceil τ hτ)
  exact bkm_regularity_pipeline u p ν hν hNS (max (y 0) (C / κ'')) hbound hcont
    hloc hcrit hbelow

/-- **Continuation under assumed global existence** (NOT a regularity theorem).
Given a global physical solution `u` and `hTstar : TstarIsTop u ν` (the maximal existence time
is infinite, i.e. it *assumes* global existence), compact-interval smoothness below `T*`
upgrades to all `t ≥ 0`. Circular as a regularity claim; a bookkeeping lemma. (Restated Nov 2026:
the solution is an input, since a `KatoLocalWitness` no longer carries a global path.) -/
public theorem continuation_under_global_existence
    (u : ℝ → VelocityField) (ν : ℝ)
    (hTstar : TstarIsTop u ν)
    (hbelow : SmoothBelowTstar u ν) :
    ∀ t ≥ (0 : ℝ), ContDiff ℝ (⊤ : ℕ∞) (u t) :=
  NavierStokes3D.beale_kato_majda_scaffold_integrability_unused u ν hTstar hbelow

/-- **Conditional global regularity** (Frohmanian Symplectic Tether, conditional).
Inputs: the open local-solution bound `LocalTetherBound` (category (d)) and the classical
continuation statement `BKMGlobalContinuation` (category (b)), via
`TetheredLyapunov.conditional_regularity`. Not an unconditional Clay solution. -/
public theorem conditional_regularity_of_open_hyps
    (u₀ : VelocityField) (ν : ℝ)
    (w : KatoLocalWitness u₀ ν)
    (hcont : TetheredLyapunov.BKMGlobalContinuation u₀ ν)
    (hRiccati : TetheredLyapunov.LocalTetherBound u₀ ν) :
    ∃ (u : ℝ → VelocityField) (p : ℝ → PressureField),
      NS_PDE u p ν ∧
      u 0 = u₀ ∧
      (∀ t ≥ (0 : ℝ), ContDiff ℝ (⊤ : ℕ∞) (u t)) ∧
      (∀ t ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u t)) ≥ 0) ∧
      (∀ t ≥ (0 : ℝ), ∀ x, div (u t) x = 0) := by
  obtain ⟨u, p, hNS, hu0, hsm, -, hnn, hdiv⟩ :=
    TetheredLyapunov.conditional_regularity u₀ ν w hcont hRiccati
  exact ⟨u, p, hNS, hu0, hsm, hnn, hdiv⟩

/-! ## Section 4 — named geometric / Lyapunov skeletons (real types) -/

/-- Quartic Lyapunov product-rule cancellation is the Young identity of §1. -/
public theorem lyapunov_quartic_cancellation_skeleton
    (M I₄ I₆ phi_norm C_abs : ℝ)
    (hI6 : 0 ≤ I₆)
    (hYoung :
      4 * CalderonZygmundConstant3D * M * I₄ ≤
        (kappa / 4) * I₆ + C_abs * (M ^ 3 * phi_norm ^ ((3 : ℝ) / 2))) :
    4 * CalderonZygmundConstant3D * M * I₄ - kappa * I₆ ≤
      C_abs * (M ^ 3 * phi_norm ^ ((3 : ℝ) / 2)) -
        (3 / 4 : ℝ) * kappa * I₆ :=
  youngs_absorption_elimination M I₄ I₆ phi_norm C_abs hI6 hYoung

/-! ## Type composition (Kato → Young/Riccati → IntegrableOn → BKM)

Each step’s output type is the next step’s input type. Closed lemmas are
invoked as real terms; the remaining geometric gate (existence of a Riccati
majorant of `‖ω‖_∞`) is the named hypothesis `RiccatiMajorantExists`, not proved here.

`constant` placeholders, `axiom kappa`, `∀ x, True` stretching bounds, and
`∫ < ∞` comparisons on `ℝ` are not used.
-/

/-- **Riccati majorant hypothesis** (open for general data). Along every physically admissible
solution of the unmodified equations from `u₀`, `M(t) = ‖ω(t)‖_∞` is continuous and is dominated by a
differentiable `y` obeying `y' ≤ C y² − κ'' y³` with `C, κ'' > 0`. A named, dischargeable
`Prop`; it is not proved for general data. -/
@[expose] public def RiccatiMajorantExists (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∀ u : ℝ → VelocityField, ∀ p : ℝ → PressureField,
    NS_PDE u p ν → u 0 = u₀ → IsPhysicalNSSolution u →
      ∃ (C κ'' : ℝ), 0 < C ∧ 0 < κ'' ∧
        ∃ y : ℝ → ℝ,
          (∀ s ≥ (0 : ℝ), DifferentiableAt ℝ y s) ∧
          (∀ s ≥ (0 : ℝ), deriv y s ≤ C * (y s) ^ 2 - κ'' * (y s) ^ 3) ∧
          (∀ t ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u t)) ≤ y t) ∧
          Continuous (fun τ : ℝ => vorticity_sup_norm (vorticity (u τ)))

/-- Sequential composition of the Millennium path, along a GIVEN global physical solution.

1. A global physical solution `u` from `u₀` is an input (a `KatoLocalWitness` only supplies a
   solution on its own interval; global existence is not derived here).
2. `youngs_absorption_elimination` is the closed coefficient match
   (`4 C_CZ(3)` absorbed, residual `-(3/4)κ I₆`) that forces the Riccati
   field `y' ≤ C y² − κ'' y³`.
3. A differentiable majorant of `M(t) = ‖ω(u t)‖_∞` obeying that field is
   the named hypothesis `RiccatiMajorantExists`; it is not proved here.
4. `regularity_from_riccati_majorant` consumes it: comparison ceiling →
   `IntegrableOn M (Icc 0 T)` → BKM `ContDiff ℝ (⊤ : ℕ∞) (u t)`.
-/
public theorem type_composition_sequence
    (u₀ : VelocityField) (ν : ℝ)
    (hν : 0 < ν)
    (u : ℝ → VelocityField) (p : ℝ → PressureField)
    (hNS : NS_PDE u p ν) (hu0 : u 0 = u₀) (hphys : IsPhysicalNSSolution u)
    (hsm0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiff ℝ (⊤ : ℕ∞) (u t))
    (hRiccati : RiccatiMajorantExists u₀ ν)
    (hcrit : TetheredLyapunov.BKMContinuationCriterionFor u₀ ν)
    (hbelow : TetheredLyapunov.SmoothBelowTstarFor u₀ ν) :
    ∀ t ≥ (0 : ℝ), ContDiff ℝ (⊤ : ℕ∞) (u t) := by
  have _young :
      ∀ M I₄ I₆ phi_norm C_abs : ℝ, 0 ≤ I₆ →
        4 * CalderonZygmundConstant3D * M * I₄ ≤
            (kappa / 4) * I₆ + C_abs * (M ^ 3 * phi_norm ^ ((3 : ℝ) / 2)) →
          4 * CalderonZygmundConstant3D * M * I₄ - kappa * I₆ ≤
            C_abs * (M ^ 3 * phi_norm ^ ((3 : ℝ) / 2)) -
              (3 / 4 : ℝ) * kappa * I₆ :=
    fun M I₄ I₆ phi_norm C_abs hI6 hY =>
      youngs_absorption_elimination M I₄ I₆ phi_norm C_abs hI6 hY
  obtain ⟨C, κ'', hC, hκ, y, hdiff, hy_dot, hmaj, hcont⟩ :=
    hRiccati u p hNS hu0 hphys
  have hloc : LocalExistenceTime u ν := by
    unfold LocalExistenceTime
    exact Tstar_pos_of_exists_smooth_solution (u 0) ν
      ⟨1, one_pos, u, hsm0, rfl, hphys.on 1, p, hNS.on 1⟩
  exact regularity_from_riccati_majorant u p ν hν hNS C κ'' hC hκ y hdiff hy_dot
    hmaj hcont hloc (hcrit u p hNS hu0 hphys) (hbelow u p hNS hu0 hphys)

end ClosureBlueprint
