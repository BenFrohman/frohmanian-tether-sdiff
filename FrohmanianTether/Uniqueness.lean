/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import FrohmanianTether.SymplecticTether
public import FrohmanianTether.Assumptions
public import FrohmanianTether.TetherNondegeneracy

/-!
# Canonicity of the tether kernel

Uniqueness ("canonicity") statements for `TetherKernel` inside a restricted class of kernels,
the kernel conditions proved or refuted for `TetherKernel` itself (nondegeneracy, polarization on
functionals with gradients, saturation, `h_proj`, the canonical density; refutations of
unrestricted polarization, of `Step1Hyp` and of the pointwise weight hypothesis), and the
vacuity of the former antisymmetric clause. These are statements about kernels; they say nothing
about regularity of Navier–Stokes solutions.
-/


namespace FrohmanianTether

open FrohmanianTether
open ArnoldGeometric
open NavierStokes3D
open MeasureTheory ForMathlib TetherNondegeneracy
open scoped InnerProductSpace


-- Step 2 is not a theorem from antisymmetry of an arbitrary `B`. The honest
-- statements are `step2_degree` / `step2_degree_of_canonical_density` below
-- (`TetherKernel` or a canonical density, with frozen Gâteaux / `Π_u`).
-- `uniqueness_of_minimal_tether` does not use either; it polarizes.

-- Step 5 for an arbitrary antisymmetric `B` is not a theorem from C2–C3
-- alone. See `step5_higher_order` (`TetherKernel` via `step2_degree`).

/-- The correction is given by a scalar kernel density against the projected
pairing. The Frohmanian kernel `-κ ‖ω‖² ∫ ⟨Π_u δF, Π_u δG⟩` is the case of the
spatially constant density `α ω x = -κ ‖ω‖²` (global enstrophy). -/
@[expose] public def HasTetherKernelDensity
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (α : CoadjointOrbit → T3 → ℝ) : Prop :=
  ∀ (ω : CoadjointOrbit) (F G : Functional),
    B ω F G =
      ∫ x,
        α ω x *
          inner ℝ
            (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x)
            (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative G ω) x)
        ∂volume

/-- Canonical density of `TetherKernel`: the spatially constant `-κ ‖ω‖²`
(`‖ω‖² = Enstrophy ω`, the global enstrophy; it does not depend on `x`). -/
public noncomputable def canonicalTetherDensity (ω : CoadjointOrbit) (_x : T3) : ℝ :=
  -kappa * Enstrophy ω

/-- If `B` is defined by a density `α` and `α = -κ ‖ω‖²`, then `B = TetherKernel`
by substitution and `integral_const_mul`. -/
public theorem uniqueness_of_kernel_density
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (α : CoadjointOrbit → T3 → ℝ)
    (h_repr : HasTetherKernelDensity B α)
    (hα : ∀ ω x, α ω x = canonicalTetherDensity ω x) :
    ∀ (ω : CoadjointOrbit) (F G : Functional), B ω F G = TetherKernel ω F G := by
  intro ω F G
  rw [h_repr ω F G]
  simp only [hα, canonicalTetherDensity]
  rw [integral_const_mul (μ := volume)]
  rfl

/-- Function-equality form: a density equal to `canonicalTetherDensity` as
functions yields `B = TetherKernel` as functions. -/
public theorem uniqueness_of_kernel_density_fun
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (α : CoadjointOrbit → T3 → ℝ)
    (h_repr : HasTetherKernelDensity B α)
    (hα : α = canonicalTetherDensity) :
    B = TetherKernel := by
  funext ω
  funext F
  funext G
  exact uniqueness_of_kernel_density B α h_repr (fun _ω x => by rw [hα]) ω F G

/-- `TetherKernel` is exactly the pairing against the canonical density. -/
public theorem tetherKernel_has_canonical_density :
    HasTetherKernelDensity TetherKernel canonicalTetherDensity := by
  intro ω F G
  unfold TetherKernel canonicalTetherDensity
  rw [integral_const_mul (μ := volume)]

/-- Reconstruction 2.3.1 in substitution form: a correction with the
canonical density is homogeneous of degree two in `ω` once the Gâteaux
slots are frozen (paper: `δF` is a tangent vector, independent of scaling
the base vorticity). -/
public theorem step2_degree_of_canonical_density
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (α : CoadjointOrbit → T3 → ℝ)
    (h_repr : HasTetherKernelDensity B α)
    (hα : ∀ ω x, α ω x = canonicalTetherDensity ω x)
    (F G : Functional) (ω : CoadjointOrbit) (c : ℝ)
    (hFD_F : FunctionalDerivative F
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ =
      FunctionalDerivative F ω)
    (hFD_G : FunctionalDerivative G
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ =
      FunctionalDerivative G ω)
    (hPi : Pi_u (velocity_from_vorticity
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩) =
      Pi_u (velocity_from_vorticity ω)) :
    B ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ F G =
      c ^ 2 * B ω F G := by
  have hB := uniqueness_of_kernel_density B α h_repr hα
  set ωc : CoadjointOrbit :=
    ⟨fun x => c • ω.val x, fun x => by
      rw [div_smul, ω.property x, mul_zero]⟩
  have hTc : B ωc F G = TetherKernel ωc F G := hB ωc F G
  have hT : B ω F G = TetherKernel ω F G := hB ω F G
  have hE : Enstrophy ωc = c ^ 2 * Enstrophy ω := by
    unfold Enstrophy Casimir
    simp only [ωc, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [integral_const_mul (μ := volume)]
  rw [hTc, hT]
  unfold TetherKernel
  rw [hE, hFD_F, hFD_G, hPi]
  ring

/-- `Π_u` is invariant under nonzero rescaling of `u`: the projection onto the
`L²`-orthogonal complement of `u` depends only on the line spanned by `u`.
(If `∫ ‖u‖² = 0` both coefficients are `0` by Lean's `x / 0 = 0` convention.) -/
public theorem Pi_u_smul_of_ne_zero (c : ℝ) (hc : c ≠ 0) (u : VelocityField) :
    Pi_u (fun x => c • u x) = Pi_u u := by
  funext v x
  simp only [Pi_u, ArnoldGeometric.pairing, inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_const_mul, integral_const_mul, smul_smul]
  congr 2
  by_cases hN : (∫ y, ‖u y‖ ^ 2 ∂volume) = 0
  · simp [hN]
  · field_simp

/-- The `hPi` hypothesis of `step2_degree` holds automatically for `c ≠ 0`
(Biot–Savart is linear, `Π_u` is scale invariant). -/
public theorem hPi_of_ne_zero (ω : CoadjointOrbit) (c : ℝ) (hc : c ≠ 0) :
    Pi_u (velocity_from_vorticity
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩) =
      Pi_u (velocity_from_vorticity ω) := by
  simp only [velocity_from_vorticity_eq_BiotSavart]
  rw [BiotSavart_smul]
  exact Pi_u_smul_of_ne_zero c hc _

/-- Step 2 for `TetherKernel`: quadratic in `ω` (weight `|ω|²`) once Gâteaux
slots and `Π_u` are frozen. Not the false claim that every antisymmetric
`B` is homogeneous of degree two. -/
public theorem step2_degree
    (F G : Functional) (ω : CoadjointOrbit) (c : ℝ)
    (hFD_F : FunctionalDerivative F
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ =
      FunctionalDerivative F ω)
    (hFD_G : FunctionalDerivative G
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ =
      FunctionalDerivative G ω)
    (hPi : Pi_u (velocity_from_vorticity
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩) =
      Pi_u (velocity_from_vorticity ω)) :
    TetherKernel ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ F G =
      c ^ 2 * TetherKernel ω F G :=
  step2_degree_of_canonical_density TetherKernel canonicalTetherDensity
    tetherKernel_has_canonical_density (fun _ _ => rfl) F G ω c hFD_F hFD_G hPi

/-- Step 5 for `TetherKernel`: no degree `≥ 3` remainder, because the kernel
is exactly quadratic (`step2_degree`). C2–C3 do not force this for an
arbitrary antisymmetric `B`. -/
public theorem step5_higher_order
    (F G : Functional) (ω : CoadjointOrbit) (c : ℝ)
    (hFD_F : FunctionalDerivative F
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ =
      FunctionalDerivative F ω)
    (hFD_G : FunctionalDerivative G
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ =
      FunctionalDerivative G ω)
    (hPi : Pi_u (velocity_from_vorticity
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩) =
      Pi_u (velocity_from_vorticity ω))
    {n : Nat} (_hn : 3 ≤ n) :
    TetherKernel ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ F G =
      c ^ 2 * TetherKernel ω F G :=
  step2_degree F G ω c hFD_F hFD_G hPi

/-- `step2_degree` with the `Π_u` hypothesis discharged for `c ≠ 0`. -/
public theorem step2_degree_of_ne_zero
    (F G : Functional) (ω : CoadjointOrbit) (c : ℝ) (hc : c ≠ 0)
    (hFD_F : FunctionalDerivative F
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ =
      FunctionalDerivative F ω)
    (hFD_G : FunctionalDerivative G
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ =
      FunctionalDerivative G ω) :
    TetherKernel ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ F G =
      c ^ 2 * TetherKernel ω F G :=
  step2_degree F G ω c hFD_F hFD_G (hPi_of_ne_zero ω c hc)

/-- Minimality: the correction saturates the C3 quadratic form of `TetherKernel`. -/
public def SaturatesTetherQuadratic
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ (F : Functional) (ω : CoadjointOrbit), B ω F F = TetherKernel ω F F

/-- Polarization identity on functionals (`F+G` is pointwise addition). -/
public def Polarizes
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ (ω : CoadjointOrbit) (F G : Functional),
    2 * B ω F G =
      B ω (fun ω' => F ω' + G ω') (fun ω' => F ω' + G ω') -
        B ω F F - B ω G G

/-- Polarization restricted to functionals that HAVE functional gradients at `ω`
(`IsFunctionalGradient`). This is the form a bilinear form in `(δF, δG)` can satisfy: at a
functional with no gradient, `FunctionalDerivative` is `0` and carries no information. -/
@[expose] public def PolarizesOnDifferentiable
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ (ω : CoadjointOrbit) (F G : Functional),
    (∃ g, IsFunctionalGradient F ω g) → (∃ g, IsFunctionalGradient G ω g) →
    2 * B ω F G =
      B ω (fun ω' => F ω' + G ω') (fun ω' => F ω' + G ω') - B ω F F - B ω G G

/-- **PROVED** (formerly the hypothesis `Polarizes TetherKernel`, now in its true form):
the tether polarizes on every pair of functionals with functional gradients. -/
public theorem tetherKernel_polarizesOnDifferentiable :
    PolarizesOnDifferentiable TetherKernel := by
  rintro ω F G ⟨a, ha⟩ ⟨b, hb⟩
  exact tetherKernel_polarizes_of_gradient ha hb

/-- **REFUTED**: unrestricted polarization of the tether is false
(`TetherNondegeneracy.not_tetherKernel_polarizes`). The former hypothesis
`h_polarT : Polarizes TetherKernel` could never be supplied. -/
public theorem not_polarizes_tetherKernel : ¬ Polarizes TetherKernel :=
  not_tetherKernel_polarizes

/-- `TetherKernel` is symmetric in `F` and `G` because the real inner product
`⟨Π_u δF, Π_u δG⟩` is symmetric. -/
public theorem tetherKernel_symmetric (ω : CoadjointOrbit) (F G : Functional) :
    TetherKernel ω F G = TetherKernel ω G F :=
  tetherKernel_comm ω F G

/-- Symmetric polarization uniqueness of `TetherKernel`: because `TetherKernel` is a
symmetric negative-semidefinite bilinear pairing (the dissipative/metric component of a
metriplectic bracket), replacing `h_antisym` with symmetry `B ω F G = B ω G F` yields
a non-vacuous characterization satisfied by `B = TetherKernel`. Polarization of the tether is
now PROVED (`tetherKernel_polarizesOnDifferentiable`), not assumed; the conclusion is stated for
functionals with functional gradients at `ω`, the only ones a derivative-based kernel can see. -/
public theorem uniqueness_of_minimal_symmetric_tether
    (SDiff : Type*) [Group SDiff] [MulAction SDiff CoadjointOrbit]
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (_h_sym : ∀ ω F G, B ω F G = B ω G F)
    (_hC1 : InvariantUnderCoadjointAction SDiff B)
    (_hC2 : DegenerateWRTKineticEnergy B)
    (_hC3 : ProducesControllableNegativeFeedback B)
    (h_sat : SaturatesTetherQuadratic B)
    (h_polarB : PolarizesOnDifferentiable B) :
    ∀ (ω : CoadjointOrbit) (F G : Functional), (∃ g, IsFunctionalGradient F ω g) →
      (∃ g, IsFunctionalGradient G ω g) → B ω F G = TetherKernel ω F G := by
  intro ω F G hF hG
  have hB := h_polarB ω F G hF hG
  have hT := tetherKernel_polarizesOnDifferentiable ω F G hF hG
  have hFF := h_sat F ω
  have hGG := h_sat G ω
  have hFG := h_sat (fun ω' => F ω' + G ω') ω
  linarith


/-! ## Theorem 2.3 over the abstract SDiff action — SYMMETRIC (author's choice)

The antisymmetric reading is vacuous: with saturation, antisymmetry forces
`TetherKernel ω F F = 0` for every `F` (`antisym_sat_forces_zero_diag`), and with polarization
it forces `B = TetherKernel = 0` (`antisymmetric_clause_forces_zero`). The antisymmetric
theorem `uniqueness_of_minimal_tether_antisymmetric` and the vacuous step lemmas
`step1_locality`, `step3_projection`, `step4_coefficient` (which carried an unused
antisymmetry hypothesis and returned their input or `rfl`) were removed. -/

/-- Proved: antisymmetry + saturation kill the tether diagonal (vacuity of the
antisymmetric version). -/
public theorem antisym_sat_forces_zero_diag
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h_antisym : ∀ ω F G, B ω F G = -B ω G F) (h_sat : SaturatesTetherQuadratic B)
    (ω : CoadjointOrbit) (F : Functional) : TetherKernel ω F F = 0 := by
  have h := h_antisym ω F F
  rw [← h_sat F ω]; linarith

/-- **What `Polarizes TetherKernel` costs.** The polarization hypothesis on the tether (used by
`uniqueness_of_minimal_symmetric_tether`) forces `TetherKernel ω F G = 0` at every vorticity
with a non-differentiable component, because there the kernel is independent of `F, G`
(`tetherKernel_indep_of_not_differentiable`) and `2K = K - K - K` gives `K = 0`. Neither this
hypothesis is now REFUTED outright (`not_polarizes_tetherKernel`); nondegeneracy is PROVED
(`TetherNondegeneracy.tetherKernel_nondegenerate`). Kept as a record. -/
public theorem polarizes_tetherKernel_zero_of_not_differentiable
    (hP : Polarizes TetherKernel)
    {ω : CoadjointOrbit} (hω : ¬ ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x)
    (F G : Functional) : TetherKernel ω F G = 0 := by
  have h := hP ω F G
  have e1 := tetherKernel_indep_of_not_differentiable hω
    (fun ω' => F ω' + G ω') (fun ω' => F ω' + G ω') F G
  have e2 := tetherKernel_indep_of_not_differentiable hω F F F G
  have e3 := tetherKernel_indep_of_not_differentiable hω G G F G
  rw [e1, e2, e3] at h
  linarith

/-- **Vacuity of the removed antisymmetric clause.** The former
`uniqueness_of_minimal_tether_antisymmetric` (and clause 1 of `frohmanian_tether_theorem`)
took an antisymmetric `B` with `SaturatesTetherQuadratic B`, `Polarizes B` and
`Polarizes TetherKernel`. Those hypotheses force BOTH `B` and `TetherKernel` to vanish
identically (`TetherKernel` is symmetric), so the clause could only ever apply when the tether
is the zero form; it said nothing about the tether. The clause and the theorem were removed. -/
public theorem antisymmetric_clause_forces_zero
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h_antisym : ∀ ω F G, B ω F G = -B ω G F)
    (h_sat : SaturatesTetherQuadratic B)
    (h_polarB : Polarizes B)
    (h_polarT : Polarizes TetherKernel) :
    ∀ (ω : CoadjointOrbit) (F G : Functional), B ω F G = 0 ∧ TetherKernel ω F G = 0 := by
  have hBT : ∀ ω F G, B ω F G = TetherKernel ω F G := by
    intro ω F G
    have hB := h_polarB ω F G
    have hT := h_polarT ω F G
    have hFF := h_sat F ω
    have hGG := h_sat G ω
    have hFG := h_sat (fun ω' => F ω' + G ω') ω
    linarith
  intro ω F G
  have h1 := h_antisym ω F G
  have h2 := tetherKernel_comm ω F G
  rw [hBT ω F G, hBT ω G F] at h1
  have hT0 : TetherKernel ω F G = 0 := by linarith
  exact ⟨(hBT ω F G).trans hT0, hT0⟩

/-- `B` pairs every zero-derivative functional to zero. -/
@[expose] public def PairsToZeroIfDerivativeVanishes
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ ω (H G : Functional), FunctionalDerivative H ω = 0 → B ω H G = 0

/-- Named hypotheses for Step 1 (OPEN for a general `B`; together close to assuming
locality): bilinearity in the first slot, linearity of the derivative encoding, and
"zero-derivative functionals pair to zero". -/
public structure Step1Hyp (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop where
  sub_left : ∀ ω F F' G, B ω (fun η => F η - F' η) G = B ω F G - B ω F' G
  deriv_sub : ∀ ω (F F' : Functional),
    FunctionalDerivative (fun η => F η - F' η) ω = FunctionalDerivative F ω - FunctionalDerivative F' ω
  zero_deriv : PairsToZeroIfDerivativeVanishes B

/-- **Route 1 classical hypothesis (OPEN)**: at `ω`, a zero-derivative functional is, as seen
by `B`, a multiple of the kinetic-energy direction. (The SDiff-generator part cannot be
used: C1 moves `ω`, not the test functionals, so it gives no vanishing in the `F` slot.) -/
@[expose] public def ZeroDerivAlongEnergy
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ ω (H : Functional), FunctionalDerivative H ω = 0 →
    ∃ c : ℝ, ∀ G, B ω H G = c * B ω KineticEnergyHamiltonian G

/-- **[fallback / superseded] Route 1**: `PairsToZeroIfDerivativeVanishes` DERIVED from symmetry + C2 + the classical
hypothesis `ZeroDerivAlongEnergy`. C2 is used; C1 is not (see above). -/
public theorem pairsToZero_of_C2
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h_sym : ∀ ω F G, B ω F G = B ω G F) (hC2 : DegenerateWRTKineticEnergy B)
    (hE : ZeroDerivAlongEnergy B) : PairsToZeroIfDerivativeVanishes B := by
  intro ω H G hH
  obtain ⟨c, hc⟩ := hE ω H hH
  rw [hc G, h_sym, hC2 G ω, mul_zero]

/-- **REFUTED**: `Step1Hyp` is unsatisfiable for every `B`, because its field `deriv_sub`
(linearity of the derivative encoding on ALL functionals) is false
(`TetherNondegeneracy.not_forall_functionalDerivative_sub`). The former
`step1_locality_sym` / `step1_locality_route1`, which took it (or `deriv_sub`) as input, were
vacuous and have been removed; Step 1 is the corollary `step1_of_factorization`. -/
public theorem not_step1Hyp (B : CoadjointOrbit → Functional → Functional → ℝ) :
    ¬ Step1Hyp B := fun H => not_forall_functionalDerivative_sub H.deriv_sub

/-- `B ω` factors through the projected derivatives via one symmetric `Q`, independent
of `F, G`. -/
@[expose] public def FactorsThroughProjection
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ ω : CoadjointOrbit, ∃ Q : (T3 → EuclideanSpace ℝ (Fin 3)) → (T3 → EuclideanSpace ℝ (Fin 3)) → ℝ,
    (∀ a b, Q a b = Q b a) ∧
    ∀ F G : Functional, B ω F G =
      Q (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω))
        (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative G ω))

/-- **Step 2 (quadratic in `Π_u δF`, `Π_u δG`)**: PROVED from symmetry and the named
hypothesis `h_proj` (OPEN: `B` sees `δF` only through `Π_u δF`, a strengthening of Step 1's
locality, related to C2-degeneracy along `u`). Step 1's conclusion is subsumed by `h_proj`
and is carried, not needed. -/
public theorem step2_quadratic
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h_sym : ∀ ω F G, B ω F G = B ω G F)
    (h_proj : ∀ ω (F F' G : Functional),
      Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) =
        Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F' ω) → B ω F G = B ω F' G) :
    FactorsThroughProjection B := by
  classical
  intro ω
  let P : Functional → (T3 → EuclideanSpace ℝ (Fin 3)) := fun F =>
    Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω)
  have hboth : ∀ F G F' G', P F = P F' → P G = P G' → B ω F G = B ω F' G' := by
    intro F G F' G' hF hG
    rw [h_proj ω F F' G hF, h_sym, h_proj ω G G' F' hG, h_sym]
  let Q : (T3 → EuclideanSpace ℝ (Fin 3)) → (T3 → EuclideanSpace ℝ (Fin 3)) → ℝ := fun a b =>
    if h : (∃ F, P F = a) ∧ (∃ G, P G = b) then B ω h.1.choose h.2.choose else 0
  have hQ : ∀ F G, B ω F G = Q (P F) (P G) := by
    intro F G
    have h : (∃ F', P F' = P F) ∧ (∃ G', P G' = P G) := ⟨⟨F, rfl⟩, ⟨G, rfl⟩⟩
    simp only [Q, dif_pos h]
    exact hboth F G _ _ h.1.choose_spec.symm h.2.choose_spec.symm
  refine ⟨Q, ?_, hQ⟩
  intro a b
  by_cases ha : ∃ F, P F = a
  · by_cases hb : ∃ G, P G = b
    · obtain ⟨F, rfl⟩ := ha; obtain ⟨G, rfl⟩ := hb
      rw [← hQ, ← hQ, h_sym]
    · simp [Q, ha, hb]
  · simp [Q, ha]

/-- **Step 1, route 2 (PRIMARY; used by `step2_quadratic_and_locality`)**: locality in the derivatives as an immediate corollary of
Step 2's factorization through `Π_u δF`, `Π_u δG`. Route 1 (`ZeroDerivAlongEnergy`, or the
user's `SplitsIntoEnergyPlusSDiff`) collapsed: given C1 and C2 it is logically equivalent to
`PairsToZeroIfDerivativeVanishes`, so it is as strong as the conclusion. -/
public theorem step1_of_factorization
    (B : CoadjointOrbit → Functional → Functional → ℝ) (h2 : FactorsThroughProjection B) :
    ∀ ω (F G F' G' : Functional), FunctionalDerivative F ω = FunctionalDerivative F' ω →
      FunctionalDerivative G ω = FunctionalDerivative G' ω → B ω F G = B ω F' G' := by
  intro ω F G F' G' hF hG
  obtain ⟨Q, -, hQ⟩ := h2 ω
  rw [hQ F G, hQ F' G', hF, hG]

/-- **Steps 1+2 (route 2, ADOPTED; replaces a separate Step 1)**: for each `ω` there is ONE
symmetric `Q`, chosen before `F, G` are quantified, with `B ω F G = Q (Π_u δF) (Π_u δG)` for
all `F G`; locality in the derivatives is the immediate corollary
(`rw [hQ F G, hQ F' G', hF, hG]`). The factorization is PROVED from `h_sym` and the named
hypothesis `h_proj` (B sees `δF` only through `Π_u δF`); `h_proj` is the open content. -/
public theorem step2_quadratic_and_locality
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h_sym : ∀ ω F G, B ω F G = B ω G F)
    (h_proj : ∀ ω (F F' G : Functional),
      Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) =
        Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F' ω) → B ω F G = B ω F' G) :
    FactorsThroughProjection B ∧
    ∀ ω (F G F' G' : Functional), FunctionalDerivative F ω = FunctionalDerivative F' ω →
      FunctionalDerivative G ω = FunctionalDerivative G' ω → B ω F G = B ω F' G' :=
  have h2 := step2_quadratic B h_sym h_proj
  ⟨h2, step1_of_factorization B h2⟩

/-- The weight hypothesis in its POINTWISE form (the former `h_weight`): every density of `B`
is `-c ‖ω‖²` at every point. -/
@[expose] public def PointwiseEnstrophyWeight
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ α, HasTetherKernelDensity B α → ∃ c : ℝ, ∀ ω x, α ω x = -c * Enstrophy ω

/-- **REFUTED: the pointwise weight hypothesis contradicts the existence of any density.**
A density can be changed at the single point `x = 0` (a null set) without changing any
integral, so it cannot be pinned down pointwise. Hence for EVERY `B`, `h_density`'s output and
the pointwise `h_weight` are jointly inconsistent, and the former core theorem (which assumed
`h_sym`, `h_proj`, `h_density` and the pointwise `h_weight`) was vacuous. -/
public theorem not_pointwiseEnstrophyWeight_of_density
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (hex : ∃ α, HasTetherKernelDensity B α) : ¬ PointwiseEnstrophyWeight B := by
  obtain ⟨α, hα⟩ := hex
  intro hW
  classical
  let α' : CoadjointOrbit → T3 → ℝ := fun ω x => if x = 0 then α ω x + 1 else α ω x
  have hα' : HasTetherKernelDensity B α' := by
    intro ω F G
    rw [hα ω F G]
    apply integral_congr_ae
    filter_upwards [Measure.ae_ne (MeasureTheory.volume : Measure T3) 0] with x hx
    simp [α', hx]
  obtain ⟨c, hc⟩ := hW α hα
  obtain ⟨c', hc'⟩ := hW α' hα'
  let ω := rotOrbit 0
  have h1 : α ω (eb 0) = α' ω (eb 0) := by
    have : (eb 0 : T3) ≠ 0 := by
      intro h; have := congrArg (fun v : T3 => v 0) h; simp [eb] at this
    simp [α', this]
  have h2 : α' ω 0 = α ω 0 + 1 := by simp [α']
  rw [hc, hc'] at h1
  rw [hc, hc'] at h2
  linarith

/-- In particular the pointwise weight hypothesis fails for the tether itself. -/
public theorem not_pointwiseEnstrophyWeight_tetherKernel :
    ¬ PointwiseEnstrophyWeight TetherKernel :=
  not_pointwiseEnstrophyWeight_of_density TetherKernel
    ⟨_, tetherKernel_has_canonical_density⟩

/-- The weight hypothesis as first stated: EVERY density of `B` (no measurability or integrability
condition) equals `-c ‖ω‖²` almost everywhere at regular vorticities. REFUTED for `TetherKernel`
(`TetherWeight.not_aeEnstrophyWeightUnrestricted_tetherKernel`): at `ω = 0` the tether vanishes,
and the indicator of a Vitali-type set is a density there (its products with any function have
Bochner integral `0`) without vanishing a.e. -/
@[expose] public def AEEnstrophyWeightUnrestricted
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ α, HasTetherKernelDensity B α → ∃ c : ℝ, ∀ ω, IsRegularVorticity ω →
    ∀ᵐ x ∂(MeasureTheory.volume : Measure T3), α ω x = -c * Enstrophy ω

/-- The weight hypothesis `h_weight` in its corrected form (PROVED for `TetherKernel`:
`TetherWeightProof.tetherKernel_aeEnstrophyWeight`; open for a general `B`): every
density of `B` that is LOCALLY INTEGRABLE at each regular vorticity equals `-c ‖ω‖²` almost
everywhere, at regular vorticities only (at non-regular ones every derivative is `0`, so the
density is invisible). The integrability condition excludes the non-measurable densities that
refute `AEEnstrophyWeightUnrestricted`. -/
@[expose] public def AEEnstrophyWeight
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ α, HasTetherKernelDensity B α →
    (∀ ω, IsRegularVorticity ω → LocallyIntegrable (α ω) (MeasureTheory.volume : Measure T3)) →
    ∃ c : ℝ, ∀ ω, IsRegularVorticity ω →
      ∀ᵐ x ∂(MeasureTheory.volume : Measure T3), α ω x = -c * Enstrophy ω

/-- The canonical density of the tether is spatially constant, hence locally integrable. -/
public theorem canonicalTetherDensity_locallyIntegrable (ω : CoadjointOrbit) :
    LocallyIntegrable (canonicalTetherDensity ω) (MeasureTheory.volume : Measure T3) :=
  locallyIntegrable_const _

/-- **Step 3 (scalar multiple of the canonical density)**: from Step 2, the named density
hypothesis `h_density` (OPEN for a general `B`: `Q = ∫ α ⟨·,·⟩` with `α ω` locally integrable at
regular `ω`, a Schwartz-kernel / isotropy statement) and the weight hypothesis
`h_weight : AEEnstrophyWeight B` (OPEN for a general `B`, PROVED for `B = TetherKernel`; the pointwise form
and the unrestricted a.e. form are refuted). At non-regular `ω` both sides vanish because
`FunctionalDerivative` is `0` there. -/
public theorem step3_scalar
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h2' : FactorsThroughProjection B)
    (h_density : FactorsThroughProjection B → ∃ α, HasTetherKernelDensity B α ∧
      ∀ ω, IsRegularVorticity ω → LocallyIntegrable (α ω) (MeasureTheory.volume : Measure T3))
    (h_weight : AEEnstrophyWeight B) :
    ∃ c : ℝ, HasTetherKernelDensity B (fun ω _x => -c * Enstrophy ω) := by
  obtain ⟨α, hα, hloc⟩ := h_density h2'
  obtain ⟨c, hc⟩ := h_weight α hα hloc
  refine ⟨c, fun ω F G => ?_⟩
  rw [hα ω F G]
  by_cases hω : IsRegularVorticity ω
  · apply integral_congr_ae
    filter_upwards [hc ω hω] with x hx
    rw [hx]
  · simp [functionalDerivative_eq_zero_of_not_regular hω, Pi_u_zero]

/-- **Step 4 (scalar = κ)**: PROVED from Step 3, saturation, and one nondegenerate witness. -/
public theorem step4_scalar_eq_kappa
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h3 : ∃ c : ℝ, HasTetherKernelDensity B (fun ω _x => -c * Enstrophy ω))
    (h_sat : SaturatesTetherQuadratic B)
    (h_nondeg : ∃ (ω : CoadjointOrbit) (F : Functional), Enstrophy ω * (∫ x,
        inner ℝ (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x)
          (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x) ∂NavierStokes3D.volume) ≠ 0) :
    HasTetherKernelDensity B canonicalTetherDensity := by
  obtain ⟨c, hc⟩ := h3
  obtain ⟨ω₀, F₀, hI⟩ := h_nondeg
  have e1 := hc ω₀ F₀ F₀
  have e2 := h_sat F₀ ω₀
  rw [integral_const_mul (μ := volume)] at e1
  have e3 : TetherKernel ω₀ F₀ F₀ = -kappa * Enstrophy ω₀ * ∫ x,
      inner ℝ (Pi_u (velocity_from_vorticity ω₀) (FunctionalDerivative F₀ ω₀) x)
        (Pi_u (velocity_from_vorticity ω₀) (FunctionalDerivative F₀ ω₀) x) ∂NavierStokes3D.volume := rfl
  have hck : c = kappa := by
    have h0 := e1.symm.trans (e2.trans e3)
    rw [mul_assoc, mul_assoc] at h0
    have h' := mul_right_cancel₀ hI h0
    linarith
  intro ω F G
  rw [hc ω F G]; simp [canonicalTetherDensity, hck]

/-- **PROVED** (formerly the hypothesis `h_nondeg`): the tether pairing is not identically
zero, witnessed by a linear test functional at the smooth rotation field `rotOrbit 0`. -/
public theorem tether_nondeg_witness :
    ∃ (ω : CoadjointOrbit) (F : Functional), Enstrophy ω * (∫ x,
        inner ℝ (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x)
          (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x) ∂NavierStokes3D.volume) ≠ 0 := by
  obtain ⟨ω, φ, -, -, hne⟩ := tetherKernel_nondegenerate
  refine ⟨ω, linFun φ, fun h => hne ?_⟩
  have e : TetherKernel ω (linFun φ) (linFun φ) = -kappa * (Enstrophy ω * (∫ x,
        inner ℝ (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative (linFun φ) ω) x)
          (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative (linFun φ) ω) x)
            ∂NavierStokes3D.volume)) := by
    rw [← mul_assoc]; rfl
  rw [e, h, mul_zero]

/-- The kernel conditions that the tether itself satisfies, all PROVED: saturation, `h_proj`,
the canonical density, restricted polarization and nondegeneracy. -/
public theorem tetherKernel_kernel_conditions :
    SaturatesTetherQuadratic TetherKernel ∧
    (∀ ω (F F' G : Functional),
      Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) =
        Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F' ω) →
        TetherKernel ω F G = TetherKernel ω F' G) ∧
    HasTetherKernelDensity TetherKernel canonicalTetherDensity ∧
    PolarizesOnDifferentiable TetherKernel ∧
    (∃ ω F, TetherKernel ω F F ≠ 0) := by
  refine ⟨fun _ _ => rfl, ?_, tetherKernel_has_canonical_density,
    tetherKernel_polarizesOnDifferentiable, ?_⟩
  · intro ω F F' G h
    unfold TetherKernel
    rw [h]
  · obtain ⟨ω, φ, -, -, hne⟩ := tetherKernel_nondegenerate
    exact ⟨ω, linFun φ, hne⟩

/-- **Step 5 (equality with `TetherKernel`)**: PROVED from Step 4. -/
public theorem step5_eq_tether
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h4 : HasTetherKernelDensity B canonicalTetherDensity) :
    ∀ ω F G, B ω F G = TetherKernel ω F G :=
  uniqueness_of_kernel_density B canonicalTetherDensity h4 (fun _ _ => rfl)

/-- **Five-step core** (symmetric). Each step consumes the previous step's conclusion.
Open inputs (properties of the arbitrary `B`): `h_proj`, `h_density` (a density, locally
integrable at regular `ω`), `h_weight` (a.e., regular `ω`, locally integrable densities). Nondegeneracy is no longer an input: it is PROVED
(`tether_nondeg_witness`). -/
public theorem uniqueness_of_minimal_tether_core
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h_sym : ∀ ω F G, B ω F G = B ω G F)
    (h_proj : ∀ ω (F F' G : Functional),
      Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) =
        Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F' ω) → B ω F G = B ω F' G)
    (h_density : FactorsThroughProjection B → ∃ α, HasTetherKernelDensity B α ∧
      ∀ ω, IsRegularVorticity ω → LocallyIntegrable (α ω) (MeasureTheory.volume : Measure T3))
    (h_weight : AEEnstrophyWeight B)
    (h_sat : SaturatesTetherQuadratic B) :
    ∀ ω F G, B ω F G = TetherKernel ω F G :=
  have h2 := (step2_quadratic_and_locality B h_sym h_proj).1
  have h3 := step3_scalar B h2 h_density h_weight
  have h4 := step4_scalar_eq_kappa B h3 h_sat tether_nondeg_witness
  step5_eq_tether B h4

/-- **Theorem 2.3 (symmetric) over the abstract SDiff action**, user interface: takes
`SDiffActionHyp`, C1–C3, saturation and polarization of `B` on differentiable functionals.
Proved by polarization; the tether's own polarization is PROVED. `hyp`, C1, C2, C3 are carried
but NOT used by the proof (the conclusion follows from `h_sat` + polarization alone). -/
public theorem uniqueness_of_minimal_tether
    (SDiff : Type*) [Group SDiff] [MulAction SDiff CoadjointOrbit]
    (_hyp : SDiffActionHyp SDiff)
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h_sym : ∀ ω F G, B ω F G = B ω G F)
    (hC1 : InvariantUnderCoadjointAction SDiff B)
    (hC2 : DegenerateWRTKineticEnergy B)
    (hC3 : ProducesControllableNegativeFeedback B)
    (h_sat : SaturatesTetherQuadratic B)
    (h_polarB : PolarizesOnDifferentiable B) :
    ∀ (ω : CoadjointOrbit) (F G : Functional), (∃ g, IsFunctionalGradient F ω g) →
      (∃ g, IsFunctionalGradient G ω g) → B ω F G = TetherKernel ω F G :=
  uniqueness_of_minimal_symmetric_tether SDiff B h_sym hC1 hC2 hC3 h_sat h_polarB

/-!
## Later paper: uniqueness of global regular solutions

Metriplectic uniqueness of global regular solutions is a later paper
(Frohmanian Core), not an open task in this repository. No `True`
placeholder theorem is declared here.
-/

/-!
## Non-Circularity Reminder (Critical for Clay Audit)

All uniqueness claims in this module respect the two-layer architecture:

- Layer 1 uniqueness (the Tether itself) is proved using only the coadjoint orbit
  geometry, the vorticity transport equation of the *unmodified* NS system, and
  the five axioms (A1)–(A5) / (C1)–(C3). It does not use any analytic estimates
  from Layer 2.

- Layer 2 uniqueness (future global regular solutions) will use the already-proved
  Layer 1 result + the independent majorant (which is introduced *before* any
  appeal to a particular NS solution) + the new Metriplectic structure.

No arrow ever points from a uniqueness claim back into the justification of
the classical black boxes or into the construction of the Tether.

See the four living checklists in `Blueprint.md` and the "How to Audit
Non-Circularity" section.
-/

-- =============================================================================
-- AXIOM CHECKS

/-! Axiom checks for the declarations of this module (the strict repository-wide audit is
`scripts/AxiomAudit.lean`). -/

#print axioms uniqueness_of_kernel_density
#print axioms uniqueness_of_kernel_density_fun
#print axioms tetherKernel_has_canonical_density
#print axioms uniqueness_of_minimal_tether
#print axioms step2_degree_of_canonical_density
#print axioms step2_degree
#print axioms step5_higher_order

end FrohmanianTether
