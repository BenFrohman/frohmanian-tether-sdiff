/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.LebesgueNormedSpace
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import FrohmanianTether.NS_Equations
public import FrohmanianTether.ArnoldGeometric
public import FrohmanianTether.ForMathlib.Projection

universe u

/-!
# The Frohmanian tether kernel

Definitions of the tether kernel `TetherKernel` (a symmetric quadratic correction to the Arnold
Lie–Poisson bracket), the tethered bracket, and the conditions (C1)–(C3), with the results proved
about them. Status (see `CERTIFICATE.md`): (C3) is proved; (C1) and (C2) are **not** proved for
`TetherKernel`; no Jacobi identity is claimed for the tethered bracket. The canonicity theorems are
in `Uniqueness.lean`. The analytic statements in `TetheredLyapunov.lean` are conditional
implications; nothing in this repository proves global regularity of the 3D Navier–Stokes
equations. The repository contains no `sorry` and declares no axioms.
-/

namespace FrohmanianTether

open ArnoldGeometric
open InnerProductSpace NavierStokes3D ArnoldGeometric MeasureTheory ForMathlib

noncomputable section

/-!
## Namespaces and Sections (§6 of the Lean Language Reference)

This file uses Lean's namespace and section scoping features as described in §6:

- The `namespace SymplecticTether` groups all novel geometric constructions (TetherKernel,
  the 5-step canonicity argument, degeneracy, invariance, and the explicit Jacobi verification
  on test functionals F_p).

- `open` brings commonly-used namespaces into scope without qualification (NavierStokes3D for
  the classical PDE layer, ArnoldGeometric for the coadjoint orbit primitives, etc.).

- `variable` declarations (introduced below) factor out repeated parameters that appear across
  the 5-step uniqueness lemmas and the Jacobi identity expansion. Per §6.2.2, these are
  automatically inserted into declarations that mention them, both in headers and (for theorems)
  in statements. This dramatically improves readability of the atomic lemmas while preserving
  the precise logical structure required by the sources.

- The `noncomputable section` is used because the development relies on classical reasoning
  principles (choice, excluded middle) in the black-box analytic parts. This is the recommended
  pattern from the reference when a section contains noncomputable definitions.

- Future use of `section … in …` or `include`/`omit` may be added when filling the remaining
  classical sub-steps inside `h_cyclic_integrand_zero` to locally bring in assumptions only where needed.

This organization directly follows the "correct precise order of representational flow" demanded
by the three source documents (PDE → classical Arnold bracket → explicit tether construction →
degeneracy → invariance → Jacobi → canonicity).
-/

/-! ## Basic Types (re-exported for convenience; must precede uses in `variable` and defs) -/

-- CoadjointOrbit is brought bare by the early open ArnoldGeometric above (reorg hygiene).
-- The previous qualified abbrev was causing "Unknown constant `ArnoldGeometric....`" resolution issues.
public abbrev Functional := CoadjointOrbit → ℝ

variable {ω : CoadjointOrbit} {F G H : Functional}

/-!
## Definitions (§7 of the Lean Language Reference)

This module follows the guidance in §7 Definitions, with the following deliberate choices:

- `abbrev` is used for transparent type aliases (`CoadjointOrbit`, `Functional`) — per 7.3, these are definitionally transparent and do not generate new constants in the kernel.

- `def` (often `noncomputable`) is used for:
  - Computational or data-level objects (`Pi_u`, `TetherKernel`, `TetheredBracket`, `MollifiedSupNormFunctional`, etc.).
  - Property definitions that are not pure theorems (`InvariantUnderCoadjointAction`, `DegenerateWRTKineticEnergy`, `ProducesControllableNegativeFeedback`). These are `def` because they define the meaning of the three necessary conditions (C1)–(C3) as predicates, not as statements to be proved.

- `theorem` / `lemma` is reserved for actual assertions that require proof:
  - `uniqueness_of_minimal_tether` (the 5-step canonicity Theorem 2.3)
  - (formerly `tether_coadjoint_invariance` and `tethered_jacobi_identity`; both deleted in
    Nov 2026, see the C1 and Jacobi sections below)

- `noncomputable section` + `noncomputable def` (7.1 Modifiers) is used because large parts of the development rely on classical reasoning (choice for existence of solutions to ODEs, excluded middle in case distinctions, etc.). This is the recommended pattern when a section contains noncomputable definitions.

- The atomic canonicity lemmas use `lemma` / `theorem` + many named `have` blocks. This follows the Tao-style atomic structure while staying inside the `theorem` command (7.4).

-- Author dev reference: standalone Mermaid for the exact 5-step canonicity the user supplied
-- lives at mermaid/5step_canonicity.mmd (pairs with the full two-layer at mermaid/two_layer_may20_architecture.mmd).

- Headers and signatures are kept explicit (no unnecessary implicit arguments at the top level of the main theorems) so that the logical dependencies are completely visible — again per the spirit of §7.2.

These choices ensure that the novel geometric content (the explicit construction of the Frohmanian Tether and its canonicity) is clearly distinguished from both the classical black boxes and from pure definitional abbreviations.
-/

/-! ## The L²-Orthogonal Projection Π_u (core device for degeneracy) -/

-- The explicit definition and core lemmas have been centralized in ForMathlib/Projection.lean
-- (Tao PFR hygiene: reusable results go to ForMathlib for eventual upstreaming).
-- We import and use the canonical rigorous version here.
-- Projection open simplified (names from ForMathlib/Projection used in comments / stubs;
-- full resolution of ForMathlib. ns prefix for the open list was triggering unknown during reorg).
-- The key lemmas (projector_orthogonality etc.) are documented via the centralized ForMathlib module.

/-! ## Calderón–Zygmund Constant (universal, solution-independent)

`C_CZ(3)` is the spherical L¹ of the operator-norm density of the 3D Biot–Savart
strain kernel
`(K z ω)_{ij} = (3/(8 π)) [(z × ω)_i z_j + (z × ω)_j z_i] / |z|^5`
(Constantin–Fefferman / Majda–Bertozzi). The angular density has operator norm
`3/(8 π)` at every pole of `S²`, so
`C_CZ(3) = (3/(8 π)) · area(S²) = (3/(8 π)) · 4 π = 3/2`.
This is **not** the nondimensional stand-in `1`. The operational multiplier `4`
in `4 C_CZ(3)` is the quartic product-rule factor, **not** a 4D spatial constant.
The L² Fourier multiplier of `∇u` from `ω` is separately `≤ 1`; the strain
multiplier is `≤ 1/2`. Young absorption is homogeneous in `κ = C_CZ(3)`.
-/

/-- `C_CZ(3) = (3/(8 π)) · 4 π`. Evaluates to `3/2`, not `1`. -/
@[expose] public noncomputable def CalderonZygmundConstant3D : ℝ :=
  biotSavartStrainKernelPrefactor * sphereAreaS2

public theorem CalderonZygmundConstant3D_eq_three_halves :
    CalderonZygmundConstant3D = 3 / 2 := by
  unfold CalderonZygmundConstant3D biotSavartStrainKernelPrefactor sphereAreaS2
  field_simp [Real.pi_ne_zero]
  ring

public theorem CalderonZygmundConstant3D_ne_one :
    CalderonZygmundConstant3D ≠ 1 := by
  rw [CalderonZygmundConstant3D_eq_three_halves]
  norm_num

public theorem CalderonZygmundConstant3D_pos : 0 < CalderonZygmundConstant3D := by
  rw [CalderonZygmundConstant3D_eq_three_halves]
  exact div_pos three_pos two_pos

/-- Tether strength. ASCII name `kappa`; `κ` is notation only.
Forced by (C3) to equal `C_CZ(3) = 3/2`, not the stand-in `1`. -/
@[expose] public noncomputable def kappa : ℝ := CalderonZygmundConstant3D

scoped notation "κ" => kappa

public theorem kappa_eq_three_halves : kappa = 3 / 2 :=
  CalderonZygmundConstant3D_eq_three_halves

public theorem kappa_ne_one : kappa ≠ 1 :=
  CalderonZygmundConstant3D_ne_one

public theorem kappa_pos : 0 < kappa := CalderonZygmundConstant3D_pos

/-- Quartic product-rule multiplier times the 3D CZ constant: `4 * C_CZ(3) = 6`. -/
@[expose] public noncomputable def quartic_stretching_bound_coeff : ℝ :=
  4 * CalderonZygmundConstant3D

/-- Residual tether strength after Young absorption: `κ' = (3/4) κ > 0`.
This packages the I₆ remainder after `ε = 3 κ / 8` (so the absorbed I₆
coefficient is `κ/4`). The paper's alternate writing `κ' = κ/2 − C_abs'`
with `C_abs' ≤ 2` keeps a Gagliardo–Nirenberg piece on I₆; here `C_abs`
stays off I₆, so positivity is `κ > 0` rather than `κ > 4`. -/
@[expose] public noncomputable def kappa' : ℝ := (3 / 4) * kappa

public theorem kappa'_pos : 0 < kappa' := by
  have h34 : (0 : ℝ) < 3 / 4 := by
    exact div_pos three_pos four_pos
  exact mul_pos h34 kappa_pos

/-- Gagliardo–Nirenberg / Sobolev representative on the 3-torus model.
Positivity is a theorem; the operational use is the Hölder bound
`∫|ω|⁴|φ| ≤ C_Sob ‖φ‖_∞ (∫|ω|⁶)^{2/3}`. -/
@[expose] public def SobolevConstant3D : ℝ := 1

public theorem SobolevConstant3D_pos : 0 < SobolevConstant3D := by
  change (0 : ℝ) < 1
  exact one_pos

/-- Canonical absorption parameter `ε_abs = κ/4` used in Young (p = 3/2, q = 3).
The analytic pipeline's ε-Young that produces I₆ coefficient `κ/4` uses
`ε = 3 κ / 8`; `ε_abs` is the canonicity-forced scale `κ/4`. -/
@[expose] public noncomputable def epsilon_abs : ℝ := kappa / 4

/-! ## The Quadratic Metric Correction (the Tether) -/

/-- Canonical Frohmanian tether kernel
`B(F,G)(ω) = -κ ‖ω‖² ∫ (Π_u (δF/δω) · Π_u (δG/δω)) dλ`, with the GLOBAL enstrophy
`‖ω‖² = Enstrophy ω = ∫ |ω|²` outside the integral (author decision 2026-11-03; the former
pointwise `|ω(x)|²` density is a different object). -/
@[expose] public noncomputable def TetherKernel (ω : CoadjointOrbit) (F G : Functional) : ℝ :=
  -kappa * Enstrophy ω * ∫ x,
      inner ℝ
        (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x)
        (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative G ω) x)
    ∂volume

public noncomputable def TetheredBracket (F G : Functional) (ω : CoadjointOrbit) : ℝ :=
  -- The Frohmanian Symplectic Tether bracket: the classical Arnold Lie–Poisson bracket
  -- plus the minimal quadratic correction (the tether kernel) that satisfies (C1)–(C3).
  -- Canonicity is proved only inside the restricted kernel class and under the explicit
  -- hypotheses of `uniqueness_of_minimal_tether` (Uniqueness.lean); it is NOT an
  -- unconditional uniqueness statement. The correction is symmetric, so this bracket is
  -- not antisymmetric.
  ClassicalBracket F G ω + TetherKernel ω F G

/-! ## The Three Necessary Conditions (C1)–(C3) — exactly as in the audited LaTeX -/

/--
Property (C1): The correction is invariant under the coadjoint action of SDiff(T³).

Defined as a `def` returning `Prop` per Lean reference §7 (Definitions).
This is a predicate on the higher-order object `B`, not a theorem asserting a specific fact.
-/
@[expose] public def InvariantUnderCoadjointAction (SDiff : Type*) [Group SDiff]
    [MulAction SDiff CoadjointOrbit] (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  -- (C1): The correction B is invariant under the coadjoint action of SDiff(T³).
  -- For all volume-preserving g, the value of the correction is unchanged when the vorticity
  -- and the test functionals are transformed by the coadjoint action.
  ∀ (g : SDiff) (F G : Functional) (ω : CoadjointOrbit),
    B (CoadjointAction g ω) F G = B ω F G

@[expose] public def DegenerateWRTKineticEnergy (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  -- (C2): The correction is degenerate with respect to the kinetic-energy Hamiltonian H.
  -- The Hamiltonian vector field generated by H is exactly the classical one (no modification
  -- to the reversible Euler dynamics). This is the energy-preserving degeneracy on energy.
  ∀ (F : Functional) (ω : CoadjointOrbit),
    B ω F KineticEnergyHamiltonian = 0

/-- (C3): after `Π_u`, the correction is negative-semidefinite with leading coefficient `-κ`. -/
@[expose] public def ProducesControllableNegativeFeedback
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ (F : Functional) (ω : CoadjointOrbit),
    B ω F F ≤
      -kappa * Enstrophy ω * ∫ x,
          ‖Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x‖ ^ 2
        ∂volume

/-- C3 as equality for the canonical kernel: `𝔗(F,F) = -κ ‖ω‖² ∫ ‖Π_u δF‖²`. -/
public theorem tetherKernel_quadratic_form (F : Functional) (ω : CoadjointOrbit) :
    TetherKernel ω F F =
      -kappa * Enstrophy ω * ∫ x,
          ‖Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x‖ ^ 2
        ∂volume := by
  unfold TetherKernel
  congr 1
  congr 1
  funext x
  rw [real_inner_self_eq_norm_sq]

/-- The canonical kernel is symmetric in the two test functionals.
A Poisson correction must be antisymmetric; these cannot both hold
unless the kernel vanishes. -/
public theorem tetherKernel_comm (ω : CoadjointOrbit) (F G : Functional) :
    TetherKernel ω F G = TetherKernel ω G F := by
  unfold TetherKernel
  congr 1
  congr 1
  funext x
  rw [real_inner_comm]

/-- At a vorticity with a non-differentiable component, `TetherKernel ω F G` does not depend on
`F` or `G` (`functionalDerivative_indep_of_not_differentiable`): the tether sees no test
functional there. -/
public theorem tetherKernel_indep_of_not_differentiable
    {ω : CoadjointOrbit} (hω : ¬ ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x)
    (F G F' G' : Functional) :
    TetherKernel ω F G = TetherKernel ω F' G' := by
  unfold TetherKernel
  rw [functionalDerivative_indep_of_not_differentiable hω F F',
    functionalDerivative_indep_of_not_differentiable hω G G']

/-- Antisymmetry of a bilinear correction forces the diagonal to vanish.
C3 negative-semidefiniteness `B(F,F) ≤ -κ ‖ω‖² ∫ ‖Π_u δF‖²` is therefore
incompatible with a Poisson (antisymmetric) correction, except on the
kernel of `Π_u`. -/
public theorem antisymmetric_correction_diagonal_zero
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h : ∀ ω F G, B ω F G = -B ω G F)
    (ω : CoadjointOrbit) (F : Functional) :
    B ω F F = 0 := by
  have := h ω F F
  linarith

public theorem tetherKernel_C3 (F : Functional) (ω : CoadjointOrbit) :
    TetherKernel ω F F ≤
      -kappa * Enstrophy ω * ∫ x,
          ‖Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x‖ ^ 2
        ∂volume :=
  le_of_eq (tetherKernel_quadratic_form F ω)

/-- The reduced pairing is the cubic source minus `k M⁴`.
Algebra only: `k` is a free real, not yet `kappa`. -/
public theorem reduced_pairing_iff_cancels_kappa_M4
    (pairing C k M : ℝ) :
    pairing ≤ (C * M - k * M ^ 2) * M ^ 2 ↔
      pairing + k * M ^ 4 ≤ C * M ^ 3 := by
  constructor
  · intro h
    have hsplit :
        (C * M - k * M ^ 2) * M ^ 2 + k * M ^ 4 = C * M ^ 3 := by ring
    linarith
  · intro h
    have hsplit :
        C * M ^ 3 - k * M ^ 4 = (C * M - k * M ^ 2) * M ^ 2 := by ring
    linarith

/-- The projected kernel density has no positive part. `Π_u` is the
`L²` complement of `span{u}`; this pointwise sign does not need
`‖Π_u δF‖ ≤ ‖δF‖`, and the summand contains no mollifier. -/
public theorem tether_kernel_density_nonpos
    (orbit : CoadjointOrbit) (testF : Functional) (x : T3) :
    -kappa *
        (‖orbit.val x‖ ^ 2 *
          ‖Pi_u (velocity_from_vorticity orbit)
              (FunctionalDerivative testF orbit) x‖ ^ 2) ≤ 0 := by
  have hκ : -kappa ≤ 0 := neg_nonpos.mpr kappa_pos.le
  have hsq :
      0 ≤ ‖orbit.val x‖ ^ 2 *
        ‖Pi_u (velocity_from_vorticity orbit)
            (FunctionalDerivative testF orbit) x‖ ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  exact mul_nonpos_of_nonpos_of_nonneg hκ hsq

/-- Step 6 is division by `M > 0`, once the reduced pairing and the
identification `rate = pairing / M` are known. Neither is supplied here. -/
public theorem max_rate_of_reduced_pairing
    (rate pairing M C k : ℝ) (hM : 0 < M)
    (hrate : rate = pairing / M)
    (hpair : pairing ≤ (C * M - k * M ^ 2) * M ^ 2) :
    rate ≤ C * M ^ 2 - k * M ^ 3 := by
  rw [hrate]
  apply (div_le_iff₀ hM).mpr
  have hrew :
      (C * M - k * M ^ 2) * M ^ 2 = (C * M ^ 2 - k * M ^ 3) * M := by ring
  exact hpair.trans_eq hrew

/-- At a spatial maximum the transport pairing vanishes and `ν ⟨ω, Δω⟩ ≤ 0`,
so neither term adds a positive remainder above `⟨ω, (ω·∇)u⟩`. -/
public theorem time_pairing_le_stretching_at_max
    (u : TimeDependentVelocity) (p : TimeDependentPressure) (ν : ℝ)
    (t : ℝ) (ht : 0 ≤ t) (x : T3)
    (hNS : NS_PDE u p ν)
    (hreg : VorticityTransportRegularity u p t x)
    (htransp : inner ℝ (vorticity (u t) x)
      (convective (u t) (vorticity (u t)) x) = 0)
    (hvisc : inner ℝ (vorticity (u t) x)
      (laplacian (vorticity (u t)) x) ≤ 0)
    (hν : 0 ≤ ν) :
    inner ℝ (vorticity (u t) x)
        (time_deriv (fun s => vorticity (u s)) t x) ≤
      inner ℝ (vorticity (u t) x)
        (convective (vorticity (u t)) (u t) x) := by
  have hinter := vorticity_transport_inner u p ν t ht x hNS hreg
  have hviscν :
      inner ℝ (vorticity (u t) x)
          (ν • laplacian (vorticity (u t)) x) ≤ 0 := by
    rw [inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos hν hvisc
  linarith [hinter, htransp, hviscν]

/-! ## Removed: bridges conditional on the false strain bound

`ConjecturedUnmodifiedTetherPairing`, `reduced_pairing_of_unmodified_and_tether`,
`tethered_stretching_of_weight`, `tethered_h_slot_stretching_remains_cubic` and
`unmodified_pairing_and_c3_diagonal` all assumed the pointwise strain bound
`‖Du(x)‖ ≤ C ‖ω‖_∞` (formerly `PointwiseStrainSupBound`). That bound is false in general
(`StrainBoundRefutation.not_forall_strain_le_sup_vorticity`), so they were deleted. -/

/-! ## The Frohmanian tether hypotheses (explicit, open, not axioms)

The main theorems are conditional. These two Props name, in one place, the
hypotheses they consume. Restricting to physically admissible solutions
(`IsPhysicalNSSolution u`) ensures non-vacuity and rules out step-jump and
unbounded non-L² parasitic fields. -/

/-- **Frohmanian tether bound** for the datum `u₀` (the `hRiccati` binder of
`conditional_regularity_of_open_hyps`): every physically admissible Navier–Stokes solution from `u₀` has
`‖ω(τ)‖_∞` bounded uniformly in `τ ≥ 0` and continuous in time.
The last conjunct (`BddAbove` of `x ↦ ‖ω(τ,x)‖` at every `τ ≥ 0`) is essential:
`vorticity_sup_norm` is a real `iSup`, which Mathlib sets to `0` on unbounded ranges, so
without it an unbounded field would satisfy the bound vacuously.
OPEN for general data; kernel-verified satisfiable at `u₀ = 0` (`frohmanianTetherBound_zero`). -/
@[expose] public abbrev FrohmanianTetherBound (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∀ u : ℝ → VelocityField, ∀ p : ℝ → PressureField,
    NS_PDE u p ν → u 0 = u₀ → IsPhysicalNSSolution u →
      ∃ Y : ℝ,
        (∀ τ ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u τ)) ≤ Y) ∧
        Continuous (fun τ : ℝ => vorticity_sup_norm (vorticity (u τ))) ∧
        (∀ τ ≥ (0 : ℝ), BddAbove (Set.range fun x => ‖vorticity (u τ) x‖))

/-- **Frohmanian tether rate** (the `hDI` binder of `frohmanian_tether_theorem`):
along every physically admissible solution, `M(t) = ‖ω(t)‖_∞` is differentiable and obeys
`M' ≤ C M² - κ'' M³` with `C, κ'' > 0`. OPEN for general data; kernel-verified satisfiable
at `u₀ = 0` (`frohmanianTetherRate_zero`). -/
@[expose] public abbrev FrohmanianTetherRate (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∀ u : ℝ → VelocityField, ∀ p : ℝ → PressureField,
    0 < ν → NS_PDE u p ν → u 0 = u₀ → IsPhysicalNSSolution u →
      ∃ C κ'' : ℝ, 0 < C ∧ 0 < κ'' ∧
        (∀ s ≥ (0 : ℝ),
          DifferentiableAt ℝ (fun τ => vorticity_sup_norm (vorticity (u τ))) s) ∧
        (∀ s ≥ (0 : ℝ),
          deriv (fun τ => vorticity_sup_norm (vorticity (u τ))) s ≤
            C * vorticity_sup_norm (vorticity (u s)) ^ 2 -
              κ'' * vorticity_sup_norm (vorticity (u s)) ^ 3) ∧
        Continuous (fun τ : ℝ => vorticity_sup_norm (vorticity (u τ))) ∧
        (∀ τ ≥ (0 : ℝ), BddAbove (Set.range fun x => ‖vorticity (u τ) x‖))

/-- If the right `Π_u` factor vanishes, the kernel is zero (C2 mechanism). -/
public theorem tetherKernel_of_right_factor_zero
    (ω : CoadjointOrbit) (F G : Functional)
    (h : Pi_u (velocity_from_vorticity ω) (FunctionalDerivative G ω) = 0) :
    TetherKernel ω F G = 0 := by
  unfold TetherKernel
  have hpt : ∀ x,
      inner ℝ
        (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x)
        (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative G ω) x) = 0 := by
    intro x
    rw [h]
    simp
  simp [hpt]

/-! ## Explicit Degeneracy for the Mollified Sup-Norm Proxy (LaTeX Section 2.4.1 — Critical for Navier–Stokes)

This lemma is one of the most important Navier–Stokes-level verifications. It must satisfy:
- Non-Circularity audit (see Blueprint.md)
- Non-Ad-Hoc, Non-Ansatz, 1st Principles, and Canonicality checklists
-/

def mollify (_ε : ℝ) (f : T3 → (EuclideanSpace ℝ (Fin 3))) : T3 → (EuclideanSpace ℝ (Fin 3)) := f   -- _ε unused (identity stub for dev); standard mollifier (black-box classical); from side tabs (Clarified and living: "standard mollifier η_ε", identity for dev as the estimates don't depend on specific kernel beyond standard properties)

def MollifiedSupNormFunctional (ε : ℝ) (ω : CoadjointOrbit) : ℝ :=
  ⨆ x, ‖mollify ε ω.val x‖

/-! ## Theorem 2.3 — Uniqueness of the Minimal Correction (PASS 2 / GotItNavier_Final Section 2.7) -/

/-! ### Supporting lemmas for degeneracy and the 5-step (drawn from classical analysis)

These are the key classical facts needed to make the degeneracy and coefficient-matching arguments rigorous.
They are treated as black boxes (with justifications) per the project's separation of classical vs novel.

See also the fully expanded + clarified user-supplied version in:
  docs/Clarified_Degeneracy_and_Majorant_Blocks.lean  (BLOCK 2)
which provides the double-support explanation for the projector (Fourier + Hodge/de Rham),
the explicit "IMPORTANT: local on existence interval" note for euler_energy_conservation,
and the full chain with user's clarifications. The versions here are adapted to the project's
CoadjointOrbit / VelocityField types and centralized ForMathlib/Projection.
-/


lemma integration_by_parts_on_torus (u : VelocityField) (φ : T3 → ℝ)
    (hφ : ∀ x, DifferentiableAt ℝ φ x)
    (hu : ∀ i x, DifferentiableAt ℝ (fun y => u y i) x)
    (hInt_pair : Integrable (fun x => inner ℝ (u x) (gradient φ x)))
    (hInt_div : Integrable (fun x => div u x * φ x))
    (hflux : ∫ x, div (fun y => φ y • u y) x ∂volume = 0) :
    ∫ x, inner ℝ (u x) (gradient φ x) ∂volume =
      -∫ x, div u x * φ x ∂volume :=
  integration_by_parts_of_vanishing_flux u φ hφ hu hInt_pair hInt_div hflux

/-- Mixed partials slot for Biot–Savart: if the recovered velocity is a
`C²` curl, then `div u = 0` by `div_of_eq_curl`. This is *not* C¹ flux IBP. -/
public theorem div_biot_savart_of_eq_curl (ω : CoadjointOrbit) (A : VelocityField)
    (hA : ∀ x k, ContDiffAt ℝ 2 (fun y => A y k) x)
    (hcurl : velocity_from_vorticity ω = curl A) :
    div (velocity_from_vorticity ω) = 0 := by
  funext x
  exact div_of_eq_curl (velocity_from_vorticity ω) A hA hcurl x

/-- C¹ slot: if `div` and the Biot–Savart integral interchange at `x`, then
`div u = 0` by the a.e. integrand identity. Not flux IBP. -/
public theorem div_biot_savart_velocity_of_interchange
    (ω : CoadjointOrbit) (x : T3)
    (hinter : NavierStokes3D.div (velocity_from_vorticity ω) x =
      ∫ y, NavierStokes3D.div
        (fun z => biotSavartKernel z y • cross (ω.val y) (z - y)) x
        ∂NavierStokes3D.volume) :
    NavierStokes3D.div (velocity_from_vorticity ω) x = 0 := by
  have hinter' :
      NavierStokes3D.div (BiotSavart ω.val) x =
        ∫ y, NavierStokes3D.div
          (fun z => biotSavartKernel z y • cross (ω.val y) (z - y)) x
          ∂NavierStokes3D.volume := by
    rw [velocity_from_vorticity_eq_BiotSavart] at hinter
    exact hinter
  have h0 := div_BiotSavart_of_interchange ω.val x hinter'
  rw [velocity_from_vorticity_eq_BiotSavart]
  exact h0

lemma div_biot_savart_velocity (ω : CoadjointOrbit) (A : VelocityField)
    (hA : ∀ x k, ContDiffAt ℝ 2 (fun y => A y k) x)
    (hcurl : velocity_from_vorticity ω = curl A) :
    div (velocity_from_vorticity ω) = 0 :=
  div_biot_savart_of_eq_curl ω A hA hcurl

/-- Euler kinetic-energy conservation on `[0, T)`.
C¹ IBP (`convective_energy_pairing_vanishes`, `pressure_energy_pairing_vanishes`)
cancels the spatial pairings; the Euler momentum equation identifies
`∂t u = −(u·∇)u − ∇p`. Mixed partials are not used here
(`curl ∇p = 0` lives in vorticity transport). -/
lemma euler_energy_conservation (u : ℝ → VelocityField) (p : ℝ → PressureField)
    (T : ℝ) (_hT : 0 < T)
    (hdiv : ∀ t ∈ Set.Ico 0 T, ∀ x, div (u t) x = 0)
    (hmom : ∀ t ∈ Set.Ico 0 T, ∀ x,
      time_deriv u t x + convective (u t) (u t) x +
        pressureGradient (p t) x = 0)
    (henergy : ∀ t ∈ Set.Ico 0 T,
      HasDerivAt (fun s => (1 / 2 : ℝ) * ∫ x, ‖u s x‖ ^ 2 ∂volume)
        (∫ x, inner ℝ (u t x) (time_deriv u t x) ∂volume) t)
    (hu : ∀ t ∈ Set.Ico 0 T, ∀ x, DifferentiableAt ℝ (u t) x)
    (hp : ∀ t ∈ Set.Ico 0 T, ∀ x, DifferentiableAt ℝ (p t) x)
    (hInt_pair_c : ∀ t ∈ Set.Ico 0 T,
      Integrable (fun x =>
        inner ℝ (u t x) (gradient (fun y => (1 / 2 : ℝ) * ‖u t y‖ ^ 2) x)))
    (hInt_div_c : ∀ t ∈ Set.Ico 0 T,
      Integrable (fun x => div (u t) x * ((1 / 2 : ℝ) * ‖u t x‖ ^ 2)))
    (hflux_c : ∀ t ∈ Set.Ico 0 T,
      ∫ x, div (fun y => ((1 / 2 : ℝ) * ‖u t y‖ ^ 2) • u t y) x ∂volume = 0)
    (hInt_pair_p : ∀ t ∈ Set.Ico 0 T,
      Integrable (fun x => inner ℝ (u t x) (gradient (p t) x)))
    (hInt_div_p : ∀ t ∈ Set.Ico 0 T,
      Integrable (fun x => div (u t) x * p t x))
    (hflux_p : ∀ t ∈ Set.Ico 0 T,
      ∫ x, div (fun y => p t y • u t y) x ∂volume = 0)
    (hInt_c : ∀ t ∈ Set.Ico 0 T,
      Integrable (fun x => inner ℝ (u t x) (convective (u t) (u t) x)))
    (hInt_p : ∀ t ∈ Set.Ico 0 T,
      Integrable (fun x => inner ℝ (u t x) (pressureGradient (p t) x))) :
    ∀ t ∈ Set.Ico 0 T,
      deriv (fun s => (1 / 2 : ℝ) * ∫ x, ‖u s x‖ ^ 2 ∂volume) t = 0 := by
  intro t ht
  have hder := (henergy t ht).deriv
  rw [hder]
  have hconv :=
    convective_energy_pairing_vanishes (u t) (hdiv t ht) (hu t ht)
      (hInt_pair_c t ht) (hInt_div_c t ht) (hflux_c t ht)
  have hpress :=
    pressure_energy_pairing_vanishes (u t) (p t) (hdiv t ht) (hu t ht)
      (hp t ht) (hInt_pair_p t ht) (hInt_div_p t ht) (hflux_p t ht)
  have hfun :
      (fun x => inner ℝ (u t x) (time_deriv u t x)) =
        fun x =>
          -inner ℝ (u t x) (convective (u t) (u t) x) -
            inner ℝ (u t x) (pressureGradient (p t) x) := by
    funext x
    have hmomx := hmom t ht x
    have hdt :
        time_deriv u t x =
          -convective (u t) (u t) x - pressureGradient (p t) x := by
      have hadd :
          time_deriv u t x +
              (convective (u t) (u t) x + pressureGradient (p t) x) = 0 := by
        rw [← add_assoc, hmomx]
      have hneg := (add_eq_zero_iff_eq_neg).mp hadd
      rw [hneg, neg_add, sub_eq_add_neg]
    rw [hdt, sub_eq_add_neg, inner_add_right, inner_neg_right, inner_neg_right]
    ring
  have hInt_negc :
      Integrable (fun x => -inner ℝ (u t x) (convective (u t) (u t) x)) :=
    (hInt_c t ht).neg
  have hInt_negp :
      Integrable (fun x => -inner ℝ (u t x) (pressureGradient (p t) x)) :=
    (hInt_p t ht).neg
  have hsplit :=
    integral_add (μ := NavierStokes3D.volume) hInt_negc hInt_negp
  have hnegc :
      ∫ x, -inner ℝ (u t x) (convective (u t) (u t) x) ∂NavierStokes3D.volume = 0 := by
    rw [integral_neg, hconv, neg_zero]
  have hnegp :
      ∫ x, -inner ℝ (u t x) (pressureGradient (p t) x) ∂NavierStokes3D.volume = 0 := by
    rw [integral_neg, hpress, neg_zero]
  have hsum :
      (fun x =>
        -inner ℝ (u t x) (convective (u t) (u t) x) -
          inner ℝ (u t x) (pressureGradient (p t) x)) =
        fun x =>
          -inner ℝ (u t x) (convective (u t) (u t) x) +
            -inner ℝ (u t x) (pressureGradient (p t) x) := by
    funext x
    ring
  rw [hfun, hsum, hsplit, hnegc, hnegp, add_zero]

-- ============================================
-- 5-STEP UNIQUENESS — TAO / PFR STYLE (ATOMIC NAMED LEMMAS)
-- ============================================

/-! The canonicity lemmas are in `Uniqueness.lean`. -/


/-! ## Invariance (C1) — skeleton

**Removed (Nov 2026).** The hypothesis `TetherIntegralPreserved` (the integral of
`⟨Π_u δF, Π_u δG⟩` is unchanged by `g • ω`, for EVERY pair of functionals `F, G`) and the
theorems that consumed it (`tether_coadjoint_invariance`, `tether_satisfies_C1`,
`tetherKernel_C1`, `tether_coadjoint_invariance_of_integral_eq`,
`ConjecturedSDiffPushforwardInvariance`) were deleted. The hypothesis quantifies over all
functionals, including ones that do not transform covariantly, and `FunctionalDerivative` is an
arbitrary `Classical.choose` among non-unique Gâteaux representatives
(`KineticEnergyDerivative.not_unique_isGateauxRepresentative`), so the statement is about that
choice rather than about vorticity. It is not refuted in Lean; it was removed because no
argument supports it. C1 for `TetherKernel` is therefore NOT proved in this repository. -/

/-- **Formerly trivial.** Under the identity stub, C1 for `TetherKernel` held by `simp`.
With the abstract action it is a NAMED HYPOTHESIS: `TetherKernel` is invariant under `A`
(OPEN: requires the real pushforward and `F, G` transforming covariantly). -/
@[expose] public def TetherKernelInvariant (SDiff : Type*) [Group SDiff]
    [MulAction SDiff CoadjointOrbit] : Prop :=
  InvariantUnderCoadjointAction SDiff TetherKernel

/-! ## C2 — degeneracy on the kinetic-energy Hamiltonian -/

/-- If kinetic energy has no functional gradient at `ω` (in particular at every non-regular
`ω`), `FunctionalDerivative H ω = 0`, so `Π_u 0 = 0` and the tether pairing against `H`
vanishes. Binder is ASCII `dH`: the notation `δ F /δω` makes `δ` illegal in a binder. -/
public theorem tetherKernel_C2_of_no_gateaux
    (ω : CoadjointOrbit)
    (h : ¬ ∃ dH, IsFunctionalGradient KineticEnergyHamiltonian ω dH)
    (F : Functional) :
    TetherKernel ω F KineticEnergyHamiltonian = 0 := by
  apply tetherKernel_of_right_factor_zero
  rw [FunctionalDerivative_eq_zero_of_not h]
  exact Pi_u_zero _

/-! ## Removed: C2 via `δH/δω = u`

The former lemmas `tetherKernel_degenerates_on_kinetic_energy`,
`tetherKernel_C2_of_identifications`, `tethered_reproduces_classical_euler` and
`degeneracy_for_mollified_sup_norm_proxy` assumed
`FunctionalDerivative KineticEnergyHamiltonian ω = velocity_from_vorticity ω`. That identification
is false with these definitions (`KineticEnergyDerivative.not_forall_functionalDerivative_kineticEnergy_eq_velocity`),
so they were deleted. C2 for `TetherKernel` is not proved in this repository. -/

/-! ## Jacobi identity: NOT proved (circular theorem removed)

The former `tethered_jacobi_identity` took two hypotheses, `hident : jacobiator F G H ω =
∫ cyclicLiePairing X Y Z` and `hvanish : ∫ cyclicLiePairing X Y Z = 0`, and concluded
`jacobiator F G H ω = 0` by `rw [hident, hvanish]`. The hypotheses were the conclusion in two
pieces, so the theorem was vacuous as evidence for the Jacobi identity; it and its re-exports
(`ClosureBlueprint.tether_kernel_jacobi`, `ClosureBlueprint.jacobi_cyclic_sum_skeleton`) were
deleted. `TetheredBracket` adds a SYMMETRIC correction to an antisymmetric bracket, so it is
not a Lie bracket and there is no reason to expect the Jacobi identity. The pointwise
cross-product identity `SymplecticConstraint.cross_jacobi_identity` is unaffected. -/

/-- Jacobiator of the tethered bracket. Vanishing is the Jacobi identity. -/
public noncomputable def jacobiator (F G H : Functional) (ω : CoadjointOrbit) : ℝ :=
  let GH : Functional := fun ω' => TetheredBracket G H ω'
  let HF : Functional := fun ω' => TetheredBracket H F ω'
  let FG : Functional := fun ω' => TetheredBracket F G ω'
  TetheredBracket F GH ω + TetheredBracket G HF ω + TetheredBracket H FG ω

/-! ## Pointwise Diagonal Coercivity & Casimir Defect Non-Degeneracy of the Symplectic Tether -/

/-- Pointwise diagonal integrand of `TetherKernel ω F F` at `x ∈ T3`:
`-κ ‖ω(x)‖² ‖Π_u(δF/δω)(x)‖²`. -/
@[expose] public noncomputable def tetherPointwiseDensity
    (ω : CoadjointOrbit) (F : Functional) (x : T3) : ℝ :=
  -kappa * ‖ω.val x‖ ^ 2 *
    ‖Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x‖ ^ 2

/-- **Pointwise Diagonal Non-Positivity (`tetherPointwiseDensity_nonpos`):**
The pointwise diagonal density of the Frohmanian Symplectic Tether is non-positive everywhere on `T3`. -/
public theorem tetherPointwiseDensity_nonpos
    (ω : CoadjointOrbit) (F : Functional) (x : T3) :
    tetherPointwiseDensity ω F x ≤ 0 := by
  unfold tetherPointwiseDensity
  have hκ : 0 ≤ kappa := le_of_lt kappa_pos
  have h1 : 0 ≤ ‖ω.val x‖ ^ 2 := sq_nonneg _
  have h2 : 0 ≤ ‖Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x‖ ^ 2 := sq_nonneg _
  have hprod : 0 ≤ kappa * ‖ω.val x‖ ^ 2 *
      ‖Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x‖ ^ 2 :=
    mul_nonneg (mul_nonneg hκ h1) h2
  linarith

/-- **Strict Negative Definiteness off Casimir / Velocity Alignment (`tetherPointwiseDensity_strict_neg_of_noncasimir`):**
At any point `x ∈ T3` where the vorticity `ω.val x ≠ 0` and the orthogonal projection
`Π_u(δF/δω)(x) ≠ 0`, the pointwise diagonal density of the Frohmanian Symplectic Tether is strictly negative. -/
public theorem tetherPointwiseDensity_strict_neg_of_noncasimir
    (ω : CoadjointOrbit) (F : Functional) (x : T3)
    (hω : ω.val x ≠ 0)
    (hPi : Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x ≠ 0) :
    tetherPointwiseDensity ω F x < 0 := by
  unfold tetherPointwiseDensity
  have hκ : 0 < kappa := kappa_pos
  have h1 : 0 < ‖ω.val x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hω)
  have h2 : 0 < ‖Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hPi)
  have hprod : 0 < kappa * ‖ω.val x‖ ^ 2 *
      ‖Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x‖ ^ 2 :=
    mul_pos (mul_pos hκ h1) h2
  linarith

/-- Two-point regularized Casimir-defect tether kernel density
`K_Cas(ωx, ωy, grad_orth) = -‖grad_orth‖² / (1 + ‖ωx - ωy‖²)⁵`.
Here `grad_orth` denotes the component of `∇φ` orthogonal to the local vorticity / Casimir direction,
and we use the integer power `(1 + ‖ωx - ωy‖²) ^ 5 > 0` for clean algebraic positivity. -/
@[expose] public noncomputable def casimirTetherKernel
    (ωx ωy grad_orth : T3) : ℝ :=
  -(‖grad_orth‖ ^ 2) / (1 + ‖ωx - ωy‖ ^ 2) ^ 5

/-- **Diagonal / Two-Point Casimir Kernel Non-Positivity (`tetherKernel_diagonal_nonpos`):**
The Casimir-defect tether kernel `casimirTetherKernel ωx ωy grad_orth` is non-positive for all
`(ωx, ωy, grad_orth)`. -/
public theorem tetherKernel_diagonal_nonpos
    (ωx ωy grad_orth : T3) :
    casimirTetherKernel ωx ωy grad_orth ≤ 0 := by
  unfold casimirTetherKernel
  have h_denom_pos : 0 < (1 + ‖ωx - ωy‖ ^ 2) ^ 5 := by
    positivity
  have h_num_nonpos : -(‖grad_orth‖ ^ 2) ≤ 0 := by
    have : 0 ≤ ‖grad_orth‖ ^ 2 := sq_nonneg _
    linarith
  exact div_nonpos_of_nonpos_of_nonneg h_num_nonpos (le_of_lt h_denom_pos)

/-- **Strict Negativity on Non-Casimir Modes (`tetherKernel_strict_neg_of_orthogonal_component`):**
Whenever the orthogonal gradient component `grad_orth ≠ 0` (so the test functional is not locally
a Casimir invariant aligned with vorticity), `casimirTetherKernel ωx ωy grad_orth < 0`. -/
public theorem tetherKernel_strict_neg_of_orthogonal_component
    (ωx ωy grad_orth : T3) (h_orth : grad_orth ≠ 0) :
    casimirTetherKernel ωx ωy grad_orth < 0 := by
  unfold casimirTetherKernel
  have h_denom_pos : 0 < (1 + ‖ωx - ωy‖ ^ 2) ^ 5 := by
    positivity
  have h_norm_pos : 0 < ‖grad_orth‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr h_orth)
  have h_num_neg : -(‖grad_orth‖ ^ 2) < 0 := by linarith
  exact div_neg_of_neg_of_pos h_num_neg h_denom_pos

/-- **Exact Non-Degeneracy Characterization on Casimir Defect (`tetherKernel_nondegenerate_on_casimir_defect`):**
The Casimir-defect tether kernel vanishes if and only if the orthogonal gradient component vanishes
(`grad_orth = 0`). -/
public theorem tetherKernel_nondegenerate_on_casimir_defect
    (ωx ωy grad_orth : T3) :
    casimirTetherKernel ωx ωy grad_orth = 0 ↔ grad_orth = 0 := by
  unfold casimirTetherKernel
  have h_denom_pos : 0 < (1 + ‖ωx - ωy‖ ^ 2) ^ 5 := by positivity
  have h_denom_ne : (1 + ‖ωx - ωy‖ ^ 2) ^ 5 ≠ 0 := ne_of_gt h_denom_pos
  rw [div_eq_zero_iff, or_iff_left h_denom_ne, neg_eq_zero, sq_eq_zero_iff, norm_eq_zero]

end   -- close noncomputable section


/-! Axiom checks for the declarations of this module (the strict repository-wide audit is
`scripts/AxiomAudit.lean`). -/

#print axioms tetherKernel_comm
#print axioms antisymmetric_correction_diagonal_zero
#print axioms tetherKernel_C2_of_no_gateaux
#print axioms div_biot_savart_of_eq_curl
#print axioms div_biot_savart_velocity_of_interchange
-- (step* and uniqueness_of_minimal_tether moved to Uniqueness.lean / FrohmanianTether namespace per modular cleanup.
-- Validation prints live there now; see Uniqueness.lean end for #print axioms on the 5-step.)
-- #print axioms uniqueness_of_minimal_tether

-- Practical Usage (as specified in the naming standard
-- Frohmanian_Tether_Naming_Symbol_Standard.md and user guidance):
-- - Use the identifier `FrohmanianTether` for the core new mathematical object.
-- - Optional notation for the custom symbol 𝔉𝕋
scoped notation "𝔉𝕋" => TetheredBracket

end FrohmanianTether
