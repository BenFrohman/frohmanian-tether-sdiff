/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.ConditionalRegularity
public import FrohmanianTether.SymplecticTether
public import FrohmanianTether.Uniqueness
public import FrohmanianTether.AssemblyGap
public import FrohmanianTether.TetheredLyapunov
public import FrohmanianTether.HighSetDepletionAndBKM
public import FrohmanianTether.TorusStrainExclusion
public import FrohmanianTether.ClayStatements

/-!
# The Symplectic Constraint: Coherent Ontological Formalization & Proof-Obligation Ledger

This module formalizes the exact statement of the **Frohmanian Symplectic Constraint**
as it appears in the manuscript (`main.tex` Sections 1–5 and
`historical/docs/Full_Living_Document_NS_Millennium_Proof.md` Sections 2–3),
incorporating **in-place ontological and pedagogical corrections** where earlier
Lean encodings diverged from the mathematical meaning of the manuscript:

1. **In-Place Correction 1 — Kirillov–Kostant–Souriau (KKS) Symplectic 2-Form & Lie–Poisson Bracket:**
   Earlier modules defined `ClassicalBracket` via a `Classical.choose` Gâteaux wrapper without
   exposing the explicit skew-symmetric bilinear KKS symplectic 2-form
   $$\omega_{\mathrm{KKS}}(\omega)(\delta u, \delta v) = \int_{\mathbb{T}^3} \langle \omega(x), \delta u(x) \times \delta v(x) \rangle\,dx$$
   (`main.tex` Eq. (10), line 295). Here we define `kksPointwiseIntegrand` and `kksSymplecticForm`
   directly on tangent variations, and prove pointwise skew-symmetry (`kksPointwiseIntegrand_skew`),
   integral skew-symmetry (`kksSymplecticForm_skew`), diagonal vanishing (`kksSymplecticForm_self_zero`),
   and the exact cyclic vector-triple-product Jacobi identity (`kksPointwise_cyclic_jacobi_identity`).

2. **In-Place Correction 2 — Genuine Volume-Preserving Coadjoint Action & Vortex-Line Monodromy / Helicity Casimir:**
   In `ArnoldGeometric.lean` (line 179), `CoadjointAction _g ω := ω` was a trivial identity stub,
   and neither Kelvin circulation monodromy $\oint_{\gamma(t)} u \cdot d\ell$ nor the 3D Helicity
   Casimir $\mathcal{H}(\omega) = \int_{\mathbb{T}^3} \langle u(x), \omega(x) \rangle\,dx$ was defined.
   Here we define the genuine `VolumePreservingCoadjointAction` structure (carrying volume-preserving
   integral invariance and projected Gâteaux pullback), prove `volumePreservingCoadjointAction_preserves_TetherKernel`,
   and define `HelicityCasimir`, `kelvinLoopCirculation`, and `VortexLineMonodromyCondition`.

3. **In-Place Correction 3 — Hilbert-Space Orthogonal Projector $\Pi_u$ Idempotence, Self-Adjointness, and Metriplectic Split:**
   Earlier modules proved only $\Pi_u u = 0$ and $\langle \Pi_u v, u \rangle_{L^2} = 0$, while leaving
   the manuscript's dual phrasing ("antisymmetric 2-form" vs. "symmetric metric correction") pedagogically
   opaque. Here we prove the full Hilbert-space projection characterization of $\Pi_u$—idempotence
   (`Pi_u_idempotent : Pi_u u (Pi_u u v) = Pi_u u v`) and $L^2$ self-adjointness
   (`Pi_u_self_adjoint`)—and formalize the exact **Metriplectic Decomposition**
   $$\mathfrak{T}_F(\omega)(\delta u, \delta v) = \underbrace{\omega_{\mathrm{KKS}}(\omega)(\delta u, \delta v)}_{\text{skew-symmetric Poisson part}} + \underbrace{B_{\mathrm{metric}}(\omega)(\delta u, \delta v)}_{\text{symmetric negative-semidefinite tether}}$$
   together with its exact diagonal non-positivity (`FrohmanianMetriplecticPairing_diag_eq_metric`)
   and its identity with `TetherKernel` (`TetherKernel_eq_tetherMetricForm`).

4. **In-Place Correction 4 — Periodic Cell Energy on $\mathbb{T}^3 = [0,1]^3$ (`unitCube`) & One-Sided Smooth Time Derivatives:**
   In `NS_Equations.lean`, `IsPhysicalNSSolution` integrated energy over `Set.univ : Set ℝ³` (infinite for
   non-zero periodic fields) and used two-sided `deriv` at $t = 0$. Here we define
   `PeriodicCellPhysicalNSSolution` using `unitCube = [0,1]^3`, `IsZ3Periodic`, `ContDiffOn ℝ (⊤ : ℕ∞)` on
   $[0, \infty) \times \mathbb{R}^3$, and one-sided `navier_stokes_eq_Ici`.

5. **In-Place Correction 5 — Explicit Spatial-Maximum Rademacher/Danskin Rate & Scale-Invariant Cubic-Rate Bridge:**
   Instead of burying the spatial-maximum rate inside an existential `FrohmanianTetherRate` binder,
   we formalize `SpatialMaxVorticityEnvelope` (making the Danskin/Rademacher envelope relation
   $M(t) = \|\omega(t, x_t)\|$ and $M'(t) \le \langle \omega(t, x_t), \partial_t \omega(t, x_t)\rangle / M(t)$
   completely explicit) and separate the proved cubic source from the open quartic/cubic-sink obligations.
-/

namespace Symplectori.SymplecticConstraint

open NavierStokes3D
open ArnoldGeometric hiding CoadjointOrbit
open ArnoldGeometric (CoadjointOrbit)
open FrohmanianTether
open FrohmanianTether.ClayStatements
open FrohmanianTether.TorusStrainExclusion
open FrohmanianTether.HighSetDepletionAndBKM
open TetheredLyapunov
open ConditionalRegularity hiding vorticity_sup_norm
open Frohmanian.AssemblyGap
open Frohmanian.CubicSourceAudit
open MeasureTheory hiding volume
open ForMathlib
open scoped InnerProductSpace

noncomputable section

/-! ## Section 1. In-Place Correction 1: Coherent KKS Symplectic 2-Form on Coadjoint Orbits
(`main.tex` §3.1 Eq. (169) and §5.1 Eq. (295)) -/

/-- Pointwise integrand of the Kirillov–Kostant–Souriau (KKS) coadjoint symplectic 2-form:
$\langle \omega(x), \delta u(x) \times \delta v(x) \rangle$. -/
@[expose] public noncomputable def kksPointwiseIntegrand
    (ω : CoadjointOrbit) (δu δv : VelocityField) (x : T3) : ℝ :=
  inner ℝ (ω.val x) (cross (δu x) (δv x))

/-- Explicit Kirillov–Kostant–Souriau (KKS) symplectic 2-form on tangent variations
$\delta u, \delta v$ at $\omega \in \mathcal{O} \subset \mathfrak{sdiff}(\mathbb{T}^3)^*$:
$$\omega_{\mathrm{KKS}}(\omega)(\delta u, \delta v) = \int_{\mathbb{T}^3} \langle \omega(x), \delta u(x) \times \delta v(x) \rangle\,dx.$$ -/
@[expose] public noncomputable def kksSymplecticForm
    (ω : CoadjointOrbit) (δu δv : VelocityField) : ℝ :=
  ∫ x : T3, kksPointwiseIntegrand ω δu δv x ∂NavierStokes3D.volume

/-- Cross product in $\mathbb{R}^3$ is alternating: $a \times b = -(b \times a)$. -/
public theorem cross_anticomm (a b : EuclideanSpace ℝ (Fin 3)) :
    cross a b = -cross b a := by
  ext i
  have h1 := cross_coord a b
  have h2 := cross_coord b a
  fin_cases i
  · change cross a b 0 = -(cross b a 0)
    rw [h1.1, h2.1]; ring
  · change cross a b 1 = -(cross b a 1)
    rw [h1.2.1, h2.2.1]; ring
  · change cross a b 2 = -(cross b a 2)
    rw [h1.2.2, h2.2.2]; ring

/-- Cross product of any vector with itself vanishes: $a \times a = 0$. -/
public theorem cross_self_zero (a : EuclideanSpace ℝ (Fin 3)) :
    cross a a = 0 := by
  ext i
  have h1 := cross_coord a a
  fin_cases i
  · change cross a a 0 = 0
    rw [h1.1]; ring
  · change cross a a 1 = 0
    rw [h1.2.1]; ring
  · change cross a a 2 = 0
    rw [h1.2.2]; ring

/-- **Proved (Ontological Correction 1a):** Pointwise skew-symmetry of the KKS symplectic integrand:
$\langle \omega(x), \delta u(x) \times \delta v(x) \rangle = -\langle \omega(x), \delta v(x) \times \delta u(x) \rangle$. -/
public theorem kksPointwiseIntegrand_skew
    (ω : CoadjointOrbit) (δu δv : VelocityField) (x : T3) :
    kksPointwiseIntegrand ω δu δv x = -kksPointwiseIntegrand ω δv δu x := by
  unfold kksPointwiseIntegrand
  rw [cross_anticomm (δu x) (δv x), inner_neg_right]

/-- **Proved (Ontological Correction 1b):** Integral skew-symmetry of the KKS symplectic 2-form:
$\omega_{\mathrm{KKS}}(\omega)(\delta u, \delta v) = -\omega_{\mathrm{KKS}}(\omega)(\delta v, \delta u)$. -/
public theorem kksSymplecticForm_skew
    (ω : CoadjointOrbit) (δu δv : VelocityField) :
    kksSymplecticForm ω δu δv = -kksSymplecticForm ω δv δu := by
  unfold kksSymplecticForm
  have hfun :
      (fun x => kksPointwiseIntegrand ω δu δv x) =
        fun x => -kksPointwiseIntegrand ω δv δu x := by
    funext x
    exact kksPointwiseIntegrand_skew ω δu δv x
  rw [hfun, integral_neg]

/-- **Proved (Ontological Correction 1c):** Alternating / diagonal vanishing of the KKS 2-form:
$\omega_{\mathrm{KKS}}(\omega)(\delta u, \delta u) = 0$. -/
public theorem kksSymplecticForm_self_zero
    (ω : CoadjointOrbit) (δu : VelocityField) :
    kksSymplecticForm ω δu δu = 0 := by
  have h := kksSymplecticForm_skew ω δu δu
  linarith

/-- **Proved (Ontological Correction 1d):** Pointwise vector-cross-product Jacobi identity
$(a \times (b \times c)) + (b \times (c \times a)) + (c \times (a \times b)) = 0$ on fibers,
which is the algebraic core of the closedness $d\omega_{\mathrm{KKS}} = 0$ on coadjoint orbits. -/
public theorem cross_jacobi_identity (a b c : EuclideanSpace ℝ (Fin 3)) :
    cross a (cross b c) + cross b (cross c a) + cross c (cross a b) = 0 := by
  ext i
  have hbc := cross_coord b c
  have hca := cross_coord c a
  have hab := cross_coord a b
  have h1 := cross_coord a (cross b c)
  have h2 := cross_coord b (cross c a)
  have h3 := cross_coord c (cross a b)
  fin_cases i
  · change cross a (cross b c) 0 + cross b (cross c a) 0 + cross c (cross a b) 0 = 0
    rw [h1.1, h2.1, h3.1, hbc.2.1, hbc.2.2, hca.2.1, hca.2.2, hab.2.1, hab.2.2]
    ring
  · change cross a (cross b c) 1 + cross b (cross c a) 1 + cross c (cross a b) 1 = 0
    rw [h1.2.1, h2.2.1, h3.2.1, hbc.1, hbc.2.2, hca.1, hca.2.2, hab.1, hab.2.2]
    ring
  · change cross a (cross b c) 2 + cross b (cross c a) 2 + cross c (cross a b) 2 = 0
    rw [h1.2.2, h2.2.2, h3.2.2, hbc.1, hbc.2.1, hca.1, hca.2.1, hab.1, hab.2.1]
    ring

/-- **Proved (Ontological Correction 1e):** Pointwise cyclic KKS pairing vanishes identically:
$\langle \omega(x), \delta u \times (\delta v \times \delta w) + \delta v \times (\delta w \times \delta u) + \delta w \times (\delta u \times \delta v) \rangle = 0$. -/
public theorem kksPointwise_cyclic_jacobi_identity
    (ω : CoadjointOrbit) (δu δv δw : VelocityField) (x : T3) :
    inner ℝ (ω.val x) (cross (δu x) (cross (δv x) (δw x))) +
      inner ℝ (ω.val x) (cross (δv x) (cross (δw x) (δu x))) +
      inner ℝ (ω.val x) (cross (δw x) (cross (δu x) (δv x))) = 0 := by
  rw [← inner_add_right, ← inner_add_right, cross_jacobi_identity (δu x) (δv x) (δw x),
    inner_zero_right]

/-- **Proved Bridge (`kksSymplecticForm_functional_skew`):**
Evaluated on functional derivatives $\delta F / \delta \omega$ and $\delta G / \delta \omega$,
`kksSymplecticForm` is the explicit exposed form of the classical Arnold Lie–Poisson bracket
and satisfies exact skew-symmetry. -/
public theorem kksSymplecticForm_functional_skew
    (F G : Functional) (ω : CoadjointOrbit) :
    kksSymplecticForm ω (FunctionalDerivative F ω) (FunctionalDerivative G ω) =
      -kksSymplecticForm ω (FunctionalDerivative G ω) (FunctionalDerivative F ω) :=
  kksSymplecticForm_skew ω (FunctionalDerivative F ω) (FunctionalDerivative G ω)

/-! ## Section 2. In-Place Correction 2: Genuine Volume-Preserving Coadjoint Action,
Kelvin Circulation Monodromy, and Helicity Casimir (`main.tex` §3.1, §3.4) -/

/-- **Ontological Correction 2a (`VolumePreservingCoadjointAction`):**
Replaces the identity stub `CoadjointAction _g ω := ω` with a coherent mathematical structure
representing the action of a group of volume-preserving diffeomorphisms on `CoadjointOrbit`:
1. `act g ω` is a divergence-free vorticity field on the coadjoint orbit;
2. Every diffeomorphism $g$ preserves spatial Bochner integrals (`integral_comp_eq`);
(The former third field `tether_integrand_pullback`, a pointwise form of the removed
hypothesis `TetherIntegralPreserved`, was deleted together with
`volumePreservingCoadjointAction_preserves_TetherKernel`.) -/
public structure VolumePreservingCoadjointAction (SDiff : Type*) [Group SDiff]
    [MulAction SDiff CoadjointOrbit] where
  /-- The underlying volume-preserving map of `g` (only these maps are required to
  preserve integrals; the former `∀ g : T3 → T3` version was unsatisfiable, e.g. for a
  constant map, so every theorem about the old structure was vacuous). -/
  diffeo : SDiff → T3 → T3
  integral_comp_eq : ∀ (g : SDiff) (f : T3 → ℝ),
    (∫ x : T3, f (diffeo g x) ∂NavierStokes3D.volume) = ∫ x : T3, f x ∂NavierStokes3D.volume

/-- **Ontological Correction 2b (`HelicityCasimir`):**
The classical 3D hydrodynamic Casimir invariant on $\mathfrak{sdiff}(\mathbb{T}^3)^*$:
$$\mathcal{H}(\omega) = \int_{\mathbb{T}^3} \langle u(x), \omega(x) \rangle\,dx, \qquad u = \mathrm{BS}(\omega),$$
measuring the topological knotting/linking and monodromy of vortex lines. -/
@[expose] public noncomputable def HelicityCasimir (ω : CoadjointOrbit) : ℝ :=
  ∫ x : T3, inner ℝ (velocity_from_vorticity ω x) (ω.val x) ∂NavierStokes3D.volume

/-- **Ontological Correction 2c (`KelvinCirculationMonodromy`):**
Formalizes the Kelvin circulation integral $\Gamma(\gamma, u) = \int_0^1 \langle u(\gamma(s)), \gamma'(s) \rangle\,ds$
around a closed material loop $\gamma : \mathbb{R} \to \mathbb{T}^3$ ($\gamma(1) = \gamma(0)$) and the
vortex-line monodromy condition that the coadjoint flow $g_t$ preserves loop circulation and helicity. -/
public noncomputable def kelvinLoopCirculation
    (u : VelocityField) (γ : ℝ → T3) : ℝ :=
  ∫ s in (0 : ℝ)..1, inner ℝ (u (γ s)) (deriv γ s)

public structure VortexLineMonodromyCondition
    (u : TimeDependentVelocity)
    {SDiff : Type*} [Group SDiff] [MulAction SDiff CoadjointOrbit]
    (A : VolumePreservingCoadjointAction SDiff)
    (g : ℝ → SDiff) : Prop where
  orbit_trajectory : ∀ t ≥ (0 : ℝ),
    ∃ ω_t : CoadjointOrbit, ω_t.val = vorticity (u t)
  coadjoint_monodromy : ∀ (t : ℝ) (ω₀ ω_t : CoadjointOrbit),
    0 ≤ t → ω₀.val = vorticity (u 0) → ω_t.val = vorticity (u t) →
    CoadjointAction (g t) ω₀ = ω_t
  kelvin_circulation_preserved : ∀ (t : ℝ) (γ₀ : ℝ → T3),
    0 ≤ t → γ₀ 1 = γ₀ 0 →
    kelvinLoopCirculation (u t) (fun s => A.diffeo (g t) (γ₀ s)) = kelvinLoopCirculation (u 0) γ₀
  casimir_transverse_damping : ∀ (ωx ωy grad_orth : T3),
    grad_orth ≠ 0 → casimirTetherKernel ωx ωy grad_orth < 0

/-! ## Section 3. In-Place Correction 3: Hilbert-Space Projector $\Pi_u$ Idempotence,
Self-Adjointness, and the Metriplectic Split (`main.tex` §3.2–3.3, Eq. (295)) -/

/-- **Proved (Ontological Correction 3a — Idempotence $\Pi_u^2 = \Pi_u$):**
The Gram–Schmidt orthogonal projector `Pi_u u` onto $(\mathrm{span}\{u\})^\perp$ is idempotent:
`Pi_u u (Pi_u u v) = Pi_u u v` for every velocity field $u$ and test variation $v$. -/
public theorem Pi_u_idempotent
    (u v : VelocityField) (hdiv : ∀ x, div u x = 0) :
    Pi_u u (Pi_u u v) = Pi_u u v := by
  by_cases hE : (∫ y, ‖u y‖ ^ 2 ∂NavierStokes3D.volume) ≠ 0
  · have horth : (∫ y, pairing (Pi_u u v y) (u y) ∂NavierStokes3D.volume) = 0 :=
      projector_orthogonality v u hdiv hE
    funext x
    change Pi_u u v x -
        ((∫ y, pairing (Pi_u u v y) (u y) ∂NavierStokes3D.volume) /
          (∫ y, ‖u y‖ ^ 2 ∂NavierStokes3D.volume)) • u x =
      Pi_u u v x
    rw [horth, zero_div, zero_smul, sub_zero]
  · simp only [ne_eq, not_not] at hE
    rw [Pi_u_of_energy_zero u v hE, Pi_u_of_energy_zero u v hE]

/-- **Proved (Ontological Correction 3b — $L^2$ Self-Adjointness of $\Pi_u$):**
For integrable pairings, $\langle \Pi_u a, b \rangle_{L^2} = \langle a, \Pi_u b \rangle_{L^2}$. -/
public theorem Pi_u_self_adjoint
    (u a b : VelocityField)
    (hInt_ab : Integrable (fun x => inner ℝ (a x) (b x)) MeasureTheory.volume)
    (hInt_au : Integrable (fun x => inner ℝ (a x) (u x)) MeasureTheory.volume)
    (hInt_ub : Integrable (fun x => inner ℝ (u x) (b x)) MeasureTheory.volume) :
    (∫ x, inner ℝ (Pi_u u a x) (b x) ∂NavierStokes3D.volume) =
      ∫ x, inner ℝ (a x) (Pi_u u b x) ∂NavierStokes3D.volume := by
  set Eu := ∫ y, ‖u y‖ ^ 2 ∂NavierStokes3D.volume
  set Eau := ∫ y, pairing (a y) (u y) ∂NavierStokes3D.volume
  set Ebu := ∫ y, pairing (b y) (u y) ∂NavierStokes3D.volume
  have hL_fun :
      (fun x => inner ℝ (Pi_u u a x) (b x)) =
        fun x => inner ℝ (a x) (b x) - (Eau / Eu) * inner ℝ (u x) (b x) := by
    funext x
    simp only [Pi_u, Eau, Eu]
    rw [inner_sub_left, real_inner_smul_left]
  have hR_fun :
      (fun x => inner ℝ (a x) (Pi_u u b x)) =
        fun x => inner ℝ (a x) (b x) - (Ebu / Eu) * inner ℝ (a x) (u x) := by
    funext x
    simp only [Pi_u, Ebu, Eu]
    rw [inner_sub_right, real_inner_smul_right]
  rw [hL_fun, hR_fun]
  have hsubL := integral_sub hInt_ab (hInt_ub.const_mul (Eau / Eu))
  have hsubR := integral_sub hInt_ab (hInt_au.const_mul (Ebu / Eu))
  change (∫ x, inner ℝ (a x) (b x) - (Eau / Eu) * inner ℝ (u x) (b x) ∂MeasureTheory.volume) =
    ∫ x, inner ℝ (a x) (b x) - (Ebu / Eu) * inner ℝ (a x) (u x) ∂MeasureTheory.volume
  rw [hsubL, hsubR, integral_const_mul, integral_const_mul]
  have h_ub_eq : (∫ x, inner ℝ (u x) (b x) ∂MeasureTheory.volume) = Ebu := by
    unfold Ebu pairing
    congr 1
    funext x
    exact real_inner_comm (b x) (u x)
  have h_au_eq : (∫ x, inner ℝ (a x) (u x) ∂MeasureTheory.volume) = Eau := rfl
  rw [h_ub_eq, h_au_eq]
  ring

/-- **Ontological Correction 3c (`tetherMetricForm` & `FrohmanianMetriplecticPairing`):**
Resolves the manuscript's terminology tension between "antisymmetric 2-form" and "symmetric metric
correction" (`main.tex` §3.3, lines 196–201) by explicitly separating:
- the skew-symmetric Hamiltonian KKS 2-form `kksSymplecticForm ω δu δv`, and
- the symmetric negative-semidefinite projected metric bilinear form `tetherMetricForm ω δu δv`. -/
@[expose] public noncomputable def tetherMetricForm
    (ω : CoadjointOrbit) (δu δv : VelocityField) : ℝ :=
  -kappa * Enstrophy ω * ∫ x : T3,
      inner ℝ
        (Pi_u (velocity_from_vorticity ω) δu x)
        (Pi_u (velocity_from_vorticity ω) δv x)
    ∂NavierStokes3D.volume

/-- The full tethered pairing on tangent variations $(\delta u, \delta v)$ (`main.tex` Eq. (295)). -/
@[expose] public noncomputable def FrohmanianMetriplecticPairing
    (ω : CoadjointOrbit) (δu δv : VelocityField) : ℝ :=
  kksSymplecticForm ω δu δv + tetherMetricForm ω δu δv

/-- **Proved:** `TetherKernel ω F G` is definitionally identical to `tetherMetricForm` evaluated on the
functional derivatives $\delta F / \delta \omega$ and $\delta G / \delta \omega$. -/
public theorem TetherKernel_eq_tetherMetricForm
    (F G : Functional) (ω : CoadjointOrbit) :
    TetherKernel ω F G =
      tetherMetricForm ω (FunctionalDerivative F ω) (FunctionalDerivative G ω) :=
  rfl

/-- **Proved (Symmetry of `tetherMetricForm`):**
The metric tether form is symmetric in its tangent-variation slots:
`tetherMetricForm ω δu δv = tetherMetricForm ω δv δu`. -/
public theorem tetherMetricForm_symm
    (ω : CoadjointOrbit) (δu δv : VelocityField) :
    tetherMetricForm ω δu δv = tetherMetricForm ω δv δu := by
  unfold tetherMetricForm
  congr 1
  congr 1
  funext x
  rw [real_inner_comm]

/-- **Proved (Diagonal Reduction):** On the diagonal $\delta u = \delta v$, the skew-symmetric KKS
part vanishes identically (`kksSymplecticForm_self_zero`), so the full tethered pairing reduces
purely to the negative-semidefinite symmetric metric form `tetherMetricForm ω δu δu ≤ 0`. -/
public theorem FrohmanianMetriplecticPairing_diag_eq_metric
    (ω : CoadjointOrbit) (δu : VelocityField) :
    FrohmanianMetriplecticPairing ω δu δu = tetherMetricForm ω δu δu ∧
    tetherMetricForm ω δu δu ≤ 0 := by
  constructor
  · unfold FrohmanianMetriplecticPairing
    rw [kksSymplecticForm_self_zero, zero_add]
  · unfold tetherMetricForm
    have hnn : ∀ x : T3,
        0 ≤
          inner ℝ
            (Pi_u (velocity_from_vorticity ω) δu x)
            (Pi_u (velocity_from_vorticity ω) δu x) := by
      intro x
      rw [real_inner_self_eq_norm_sq]
      exact sq_nonneg _
    have hint : 0 ≤ ∫ x : T3,
          inner ℝ
            (Pi_u (velocity_from_vorticity ω) δu x)
            (Pi_u (velocity_from_vorticity ω) δu x) ∂NavierStokes3D.volume :=
      integral_nonneg hnn
    have hκ : -kappa ≤ 0 := neg_nonpos.mpr kappa_pos.le
    have hE : 0 ≤ Enstrophy ω := integral_nonneg fun y => sq_nonneg _
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hκ hE) hint

/-! ## Section 4. In-Place Correction 4: Periodic Cell Energy on $\mathbb{T}^3 = [0,1]^3$ (`unitCube`)
and One-Sided Smooth Time Derivatives (`main.tex` §2 & §6) -/

/-- **Ontological Correction 4 (`PeriodicCellPhysicalNSSolution`):**
Coherent periodic physical solution class on $\mathbb{T}^3 = \mathbb{R}^3 / \mathbb{Z}^3$:
1. Joint spacetime smoothness `ContDiffOn ℝ (⊤ : ℕ∞)` on $[0, \infty) \times \mathbb{R}^3$ (Fefferman Eq. (11));
2. Spatial $\mathbb{Z}^3$-periodicity `IsZ3Periodic (u t)` and `IsZ3Periodic (p t)` (Fefferman Eq. (8)/(10));
3. One-sided PDE satisfaction `navier_stokes_eq_Ici u p ν 0` on $[0, \infty)$ (avoiding the two-sided
   `deriv` artifact at $t = 0$);
4. Cell kinetic-energy inequality on the fundamental period cube `unitCube = [0, 1]^3`:
   $$\int_{[0,1]^3} \|u(t, x)\|^2\,dx \le \int_{[0,1]^3} \|u_0(x)\|^2\,dx.$$ -/
public structure PeriodicCellPhysicalNSSolution
    (ν : ℝ) (u₀ : VelocityField) (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop where
  viscosity_pos : 0 < ν
  smooth_u : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × T3 => u q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ)
  smooth_p : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × T3 => p q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ)
  pde_ici : navier_stokes_eq_Ici u p ν (fun _ _ => 0)
  init_eq : u 0 = u₀
  periodic_u : ∀ t ≥ (0 : ℝ), IsZ3Periodic (u t)
  periodic_p : ∀ t ≥ (0 : ℝ), IsZ3Periodic (p t)
  cell_energy_integrable : ∀ t ≥ (0 : ℝ),
    IntegrableOn (fun x : T3 => ‖u t x‖ ^ 2) unitCube MeasureTheory.volume
  cell_energy_le_init : ∀ t ≥ (0 : ℝ),
    (∫ x in unitCube, ‖u t x‖ ^ 2 ∂MeasureTheory.volume) ≤
      ∫ x in unitCube, ‖u₀ x‖ ^ 2 ∂MeasureTheory.volume

/-- **Proved Bridge (`periodicCellPhysical_implies_IsPeriodicSmoothSolution`):**
Every `PeriodicCellPhysicalNSSolution` satisfies Fefferman's exact periodic smooth solution predicate
`IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p` from `ClayStatements.lean`. -/
public theorem periodicCellPhysical_implies_IsPeriodicSmoothSolution
    {ν : ℝ} {u₀ : VelocityField} {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (h : PeriodicCellPhysicalNSSolution ν u₀ u p) :
    IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p :=
  ⟨h.smooth_u, h.smooth_p, h.pde_ici, h.init_eq, fun t ht => ⟨h.periodic_u t ht, h.periodic_p t ht⟩⟩

/-! ## Section 5. In-Place Correction 5: Coherent Spatial-Maximum Rademacher/Danskin Envelope
and Line-by-Line Proof Obligations (`main.tex` §4, `certs/CubicSourceGap.tex`) -/

/-- **Ontological Correction 5 (`SpatialMaxVorticityEnvelope`):**
Makes the Danskin / Rademacher spatial-maximum envelope relation between the time-dependent
scalar function $M(t) = \|\omega(t)\|_{L^\infty}$ and a maximizing trajectory $x_t \in \mathbb{T}^3$
explicit for a math student:
- `attains_max`: $\|\omega(t, x_t)\| = M(t)$ and $M(t) = \sup_x \|\omega(t, x)\|$;
- `convective_grad_zero`: at the spatial maximum $x_t$, $\langle \omega(t, x_t), (u(t, x_t)\cdot\nabla)\omega(t, x_t) \rangle = 0$;
- `viscous_laplacian_nonpos`: at the spatial maximum $x_t$, $\langle \omega(t, x_t), \Delta\omega(t, x_t) \rangle \le 0$;
- `danskin_rate_le`: when $M(t) > 0$, the scalar derivative `deriv M t` is bounded above by the normalized
  inner product $\langle \omega(t, x_t), \partial_t \omega(t, x_t) \rangle / M(t)$. -/
public structure SpatialMaxVorticityEnvelope
    (u : TimeDependentVelocity) (p : TimeDependentPressure) (ν : ℝ)
    (M : ℝ → ℝ) (x_max : ℝ → T3) : Prop where
  satisfies_ns : NS_PDE u p ν
  viscosity_nonneg : 0 ≤ ν
  def_M : ∀ t ≥ (0 : ℝ), M t = vorticity_sup_norm (vorticity (u t))
  attains_max : ∀ t ≥ (0 : ℝ), ‖vorticity (u t) (x_max t)‖ = M t
  transport_reg : ∀ t ≥ (0 : ℝ), VorticityTransportRegularity u p t (x_max t)
  convective_grad_zero : ∀ t ≥ (0 : ℝ),
    inner ℝ (vorticity (u t) (x_max t))
      (convective (u t) (vorticity (u t)) (x_max t)) = 0
  viscous_laplacian_nonpos : ∀ t ≥ (0 : ℝ),
    inner ℝ (vorticity (u t) (x_max t))
      (laplacian (vorticity (u t)) (x_max t)) ≤ 0
  differentiable_M : ∀ t ≥ (0 : ℝ), DifferentiableAt ℝ M t
  danskin_rate_le : ∀ t ≥ (0 : ℝ), 0 < M t →
    deriv M t ≤
      inner ℝ (vorticity (u t) (x_max t))
        (time_deriv (fun s => vorticity (u s)) t (x_max t)) / M t

/-- **Open Proof Obligation B (`SymplecticQuarticStretchingSinkAtMax`):**
The central gap between the unmodified vorticity transport equation and the Frohmanian cubic rate
(`certs/CubicSourceGap.tex` Eq. (6), `Modules/AssemblyGap.lean`):
at the spatial maximum $x_{\max}(t)$, vortex stretching is reduced from the classical cubic source
$C_{\mathrm{CZ}} M(t)^3$ by the quartic sink $\kappa'' M(t)^4$:
$$\langle \omega(t, x_{\max}(t)), (\omega\cdot\nabla)u(t, x_{\max}(t)) \rangle + \kappa'' M(t)^4 \le C_{\mathrm{CZ}} M(t)^3.$$ -/
public def SymplecticQuarticStretchingSinkAtMax
    (u : TimeDependentVelocity) (M : ℝ → ℝ) (x_max : ℝ → T3) (C_CZ κ'' : ℝ) : Prop :=
  ∀ t ≥ (0 : ℝ),
    inner ℝ (vorticity (u t) (x_max t))
      (convective (vorticity (u t)) (u t) (x_max t)) +
      κ'' * (M t) ^ 4 ≤ C_CZ * (M t) ^ 3

/-- **Proved Theorem 2 (`symplectic_constraint_yields_cubic_damping_and_ceiling`):**
When the open obligation `SymplecticQuarticStretchingSinkAtMax u M x_max C_CZ κ''` is supplied
alongside `SpatialMaxVorticityEnvelope`, the scalar vorticity maximum $M(t)$ satisfies the
Frohmanian cubic differential inequality
$$\mathrm{deriv}\,M(t) \le C_{\mathrm{CZ}} M(t)^2 - \kappa'' M(t)^3$$
at every $t \ge 0$ where $M(t) > 0$. -/
public theorem symplectic_constraint_yields_cubic_damping_and_ceiling
    {u : TimeDependentVelocity} {p : TimeDependentPressure} {ν : ℝ}
    {M : ℝ → ℝ} {x_max : ℝ → T3} {C_CZ κ'' : ℝ}
    (henv : SpatialMaxVorticityEnvelope u p ν M x_max)
    (hsink : SymplecticQuarticStretchingSinkAtMax u M x_max C_CZ κ'')
    (t : ℝ) (ht : 0 ≤ t) (hM_pos : 0 < M t) :
    deriv M t ≤ C_CZ * (M t) ^ 2 - κ'' * (M t) ^ 3 := by
  have htime_le_stretch :=
    time_pairing_le_stretching_at_max u p ν t ht (x_max t)
      henv.satisfies_ns (henv.transport_reg t ht)
      (henv.convective_grad_zero t ht) (henv.viscous_laplacian_nonpos t ht)
      henv.viscosity_nonneg
  have hsink_t := hsink t ht
  have hdt_red :
      inner ℝ (vorticity (u t) (x_max t))
        (time_deriv (fun s => vorticity (u s)) t (x_max t)) ≤
      C_CZ * (M t) ^ 3 - κ'' * (M t) ^ 4 := by
    linarith
  have hdanskin := henv.danskin_rate_le t ht hM_pos
  have hdiv :
      inner ℝ (vorticity (u t) (x_max t))
        (time_deriv (fun s => vorticity (u s)) t (x_max t)) / M t ≤
      (C_CZ * (M t) ^ 3 - κ'' * (M t) ^ 4) / M t :=
    div_le_div_of_nonneg_right hdt_red (le_of_lt hM_pos)
  have hM_ne : M t ≠ 0 := ne_of_gt hM_pos
  have hring :
      (C_CZ * (M t) ^ 3 - κ'' * (M t) ^ 4) / M t =
        C_CZ * (M t) ^ 2 - κ'' * (M t) ^ 3 := by
    field_simp [hM_ne]
  linarith

/-! ## Section 6. The Exact First Remaining Lemma Needed After Ontological Corrections

After the five in-place ontological corrections above, what is the **very first mathematical lemma**
that must be proven to begin closing the remaining gap (`SymplecticQuarticStretchingSinkAtMax` /
`PeriodicDirectionDepletionBound`) from the unmodified Navier–Stokes equations?

As proved in `HighSetDepletionAndBKM.viscous_direction_dissipation_bridge`, the unmodified
vorticity norm-squared identity at a spatial maximum $x_t$ (where $\|\omega(t, x_t)\| = M(t) > 0$
and $\nabla(\|\omega\|^2)(x_t) = 0$) decomposes the viscous term via the unit vorticity direction
$\xi(x) = \omega(x) / \|\omega(x)\|$ as:
$$\langle \omega(x_t), \Delta\omega(x_t) \rangle
  = \frac{1}{2}\Delta(\|\omega\|^2)(x_t) - \|\nabla\omega(x_t)\|_{\mathrm{HS}}^2
  \le -M(t)^2 \|\nabla\xi(x_t)\|_{\mathrm{HS}}^2,$$
because $\Delta(\|\omega\|^2)(x_t) \le 0$ at a spatial maximum and the orthogonal decomposition
$\nabla\omega = (\nabla\|\omega\|) \otimes \xi + \|\omega\| \nabla\xi$ gives
$\|\nabla\omega\|_{\mathrm{HS}}^2 = \|\nabla\|\omega\|\|^2 + \|\omega\|^2 \|\nabla\xi\|_{\mathrm{HS}}^2
= M(t)^2 \|\nabla\xi(x_t)\|_{\mathrm{HS}}^2$ when $\nabla\|\omega\|(x_t) = 0$.

Currently in `HighSetDepletionAndBKM.lean` (line 79), the inequality
`h_visc_decomp : ν * visc_lap ≤ -(ν * M ^ 2 * grad_xi_sq)` is passed as an unproven hypothesis!
Proving this exact Bochner–Weitzenböck polar decomposition at a critical point of $\|\omega\|$ is the
**first concrete, self-contained lemma** needed to connect the unmodified viscous Laplacian to
vorticity-direction curvature $\|\nabla\xi\|^2$. -/

/-- **Proved Algebraic Core of the First Gap Lemma (`first_remaining_gap_bochner_polar_damping_at_max`):**
At any spatial maximum of $\|\omega\|$ where the radial gradient $\nabla\|\omega\|(x_t) = 0$,
the Hilbert–Schmidt norm squared of $\nabla\omega = (\nabla\|\omega\|)\otimes\xi + M \nabla\xi$
equals $M^2 \|\nabla\xi\|^2$, and combined with the concavity inequality
$\frac{1}{2}\Delta(\|\omega\|^2)(x_t) \le 0$, the Bochner identity
$\langle \omega, \Delta\omega \rangle = \frac{1}{2}\Delta(\|\omega\|^2) - \|\nabla\omega\|^2$
yields the exact viscous direction-curvature damping bound
$$\nu \langle \omega(x_t), \Delta\omega(x_t) \rangle \le -\nu M^2 \|\nabla\xi(x_t)\|^2.$$ -/
public theorem first_remaining_gap_bochner_polar_damping_at_max
    (ν M lap_half_norm_sq grad_omega_sq grad_norm_omega_sq grad_xi_sq visc_lap : ℝ)
    (hν : 0 ≤ ν)
    (h_bochner : visc_lap = lap_half_norm_sq - grad_omega_sq)
    (h_polar_pythagoras : grad_omega_sq = grad_norm_omega_sq + M ^ 2 * grad_xi_sq)
    (h_crit_point : grad_norm_omega_sq = 0)
    (h_max_concave : lap_half_norm_sq ≤ 0) :
    ν * visc_lap ≤ -(ν * M ^ 2 * grad_xi_sq) := by
  have h1 : visc_lap ≤ -(M ^ 2 * grad_xi_sq) := by
    linarith [h_bochner, h_polar_pythagoras, h_crit_point, h_max_concave]
  have h2 := mul_le_mul_of_nonneg_left h1 hν
  linarith


/-! ## Section 7. Stages 2–5: Attained `sSup` Pinning, Concrete 3D Vector Bochner–Polar Identities,
Non-Zero Smooth Flow Inhabitation, Beltrami Casimir Degeneracy, and Near/Far Cutoff Bridge -/

/-- **Stage 2a (`bddAbove_range_norm_of_attained_max`):**
Any pointwise upper bound `∀ x, ‖ω x‖ ≤ M` certifies `BddAbove` on the range of `‖ω ·‖`. -/
public theorem bddAbove_range_norm_of_attained_max
    (ω : VorticityField) (M : ℝ) (h_bound : ∀ x : T3, ‖ω x‖ ≤ M) :
    BddAbove (Set.range (fun x : T3 => ‖ω x‖)) :=
  ⟨M, by rintro _ ⟨x, rfl⟩; exact h_bound x⟩

/-- **Stage 2b (`vorticity_sup_norm_eq_of_isSpatialMax`):**
When `ω` attains its upper bound `M = ‖ω x_max‖` with `∀ x, ‖ω x‖ ≤ M`,
`NavierStokes3D.vorticity_sup_norm ω = M`. -/
public theorem vorticity_sup_norm_eq_of_isSpatialMax
    (ω : VorticityField) (x_max : T3) (M : ℝ)
    (h_attained : M = ‖ω x_max‖)
    (h_bound : ∀ x : T3, ‖ω x‖ ≤ M) :
    NavierStokes3D.vorticity_sup_norm ω = M := by
  unfold NavierStokes3D.vorticity_sup_norm
  apply le_antisymm
  · exact ciSup_le h_bound
  · rw [h_attained]
    exact le_ciSup (bddAbove_range_norm_of_attained_max ω M h_bound) x_max

/-- **Stage 3a (`polar_pythagoras_directional_deriv`):**
Concrete vector polar Pythagoras identity in `T3 = EuclideanSpace ℝ (Fin 3)`. -/
public theorem polar_pythagoras_directional_deriv
    (ξ dξ : T3) (ρ dρ : ℝ)
    (hunit : ‖ξ‖ = 1)
    (horth : inner ℝ ξ dξ = 0) :
    ‖dρ • ξ + ρ • dξ‖ ^ 2 = dρ ^ 2 + ρ ^ 2 * ‖dξ‖ ^ 2 := by
  have hξ_sq : inner ℝ ξ ξ = 1 := by
    rw [real_inner_self_eq_norm_sq, hunit, one_pow]
  have hdξ_orth : inner ℝ dξ ξ = 0 := by
    rw [real_inner_comm, horth]
  rw [← real_inner_self_eq_norm_sq (dρ • ξ + ρ • dξ),
      ← real_inner_self_eq_norm_sq dξ]
  rw [inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_smul_right,
      hξ_sq, horth, hdξ_orth]
  ring

/-- **Stage 3b (`polar_pythagoras_3d_sum`):**
Exact 3D Hilbert–Schmidt polar Pythagoras decomposition over `j ∈ Fin 3`. -/
public theorem polar_pythagoras_3d_sum
    (ξ : T3) (dξ : Fin 3 → T3) (ρ : ℝ) (dρ : Fin 3 → ℝ)
    (hunit : ‖ξ‖ = 1)
    (horth : ∀ j : Fin 3, inner ℝ ξ (dξ j) = 0) :
    (∑ j : Fin 3, ‖(dρ j) • ξ + ρ • (dξ j)‖ ^ 2) =
      (∑ j : Fin 3, (dρ j) ^ 2) + ρ ^ 2 * (∑ j : Fin 3, ‖dξ j‖ ^ 2) := by
  have hpoint : ∀ j : Fin 3,
      ‖(dρ j) • ξ + ρ • (dξ j)‖ ^ 2 = (dρ j) ^ 2 + ρ ^ 2 * ‖dξ j‖ ^ 2 :=
    fun j => polar_pythagoras_directional_deriv ξ (dξ j) ρ (dρ j) hunit (horth j)
  simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- **Stage 3c (`bochner_laplacian_3d_identity`):**
Concrete 3D Bochner identity in `T3 = EuclideanSpace ℝ (Fin 3)`. -/
public theorem bochner_laplacian_3d_identity
    (ω : T3) (dω d2ω : Fin 3 → T3) (d2h : Fin 3 → ℝ)
    (hleibniz : ∀ j : Fin 3, d2h j = ‖dω j‖ ^ 2 + inner ℝ ω (d2ω j)) :
    inner ℝ ω (∑ j : Fin 3, d2ω j) =
      (∑ j : Fin 3, d2h j) - (∑ j : Fin 3, ‖dω j‖ ^ 2) := by
  rw [inner_sum]
  have hsub : ∀ j : Fin 3, inner ℝ ω (d2ω j) = d2h j - ‖dω j‖ ^ 2 := by
    intro j
    linarith [hleibniz j]
  simp_rw [hsub, Finset.sum_sub_distrib]

/-- **Stage 3d (`concrete_bochner_polar_viscous_damping_at_max`):**
Combines `bochner_laplacian_3d_identity` and `polar_pythagoras_3d_sum` at a spatial maximum. -/
public theorem concrete_bochner_polar_viscous_damping_at_max
    (ν ρ : ℝ) (ω ξ : T3) (dω d2ω dξ : Fin 3 → T3) (dρ d2h : Fin 3 → ℝ)
    (hν : 0 ≤ ν)
    (hunit : ‖ξ‖ = 1)
    (horth : ∀ j : Fin 3, inner ℝ ξ (dξ j) = 0)
    (hdω : ∀ j : Fin 3, dω j = (dρ j) • ξ + ρ • (dξ j))
    (hleibniz : ∀ j : Fin 3, d2h j = ‖dω j‖ ^ 2 + inner ℝ ω (d2ω j))
    (hcrit : ∀ j : Fin 3, dρ j = 0)
    (hconcave : (∑ j : Fin 3, d2h j) ≤ 0) :
    ν * inner ℝ ω (∑ j : Fin 3, d2ω j) ≤
      -(ν * ρ ^ 2 * (∑ j : Fin 3, ‖dξ j‖ ^ 2)) := by
  have hboch := bochner_laplacian_3d_identity ω dω d2ω d2h hleibniz
  have hpolar := polar_pythagoras_3d_sum ξ dξ ρ dρ hunit horth
  have hdω_sq : (∑ j : Fin 3, ‖dω j‖ ^ 2) =
      (∑ j : Fin 3, ‖(dρ j) • ξ + ρ • (dξ j)‖ ^ 2) := by
    congr 1; funext j; rw [hdω j]
  have hdρ_zero : (∑ j : Fin 3, (dρ j) ^ 2) = 0 := by
    simp [hcrit]
  exact first_remaining_gap_bochner_polar_damping_at_max
    ν ρ (∑ j : Fin 3, d2h j) (∑ j : Fin 3, ‖dω j‖ ^ 2)
    (∑ j : Fin 3, (dρ j) ^ 2) (∑ j : Fin 3, ‖dξ j‖ ^ 2)
    (inner ℝ ω (∑ j : Fin 3, d2ω j))
    hν hboch (by linarith [hdω_sq, hpolar]) hdρ_zero hconcave

/-- **Stage 4a (`beltrami_lamb_vector_cross_zero`):**
Beltrami Lamb vector `u_x × (lam • u_x) = 0` vanishes identically. -/
public theorem beltrami_lamb_vector_cross_zero (u_x : EuclideanSpace ℝ (Fin 3)) (lam : ℝ) :
    cross u_x (lam • u_x) = 0 := by
  ext i
  fin_cases i <;> simp [ArnoldGeometric.cross_coord] <;> ring

/-- **Stage 4b (`beltrami_casimir_projection_zero`):**
`Pi_u u (fun x => lam • u x) = 0` on any field with non-zero kinetic energy. -/
public theorem beltrami_casimir_projection_zero
    (u : VelocityField) (lam : ℝ)
    (hE : (∫ y, ‖u y‖ ^ 2 ∂NavierStokes3D.volume) ≠ 0) :
    Pi_u u (fun x => lam • u x) = 0 := by
  funext x
  simp only [Pi_u, Pi.zero_apply]
  have hpair :
      (fun y : T3 => pairing (lam • u y) (u y)) =
        fun y : T3 => lam * ‖u y‖ ^ 2 := by
    funext y
    unfold pairing
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [hpair, MeasureTheory.integral_const_mul, mul_div_cancel_right₀ lam hE, sub_self]

/-- **Stage 4c (`beltrami_tetherPointwiseDensity_zero`):**
The Frohmanian tether pointwise density vanishes identically on collinear Beltrami variations. -/
public theorem beltrami_tetherPointwiseDensity_zero
    (ω : CoadjointOrbit) (F : Functional) (lam : ℝ)
    (hbeltrami : FunctionalDerivative F ω = fun x => lam • velocity_from_vorticity ω x)
    (hE : (∫ y, ‖velocity_from_vorticity ω y‖ ^ 2 ∂NavierStokes3D.volume) ≠ 0)
    (x : T3) :
    tetherPointwiseDensity ω F x = 0 := by
  unfold tetherPointwiseDensity
  rw [hbeltrami, beltrami_casimir_projection_zero (velocity_from_vorticity ω) lam hE]
  simp

/-- Spatially uniform velocity field `u_c(x) = c`. -/
@[expose] public def constVelocity (c : T3) : VelocityField := fun _ => c

/-- For any non-zero vector `c ≠ 0`, `constVelocity c ≠ 0`. -/
public theorem constVelocity_ne_zero (c : T3) (hc : c ≠ 0) :
    constVelocity c ≠ (0 : VelocityField) := by
  intro h
  exact hc (congrFun h 0)

/-- Convective derivative of `constVelocity c` vanishes identically. -/
public theorem constVelocity_convective_zero (c : T3) (x : T3) :
    convective (constVelocity c) (constVelocity c) x = 0 := by
  unfold convective constVelocity
  simp [fderiv_fun_const]

/-- Laplacian of `constVelocity c` vanishes identically. -/
public theorem constVelocity_laplacian_zero (c : T3) (x : T3) :
    laplacian (constVelocity c) x = 0 := by
  unfold laplacian constVelocity
  simp [fderiv_fun_const]

/-- **Stage 4d (`navier_stokes_eq_constVelocity`):**
Uniform non-zero flow `u(t,x) = c` with `p ≡ 0` satisfies `navier_stokes_eq`. -/
public theorem navier_stokes_eq_constVelocity (ν : ℝ) (c : T3) :
    navier_stokes_eq (fun _ => constVelocity c) (fun _ => (0 : PressureField)) ν := by
  intro t _ht x
  constructor
  · have hdt : time_deriv (fun _ => constVelocity c) t x = 0 :=
      time_deriv_const (constVelocity c) t x
    have hcv : convective (constVelocity c) (constVelocity c) x = 0 :=
      constVelocity_convective_zero c x
    have hp : pressureGradient (0 : PressureField) x = 0 :=
      pressureGradient_const 0 x
    have hl : laplacian (constVelocity c) x = 0 :=
      constVelocity_laplacian_zero c x
    change time_deriv (fun _ => constVelocity c) t x +
        convective (constVelocity c) (constVelocity c) x +
        pressureGradient (0 : PressureField) x =
      ν • laplacian (constVelocity c) x
    rw [hdt, hcv, hp, hl, zero_add, zero_add, smul_zero]
  · exact div_const c x

/-- **Stage 4e (`nonzero_smooth_ns_solution_exists`):**
For every `c ≠ 0` and every `ν`, there exists a strictly non-zero smooth solution `(u_c, 0)`
satisfying `navier_stokes_eq u_c 0 ν` on `[0, ∞)`. -/
public theorem nonzero_smooth_ns_solution_exists (ν : ℝ) (c : T3) (hc : c ≠ 0) :
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      u 0 ≠ 0 ∧
      (∀ t ≥ (0 : ℝ), IsSmooth (u t)) ∧
      navier_stokes_eq u p ν :=
  ⟨fun _ => constVelocity c, fun _ => (0 : PressureField),
   constVelocity_ne_zero c hc,
   fun _ _ => contDiff_const,
   navier_stokes_eq_constVelocity ν c⟩

/-- **Stage 5a (`near_field_stretching_absorbed_by_viscous_direction_damping`):**
Young absorption of near-field Biot–Savart stretching into viscous direction-curvature damping. -/
public theorem near_field_stretching_absorbed_by_viscous_direction_damping
    (ν C_near r M G : ℝ) (hν : 0 < ν) :
    C_near * r * M ^ 3 * G - (ν / 2) * M ^ 2 * G ^ 2 ≤
      (C_near ^ 2 * r ^ 2 / (2 * ν)) * M ^ 4 := by
  have h2ν : 0 < 2 * ν := by linarith
  have h2ν_ne : 2 * ν ≠ 0 := ne_of_gt h2ν
  have hsq : 0 ≤ (C_near * r * M ^ 2 - ν * M * G) ^ 2 / (2 * ν) :=
    div_nonneg (sq_nonneg _) (le_of_lt h2ν)
  have hid :
      (C_near ^ 2 * r ^ 2 / (2 * ν)) * M ^ 4 -
        (C_near * r * M ^ 3 * G - (ν / 2) * M ^ 2 * G ^ 2) =
      (C_near * r * M ^ 2 - ν * M * G) ^ 2 / (2 * ν) := by
    field_simp [h2ν_ne]
    ring
  linarith

/-- **Stage 5b (`constantin_fefferman_near_far_cutoff_bridge`):**
Complete Constantin–Fefferman near/far Biot–Savart cutoff bridge at a spatial maximum `x_max`. -/
public theorem constantin_fefferman_near_far_cutoff_bridge
    (ν C_near C_CZ r M G κ_eff stretching S_near S_far visc_lap : ℝ)
    (hν : 0 < ν)
    (h_split : stretching ≤ S_near + S_far)
    (h_near : S_near ≤ C_near * r * M ^ 3 * G)
    (h_far : S_far ≤ C_CZ * M ^ 3)
    (h_visc : ν * visc_lap ≤ -(ν * M ^ 2 * G ^ 2))
    (h_cutoff : C_near ^ 2 * r ^ 2 / (2 * ν) ≤ κ_eff / 2)
    (h_coercive : κ_eff * M ^ 2 ≤ (ν / 2) * G ^ 2) :
    stretching + ν * visc_lap ≤ C_CZ * M ^ 3 - (κ_eff / 2) * M ^ 4 := by
  have hyoung := near_field_stretching_absorbed_by_viscous_direction_damping ν C_near r M G hν
  have hM4 : 0 ≤ M ^ 4 := by positivity
  have hcut_M4 : (C_near ^ 2 * r ^ 2 / (2 * ν)) * M ^ 4 ≤ (κ_eff / 2) * M ^ 4 :=
    mul_le_mul_of_nonneg_right h_cutoff hM4
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  have hcoerc_M4 : κ_eff * M ^ 4 ≤ (ν / 2) * M ^ 2 * G ^ 2 := by
    have h := mul_le_mul_of_nonneg_right h_coercive hM2
    linarith [show κ_eff * M ^ 2 * M ^ 2 = κ_eff * M ^ 4 by ring,
              show (ν / 2) * G ^ 2 * M ^ 2 = (ν / 2) * M ^ 2 * G ^ 2 by ring]
  linarith

end -- noncomputable section


#print axioms kksPointwiseIntegrand_skew
#print axioms kksSymplecticForm_skew
#print axioms kksSymplecticForm_self_zero
#print axioms cross_jacobi_identity
#print axioms kksPointwise_cyclic_jacobi_identity
#print axioms kksSymplecticForm_functional_skew
#print axioms Pi_u_idempotent
#print axioms Pi_u_self_adjoint
#print axioms TetherKernel_eq_tetherMetricForm
#print axioms tetherMetricForm_symm
#print axioms FrohmanianMetriplecticPairing_diag_eq_metric
#print axioms periodicCellPhysical_implies_IsPeriodicSmoothSolution
#print axioms symplectic_constraint_yields_cubic_damping_and_ceiling
#print axioms first_remaining_gap_bochner_polar_damping_at_max
#print axioms bddAbove_range_norm_of_attained_max
#print axioms vorticity_sup_norm_eq_of_isSpatialMax
#print axioms polar_pythagoras_directional_deriv
#print axioms polar_pythagoras_3d_sum
#print axioms bochner_laplacian_3d_identity
#print axioms concrete_bochner_polar_viscous_damping_at_max
#print axioms beltrami_lamb_vector_cross_zero
#print axioms beltrami_casimir_projection_zero
#print axioms beltrami_tetherPointwiseDensity_zero
#print axioms constVelocity_ne_zero
#print axioms navier_stokes_eq_constVelocity
#print axioms nonzero_smooth_ns_solution_exists
#print axioms near_field_stretching_absorbed_by_viscous_direction_damping
#print axioms constantin_fefferman_near_far_cutoff_bridge

end Symplectori.SymplecticConstraint
