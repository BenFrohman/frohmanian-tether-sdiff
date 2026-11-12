import Scratch.GradBound

/-! # Kato–Ponce H³ energy inequality for Fefferman-class solutions

Target (the Kato–Ponce conjunct of `R3BKM.KatoMaximalSolution`): there is a
constant `C_k ≥ 0` such that, for every solution `u` in Fefferman's smooth class
on `[0, T)` (`IsFeffermanSolutionOn`) with `‖u(t)‖²_{H³}` finite on `[0, T)`,
at every `s ∈ [0, T)` the map `t ↦ ‖u(t)‖²_{H³}` has a right derivative
`d ≤ C_k ‖∇u(s)‖_∞ ‖u(s)‖²_{H³}`.

The quantities `sobolevEnergy`, `hsSq`, and `gradSup` are exactly those of
`R3BKM` (used by `KatoMaximalSolution`). The argument is the standard one:

* the H³ energy identity, from the momentum equation;
* transport cancellation `∫ ⟨v, (u·∇)v⟩ = 0` when `div u = 0`
  (`transport_pairing_vanishes`, from the library identity
  `transported_energy_pairing_vanishes`);
* the pressure pairing `∫ ⟨v, ∇q⟩ = 0` when `div v = 0`
  (`pressure_pairing_vanishes`);
* viscous dissipation `∫ ⟨v, Δv⟩ ≤ 0` (`inner_laplacian_nonpos`);
* a commutator bound on `∫ ⟨∂^α u, [∂^α, u·∇]u⟩`.

The first four steps are proved, under explicit vanishing-flux / mixed-partial
hypotheses recorded below. The commutator estimate is the remaining analytic
input (`H3CommutatorEstimate`): the Leibniz terms with two factors of order 2
need a Gagliardo–Nirenberg interpolation that is not yet in this repository.
The order-zero commutator vanishes, and the first-order commutator is
identified with `(∂_i u)·∇u` and bounded by `‖∇u‖_∞` directly.

Nothing in this file is a `sorry`, a custom axiom, or an `opaque` trick.
-/

open MeasureTheory hiding volume
open NavierStokes3D FrohmanianTether RepairedTether Set Filter Topology
open scoped ContDiff InnerProductSpace

set_option autoImplicit false

noncomputable section
namespace KatoPonce

open R3BKM

/-! ## Word derivatives and the convective commutator -/

/-- Multi-index (word) derivative `∂_{α 0} ⋯ ∂_{α (k-1)} f`, matching the
summands of `R3BKM.sobolevEnergy`. -/
def wordDeriv (k : ℕ) (α : Fin k → Fin 3) (f : VelocityField) : VelocityField :=
  fun x => iteratedFDeriv ℝ k f x (fun j => EuclideanSpace.single (α j) (1 : ℝ))

/-- Scalar analogue, used for `∂^α p`. -/
def wordDerivScalar (k : ℕ) (α : Fin k → Fin 3) (p : PressureField) : PressureField :=
  fun x => iteratedFDeriv ℝ k p x (fun j => EuclideanSpace.single (α j) (1 : ℝ))

/-- The convective commutator `[∂^α, u·∇] u`. -/
def convectiveCommutator (k : ℕ) (α : Fin k → Fin 3) (u : VelocityField) : VelocityField :=
  fun x => wordDeriv k α (convective u u) x - convective u (wordDeriv k α u) x

/-- One-sided time derivative of a Fefferman-class field at time `s`, as a
spatial field. Matches the momentum equation in `IsFeffermanSolutionOn`. -/
def timeSliceDeriv (u : TimeDependentVelocity) (s : ℝ) : VelocityField :=
  fun x => derivWithin (fun τ => u τ x) (Ici (0 : ℝ)) s

lemma wordDeriv_zero (α : Fin 0 → Fin 3) (f : VelocityField) : wordDeriv 0 α f = f := by
  funext x
  exact iteratedFDeriv_zero_apply _

lemma wordDeriv_one (α : Fin 1 → Fin 3) (f : VelocityField) (x : T3) :
    wordDeriv 1 α f x = (fderiv ℝ f x) (EuclideanSpace.single (α 0) (1 : ℝ)) :=
  iteratedFDeriv_one_apply _

/-- The order-zero commutator vanishes identically. -/
theorem convectiveCommutator_zero (α : Fin 0 → Fin 3) (u : VelocityField) :
    convectiveCommutator 0 α u = 0 := by
  funext x
  simp [convectiveCommutator, wordDeriv_zero]

lemma wordDeriv_add {k : ℕ} (α : Fin k → Fin 3) {f g : VelocityField}
    (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) :
    wordDeriv k α (f + g) = wordDeriv k α f + wordDeriv k α g := by
  funext x
  simp only [wordDeriv, Pi.add_apply]
  exact congrArg (fun L => L (fun j => EuclideanSpace.single (α j) (1 : ℝ)))
    (iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt)

lemma wordDeriv_sub {k : ℕ} (α : Fin k → Fin 3) {f g : VelocityField}
    (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) :
    wordDeriv k α (f - g) = wordDeriv k α f - wordDeriv k α g := by
  funext x
  simp only [wordDeriv, Pi.sub_apply]
  exact congrArg (fun L => L (fun j => EuclideanSpace.single (α j) (1 : ℝ)))
    (iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt)

lemma wordDeriv_const_smul {k : ℕ} (α : Fin k → Fin 3) (c : ℝ) {f : VelocityField}
    (hf : ContDiff ℝ k f) :
    wordDeriv k α (fun x => c • f x) = fun x => c • wordDeriv k α f x := by
  funext x
  simp only [wordDeriv]
  have := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (E := T3)
      (F := EuclideanSpace ℝ (Fin 3)) (f := f) (a := c) (i := k) (x := x) hf.contDiffAt
  exact congrArg (fun L => L (fun j => EuclideanSpace.single (α j) (1 : ℝ))) this

lemma wordDeriv_add3 {k : ℕ} (α : Fin k → Fin 3) {f g h : VelocityField}
    (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) (hh : ContDiff ℝ k h) :
    wordDeriv k α (f + g + h) = wordDeriv k α f + wordDeriv k α g + wordDeriv k α h := by
  have hfg : ContDiff ℝ k (f + g) := hf.add hg
  rw [wordDeriv_add α hfg hh, wordDeriv_add α hf hg]

/-! ## Smoothness of slices and of derived fields -/

lemma contDiff_u_slice {ν T : ℝ} {u₀ : VelocityField}
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hu : IsFeffermanSolutionOn ν T u₀ u p) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    ContDiff ℝ ∞ (u t) :=
  R3BKM.contDiff_slice (g := fun q : T3 × ℝ => u q.2 q.1) hu.1 ht

lemma contDiff_p_slice {ν T : ℝ} {u₀ : VelocityField}
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hu : IsFeffermanSolutionOn ν T u₀ u p) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    ContDiff ℝ ∞ (p t) :=
  R3BKM.contDiff_slice (g := fun q : T3 × ℝ => p q.2 q.1) hu.2.1 ht

lemma div_u_slice {ν T : ℝ} {u₀ : VelocityField}
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hu : IsFeffermanSolutionOn ν T u₀ u p) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (x : T3) :
    div (u t) x = 0 :=
  (hu.2.2.1 t ht x).2

lemma bddAbove_grad_slice {u : VelocityField} (hu : ContDiff ℝ ∞ u)
    (hE : sobolevEnergy 3 u < ⊤) :
    BddAbove (range fun x => ‖fderiv ℝ u x‖) :=
  GradBound.bddAbove_norm_fderiv hu hE

lemma contDiff_of_infty {n : ℕ} {f : VelocityField} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ n f :=
  hf.of_le (by exact_mod_cast le_top)

lemma contDiff_convective {u v : VelocityField}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (convective u v) := by
  unfold convective
  exact (hv.fderiv_right (m := ∞) le_rfl).clm_apply hu

lemma contDiff_pressureGradient {q : PressureField} (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (pressureGradient q) := by
  unfold pressureGradient gradient
  exact (InnerProductSpace.toDual ℝ T3).symm.contDiff.comp
    (hq.fderiv_right (m := ∞) le_rfl)

lemma contDiff_laplacian {f : VelocityField} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (laplacian f) := by
  unfold laplacian
  refine ContDiff.sum (fun i _ => ?_)
  exact (((hf.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const).fderiv_right
    (m := ∞) le_rfl).clm_apply contDiff_const

lemma contDiff_wordDeriv {k : ℕ} (α : Fin k → Fin 3) {f : VelocityField}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (wordDeriv k α f) := by
  unfold wordDeriv
  have h : ContDiff ℝ ∞ (iteratedFDeriv ℝ k f) :=
    hf.iteratedFDeriv_right (by
      rw [show (k : WithTop ℕ∞) = ((k : ℕ∞) : WithTop ℕ∞) from rfl, ← WithTop.coe_add,
        top_add])
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => T3)
      (EuclideanSpace ℝ (Fin 3))
      (fun j => EuclideanSpace.single (α j) (1 : ℝ))).contDiff.comp h

/-! ## Momentum equation as a spatial field identity -/

lemma ns_momentum_field {ν T : ℝ} {u₀ : VelocityField}
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hu : IsFeffermanSolutionOn ν T u₀ u p) {s : ℝ} (hs : s ∈ Ico (0 : ℝ) T) :
    timeSliceDeriv u s + convective (u s) (u s) + pressureGradient (p s) =
      fun x => ν • laplacian (u s) x := by
  funext x
  have h := (hu.2.2.1 s hs x).1
  simpa [timeSliceDeriv, add_zero, Pi.add_apply] using h

/-! ## Transport and pressure cancellation (library wrappers) -/

/-- **Transport cancellation.** If `div u = 0` and the flux of `½|v|² u`
vanishes, then `∫ ⟨v, (u·∇)v⟩ = 0`. This is
`NavierStokes3D.transported_energy_pairing_vanishes`, restated so it can be
applied at every multi-index `v = ∂^α u` in the H³ energy identity. -/
theorem transport_pairing_vanishes
    (u v : VelocityField)
    (hdiv : ∀ x, div u x = 0)
    (hu : ∀ x, DifferentiableAt ℝ u x)
    (hv : ∀ x, DifferentiableAt ℝ v x)
    (hInt_pair : Integrable
      (fun x => inner ℝ (u x) (gradient (fun y => (1 / 2 : ℝ) * ‖v y‖ ^ 2) x)))
    (hInt_div : Integrable
      (fun x => div u x * ((1 / 2 : ℝ) * ‖v x‖ ^ 2)))
    (hflux : ∫ x, div (fun y => ((1 / 2 : ℝ) * ‖v y‖ ^ 2) • u y) x ∂volume = 0) :
    ∫ x, inner ℝ (v x) (convective u v x) ∂volume = 0 :=
  transported_energy_pairing_vanishes u v hdiv hu hv hInt_pair hInt_div hflux

/-- **Pressure pairing.** If `div v = 0` and the flux of `q v` vanishes, then
`∫ ⟨v, ∇q⟩ = 0`. Wrapper for `pressure_energy_pairing_vanishes`. -/
theorem pressure_pairing_vanishes
    (v : VelocityField) (q : PressureField)
    (hdiv : ∀ x, div v x = 0)
    (hv : ∀ x, DifferentiableAt ℝ v x)
    (hq : ∀ x, DifferentiableAt ℝ q x)
    (hInt_pair : Integrable (fun x => inner ℝ (v x) (gradient q x)))
    (hInt_div : Integrable (fun x => div v x * q x))
    (hflux : ∫ x, div (fun y => q y • v y) x ∂volume = 0) :
    ∫ x, inner ℝ (v x) (pressureGradient q x) ∂volume = 0 :=
  pressure_energy_pairing_vanishes v q hdiv hv hq hInt_pair hInt_div hflux

/-! ## Directional integration by parts and viscous dissipation -/

/-- Divergence of a field that is a scalar times a coordinate basis vector:
`div(φ eᵢ) = ∂ᵢ φ`. -/
theorem div_smul_single (φ : T3 → ℝ) (i : Fin 3) (x : T3)
    (hφ : DifferentiableAt ℝ φ x) :
    div (fun y => φ y • EuclideanSpace.single i (1 : ℝ)) x =
      (fderiv ℝ φ x) (EuclideanSpace.single i (1 : ℝ)) := by
  unfold div
  have hcoord : ∀ j,
      (fun y => (φ y • EuclideanSpace.single i (1 : ℝ)) j) =
        fun y => φ y * EuclideanSpace.single i (1 : ℝ) j := by
    intro j; funext y; exact smul_coord (φ y) _ j
  simp_rw [hcoord]
  have hfd : ∀ j,
      fderiv ℝ (fun y => φ y * EuclideanSpace.single i (1 : ℝ) j) x =
        EuclideanSpace.single i (1 : ℝ) j • fderiv ℝ φ x := by
    intro j
    have hc : (fun y => φ y * EuclideanSpace.single i (1 : ℝ) j) =
        fun y => EuclideanSpace.single i (1 : ℝ) j * φ y := by
      funext y; ring
    rw [hc, fderiv_const_mul hφ (EuclideanSpace.single i (1 : ℝ) j)]
  simp_rw [hfd, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hsum :
      (∑ j : Fin 3, EuclideanSpace.single i (1 : ℝ) j *
          (fderiv ℝ φ x) (EuclideanSpace.single j (1 : ℝ))) =
        (fderiv ℝ φ x)
          (∑ j : Fin 3, EuclideanSpace.single i (1 : ℝ) j •
            EuclideanSpace.single j (1 : ℝ)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.map_smul, smul_eq_mul, mul_comm]
  rw [hsum]
  have hbasis : (∑ j : Fin 3, EuclideanSpace.single i (1 : ℝ) j •
      EuclideanSpace.single j (1 : ℝ)) = EuclideanSpace.single i (1 : ℝ) := by
    ext k
    simp [EuclideanSpace.single, Finset.mem_univ]
  rw [hbasis]

/-- Product rule for `div((φψ) eᵢ)`. -/
theorem div_mul_smul_single (φ ψ : T3 → ℝ) (i : Fin 3) (x : T3)
    (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) :
    div (fun y => (φ y * ψ y) • EuclideanSpace.single i (1 : ℝ)) x =
      φ x * (fderiv ℝ ψ x) (EuclideanSpace.single i (1 : ℝ)) +
        ψ x * (fderiv ℝ φ x) (EuclideanSpace.single i (1 : ℝ)) := by
  have hmul : DifferentiableAt ℝ (fun y => φ y * ψ y) x := hφ.mul hψ
  rw [div_smul_single _ i x hmul, fderiv_fun_mul hφ hψ]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Vanishing-flux data for the directional IBP `∫ φ ∂ᵢ ψ = −∫ ψ ∂ᵢ φ`. -/
structure PartialIBP (i : Fin 3) (φ ψ : T3 → ℝ) : Prop where
  differentiable_φ : ∀ x, DifferentiableAt ℝ φ x
  differentiable_ψ : ∀ x, DifferentiableAt ℝ ψ x
  integrable_left :
    Integrable (fun x => φ x * (fderiv ℝ ψ x) (EuclideanSpace.single i (1 : ℝ)))
  integrable_right :
    Integrable (fun x => ψ x * (fderiv ℝ φ x) (EuclideanSpace.single i (1 : ℝ)))
  flux : ∫ x, div (fun y => (φ y * ψ y) • EuclideanSpace.single i (1 : ℝ)) x ∂volume = 0

/-- Directional integration by parts from a vanishing flux of `(φψ) eᵢ`. -/
theorem integral_partial_ibp {i : Fin 3} {φ ψ : T3 → ℝ} (h : PartialIBP i φ ψ) :
    ∫ x, φ x * (fderiv ℝ ψ x) (EuclideanSpace.single i (1 : ℝ)) ∂volume =
      -∫ x, ψ x * (fderiv ℝ φ x) (EuclideanSpace.single i (1 : ℝ)) ∂volume := by
  have hfun :
      (fun x => div (fun y => (φ y * ψ y) • EuclideanSpace.single i (1 : ℝ)) x) =
        fun x => φ x * (fderiv ℝ ψ x) (EuclideanSpace.single i (1 : ℝ)) +
          ψ x * (fderiv ℝ φ x) (EuclideanSpace.single i (1 : ℝ)) := by
    funext x
    exact div_mul_smul_single φ ψ i x (h.differentiable_φ x) (h.differentiable_ψ x)
  have hsum := MeasureTheory.integral_add (μ := volume) h.integrable_left h.integrable_right
  have h0 : ∫ x, φ x * (fderiv ℝ ψ x) (EuclideanSpace.single i (1 : ℝ)) +
      ψ x * (fderiv ℝ φ x) (EuclideanSpace.single i (1 : ℝ)) ∂volume = 0 := by
    rw [← hfun]
    exact h.flux
  linarith [hsum, h0]

/-- Hypotheses needed to conclude `∫ ⟨v, Δv⟩ ≤ 0`.

Added because the identity is integration by parts on each coordinate and
direction, which requires a vanishing flux of `(vⱼ ∂ᵢ vⱼ) eᵢ` at spatial
infinity. That decay is not implied by `IsFeffermanSolutionOn` alone. -/
structure ViscousDissipationIBP (v : VelocityField) : Prop where
  /-- `C²` is the regularity used by `laplacian_coord`. -/
  contDiff2 : ContDiff ℝ 2 v
  partialIBP : ∀ (i j : Fin 3),
    PartialIBP i (fun y => v y j) (fun y => directionalCoord v j i y)
  integrable_inner : Integrable (fun x => inner ℝ (v x) (laplacian v x))

lemma real_inner_eq_mul (x y : ℝ) : inner ℝ x y = x * y := by
  have h1 : inner ℝ (1 : ℝ) (1 : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq]
    simp
  have hy : inner ℝ (1 : ℝ) y = y := by
    have h := real_inner_smul_right (1 : ℝ) (1 : ℝ) y
    have hy1 : y • (1 : ℝ) = y := by simp [smul_eq_mul]
    rw [hy1, h1, mul_one] at h
    exact h
  have hx := real_inner_smul_left (1 : ℝ) y x
  have hx1 : x • (1 : ℝ) = x := by simp [smul_eq_mul]
  rw [hx1, hy] at hx
  exact hx

theorem inner_eq_sum_mul (a b : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ a b = ∑ j : Fin 3, a j * b j := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun j _ => real_inner_eq_mul _ _

/-- **Viscous dissipation.** Under the flux hypotheses in
`ViscousDissipationIBP`, `∫ ⟨v, Δv⟩ = −∑_{i,j} ∫ (∂ᵢ vⱼ)² ≤ 0`. -/
theorem inner_laplacian_nonpos (v : VelocityField) (h : ViscousDissipationIBP v) :
    ∫ x, inner ℝ (v x) (laplacian v x) ∂volume ≤ 0 := by
  have hC2 : ∀ x, ContDiffAt ℝ 2 v x := fun x => h.contDiff2.contDiffAt
  have hcoord : ∀ x j, laplacian v x j =
      ∑ i : Fin 3, (fderiv ℝ (fun y => directionalCoord v j i y) x)
        (EuclideanSpace.single i (1 : ℝ)) :=
    fun x j => laplacian_coord v x j (hC2 x)
  have hinter :
      (fun x => inner ℝ (v x) (laplacian v x)) =
        fun x => ∑ j : Fin 3, ∑ i : Fin 3,
          v x j * (fderiv ℝ (fun y => directionalCoord v j i y) x)
            (EuclideanSpace.single i (1 : ℝ)) := by
    funext x
    rw [inner_eq_sum_mul, Finset.sum_congr rfl fun j _ => ?_]
    rw [hcoord x j, Finset.mul_sum]
  -- Each summand integrates to `-∫ (∂ᵢ vⱼ)²`.
  have hterm : ∀ i j,
      ∫ x, v x j * (fderiv ℝ (fun y => directionalCoord v j i y) x)
        (EuclideanSpace.single i (1 : ℝ)) ∂volume =
        -∫ x, (directionalCoord v j i x) *
          (fderiv ℝ (fun y => v y j) x) (EuclideanSpace.single i (1 : ℝ)) ∂volume :=
    fun i j => integral_partial_ibp (h.partialIBP i j)
  have hident : ∀ i j x,
      (directionalCoord v j i x) *
          (fderiv ℝ (fun y => v y j) x) (EuclideanSpace.single i (1 : ℝ)) =
        (directionalCoord v j i x) ^ 2 := by
    intro i j x
    rw [directionalCoord, sq]
  have hnonpos : ∀ i j,
      ∫ x, v x j * (fderiv ℝ (fun y => directionalCoord v j i y) x)
        (EuclideanSpace.single i (1 : ℝ)) ∂volume ≤ 0 := by
    intro i j
    have hIBP := h.partialIBP i j
    have : ∫ x, (directionalCoord v j i x) *
        (fderiv ℝ (fun y => v y j) x) (EuclideanSpace.single i (1 : ℝ)) ∂volume =
        ∫ x, (directionalCoord v j i x) ^ 2 ∂volume :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => hident i j x)
    have hsq : 0 ≤ ∫ x, (directionalCoord v j i x) ^ 2 ∂volume :=
      MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
    linarith [hterm i j, this, hsq]
  -- The integral of the inner product is the sum of these nonpositive terms,
  -- once we know the double sum is integrable.
  have hint_summand : ∀ i j,
      Integrable (fun x => v x j *
        (fderiv ℝ (fun y => directionalCoord v j i y) x)
          (EuclideanSpace.single i (1 : ℝ))) :=
    fun i j => (h.partialIBP i j).integrable_left
  have hint_inner_j : ∀ j,
      Integrable (fun x => v x j * laplacian v x j) := by
    intro j
    have : (fun x => v x j * laplacian v x j) =
        fun x => ∑ i : Fin 3, v x j *
          (fderiv ℝ (fun y => directionalCoord v j i y) x)
            (EuclideanSpace.single i (1 : ℝ)) := by
      funext x; rw [hcoord x j, Finset.mul_sum]
    rw [this]
    exact integrable_finset_sum _ (fun i _ => hint_summand i j)
  have hinter_int : Integrable
      (fun x => ∑ j : Fin 3, ∑ i : Fin 3,
        v x j * (fderiv ℝ (fun y => directionalCoord v j i y) x)
          (EuclideanSpace.single i (1 : ℝ))) := by
    refine integrable_finset_sum _ (fun j _ => ?_)
    exact integrable_finset_sum _ (fun i _ => hint_summand i j)
  have heq := MeasureTheory.integral_congr_ae (μ := volume)
    (Filter.Eventually.of_forall fun x => congrFun hinter x)
  rw [heq]
  have hsplit :
      ∫ x, ∑ j : Fin 3, ∑ i : Fin 3,
          v x j * (fderiv ℝ (fun y => directionalCoord v j i y) x)
            (EuclideanSpace.single i (1 : ℝ)) ∂volume =
        ∑ j : Fin 3, ∑ i : Fin 3,
          ∫ x, v x j * (fderiv ℝ (fun y => directionalCoord v j i y) x)
            (EuclideanSpace.single i (1 : ℝ)) ∂volume := by
    rw [MeasureTheory.integral_finset_sum (μ := volume) _ (fun j _ =>
      integrable_finset_sum _ (fun i _ => hint_summand i j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact MeasureTheory.integral_finset_sum (μ := volume) _ (fun i _ => hint_summand i j)
  rw [hsplit]
  exact Finset.sum_nonpos fun j _ => Finset.sum_nonpos fun i _ => hnonpos i j

lemma differentiableAt_of_contDiff {f : VelocityField} (hf : ContDiff ℝ ∞ f) (x : T3) :
    DifferentiableAt ℝ f x :=
  (hf.of_le (by exact_mod_cast le_top : (1 : WithTop ℕ∞) ≤ ∞)).contDiffAt.differentiableAt_one

/-! ## First-order commutator

The order-zero commutator vanishes (`convectiveCommutator_zero`). For `|α| = 1`,
the Leibniz expansion gives `[∂ᵢ, u·∇]u = (∂ᵢ u)·∇u`, hence
`‖[∂ᵢ, u·∇]u(x)‖ ≤ ‖∇u(x)‖ ‖∂ᵢ u(x)‖` by `convective_norm_le`. The remaining
higher-order Leibniz terms are packaged in `H3CommutatorEstimate`.
-/

/-! ## Named remaining hypotheses

Each hypothesis is a `Prop` with a docstring that says exactly what was added
and why. None of them silently weakens the conclusion
`d ≤ C_k ‖∇u‖_∞ ‖u‖²_{H³}`. Prefer discharging them later from the Fefferman
class or from `PersistenceHm`; they are not hidden in definitions. -/

/-- Pairing that is the candidate right derivative of `t ↦ ‖u(t)‖²_{H³}`. -/
def h3EnergyPairing (u : TimeDependentVelocity) (s : ℝ) : ℝ :=
  2 * ∑ k ∈ Finset.range 4, ∑ α : Fin k → Fin 3,
    ∫ x, inner ℝ (wordDeriv k α (u s) x)
      (wordDeriv k α (timeSliceDeriv u s) x) ∂volume

/-- **Time-differentiability of the H³ energy, with the pairing formula.**

Added because passing `d/dt` under the Lebesgue integral
`∫ |∂^α u(t,x)|² dx` needs an integrable dominant of the difference
quotients near `t = s`. Joint `C^∞` on `ℝ³ × [0,T)` from
`IsFeffermanSolutionOn` does not supply one: that definition has no uniform
spatial decay. The formula is the standard one: the right derivative of
`‖u(t)‖²_{H³}` equals `2 ∑_{|α|≤3} ∫ ⟨∂^α u(s), ∂^α ∂ₜ u(s)⟩`, using the
same one-sided time derivative as the momentum equation in
`IsFeffermanSolutionOn`.

The extra `ContDiff` of the time-derivative slice is likewise not yet
recorded for `derivWithin (Ici 0)` in this repository; joint smoothness
implies it, but the lemma is not formalized here. -/
structure H3EnergyRightDerivativeFormula (T : ℝ) (u : TimeDependentVelocity) : Prop where
  integrable : ∀ s ∈ Ico (0 : ℝ) T, sobolevEnergy 3 (u s) < ⊤ →
    ∀ k ∈ Finset.range 4, ∀ α : Fin k → Fin 3,
      Integrable (fun x => inner ℝ (wordDeriv k α (u s) x)
        (wordDeriv k α (timeSliceDeriv u s) x))
  /-- The one-sided time derivative, as a spatial field, is `C^∞`. -/
  contDiff_timeSlice : ∀ s ∈ Ico (0 : ℝ) T, ContDiff ℝ ∞ (timeSliceDeriv u s)
  hasDeriv : ∀ s ∈ Ico (0 : ℝ) T, sobolevEnergy 3 (u s) < ⊤ →
    HasDerivWithinAt (fun t => hsSq 3 (u t)) (h3EnergyPairing u s) (Ici s) s

/-- **Commutation of word derivatives with `Δ` and `∇`, and preservation of
`div = 0`.**

Added because the energy identity uses `∂^α Δu = Δ ∂^α u` and
`∂^α ∇p = ∇ ∂^α p`, and uses `div (∂^α u) = 0` to cancel the pressure
pairing. All three are equality of mixed partials on `C^∞` fields, but
they are not yet recorded for `wordDeriv` in this repository. -/
structure H3PartialCommutation (u : VelocityField) (p : PressureField) : Prop where
  wordDeriv_laplacian : ∀ k ∈ Finset.range 4, ∀ α : Fin k → Fin 3,
    wordDeriv k α (laplacian u) = laplacian (wordDeriv k α u)
  wordDeriv_pressureGradient : ∀ k ∈ Finset.range 4, ∀ α : Fin k → Fin 3,
    wordDeriv k α (pressureGradient p) = pressureGradient (wordDerivScalar k α p)
  div_wordDeriv : (∀ x, div u x = 0) →
    ∀ k ∈ Finset.range 4, ∀ α : Fin k → Fin 3, ∀ x, div (wordDeriv k α u) x = 0

/-- Vanishing-flux / integrability package at a single multi-index, used to
justify IBP for transport, pressure and viscosity. -/
structure WordIBP (u : VelocityField) (p : PressureField)
    (k : ℕ) (α : Fin k → Fin 3) : Prop where
  integrable_transport_pair : Integrable
    (fun x => inner ℝ (u x) (gradient (fun y => (1 / 2 : ℝ) * ‖wordDeriv k α u y‖ ^ 2) x))
  integrable_transport_div : Integrable
    (fun x => div u x * ((1 / 2 : ℝ) * ‖wordDeriv k α u x‖ ^ 2))
  flux_transport :
    ∫ x, div (fun y => ((1 / 2 : ℝ) * ‖wordDeriv k α u y‖ ^ 2) • u y) x ∂volume = 0
  integrable_pressure_pair : Integrable
    (fun x => inner ℝ (wordDeriv k α u x) (gradient (wordDerivScalar k α p) x))
  integrable_pressure_div : Integrable
    (fun x => div (wordDeriv k α u) x * wordDerivScalar k α p x)
  flux_pressure :
    ∫ x, div (fun y => wordDerivScalar k α p y • wordDeriv k α u y) x ∂volume = 0
  viscous : ViscousDissipationIBP (wordDeriv k α u)
  integrable_viscous :
    Integrable (fun x => inner ℝ (wordDeriv k α u x) (laplacian (wordDeriv k α u) x))
  integrable_transport :
    Integrable (fun x => inner ℝ (wordDeriv k α u x) (convective u (wordDeriv k α u) x))
  integrable_commutator :
    Integrable (fun x => inner ℝ (wordDeriv k α u x) (convectiveCommutator k α u x))
  integrable_convective :
    Integrable (fun x => inner ℝ (wordDeriv k α u x) (wordDeriv k α (convective u u) x))
  integrable_pressure :
    Integrable (fun x => inner ℝ (wordDeriv k α u x)
      (wordDeriv k α (pressureGradient p) x))
  integrable_laplacian :
    Integrable (fun x => inner ℝ (wordDeriv k α u x) (wordDeriv k α (laplacian u) x))

/-- **Vanishing-flux / integrability package at a time slice.**

Added because `IsFeffermanSolutionOn` gives joint smoothness and the Leray
L² energy inequality, but not the decay at spatial infinity that makes the
fluxes of `½|∂^α u|² u`, `(∂^α p)(∂^α u)`, and the viscous integrands have
vanishing integral of divergence. -/
def H3IBPVanishingFlux (u : VelocityField) (p : PressureField) : Prop :=
  ∀ k ∈ Finset.range 4, ∀ α : Fin k → Fin 3, WordIBP u p k α

/-- **H³ Kato commutator estimate.**

There is a constant `C ≥ 0` such that for every smooth field with finite
H³ energy,
`|∑_{|α|≤3} ∫ ⟨∂^α u, [∂^α, u·∇]u⟩| ≤ C ‖∇u‖_∞ ‖u‖²_{H³}`.

Added because the Leibniz expansion of the commutator has terms
(e.g. `‖∂²u · ∂²u‖₂`) that require a Gagliardo–Nirenberg interpolation
`‖∂²u‖₄² ≤ C ‖∇u‖_∞ ‖u‖_{H³}` which is not yet formalized in this repo.
The order-zero commutator vanishes (`convectiveCommutator_zero`). For `|α| = 1`
the Leibniz expansion is `(∂ᵢ u)·∇u`, which is bounded pointwise by
`‖∇u‖ ‖∂ᵢ u‖` via `convective_norm_le`. -/
def H3CommutatorEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : VelocityField),
    ContDiff ℝ ∞ u →
    sobolevEnergy 3 u < ⊤ →
    |∑ k ∈ Finset.range 4, ∑ α : Fin k → Fin 3,
        ∫ x, inner ℝ (wordDeriv k α u x) (convectiveCommutator k α u x) ∂volume|
      ≤ C * gradSup u * hsSq 3 u

/-! ## Main theorem -/

lemma wordDeriv_timeSlice_eq {ν T : ℝ} {u₀ : VelocityField}
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hu : IsFeffermanSolutionOn ν T u₀ u p)
    (hform : H3EnergyRightDerivativeFormula T u)
    {s : ℝ} (hs : s ∈ Ico (0 : ℝ) T) {k : ℕ} (α : Fin k → Fin 3)
    (_hk : k ≤ 3) :
    wordDeriv k α (timeSliceDeriv u s) =
      wordDeriv k α (fun x => ν • laplacian (u s) x) -
        wordDeriv k α (convective (u s) (u s)) -
        wordDeriv k α (pressureGradient (p s)) := by
  have huS : ContDiff ℝ ∞ (u s) := contDiff_u_slice hu hs
  have hpS : ContDiff ℝ ∞ (p s) := contDiff_p_slice hu hs
  have hdt : ContDiff ℝ ∞ (timeSliceDeriv u s) := hform.contDiff_timeSlice s hs
  have hcv : ContDiff ℝ ∞ (convective (u s) (u s)) := contDiff_convective huS huS
  have hpg : ContDiff ℝ ∞ (pressureGradient (p s)) := contDiff_pressureGradient hpS
  have hΔ : ContDiff ℝ ∞ (laplacian (u s)) := contDiff_laplacian huS
  have hk' : ContDiff ℝ k (timeSliceDeriv u s) := contDiff_of_infty hdt
  have hcvk : ContDiff ℝ k (convective (u s) (u s)) := contDiff_of_infty hcv
  have hpgk : ContDiff ℝ k (pressureGradient (p s)) := contDiff_of_infty hpg
  have hΔk : ContDiff ℝ k (laplacian (u s)) := contDiff_of_infty hΔ
  have hNSfun : timeSliceDeriv u s + convective (u s) (u s) + pressureGradient (p s) =
      fun x => ν • laplacian (u s) x := ns_momentum_field hu hs
  have hsum := wordDeriv_add3 α hk' hcvk hpgk
  have hsmul := wordDeriv_const_smul α ν hΔk
  have hleft : wordDeriv k α (timeSliceDeriv u s + convective (u s) (u s) +
      pressureGradient (p s)) =
      wordDeriv k α (fun x => ν • laplacian (u s) x) := by
    rw [hNSfun]
  -- Rearrange `wordDeriv (A+B+C) = wordDeriv (ν•Δ)` into the claimed identity.
  have : wordDeriv k α (timeSliceDeriv u s) + wordDeriv k α (convective (u s) (u s)) +
      wordDeriv k α (pressureGradient (p s)) =
      wordDeriv k α (fun x => ν • laplacian (u s) x) := by
    rw [← hsum, hleft]
  calc
    wordDeriv k α (timeSliceDeriv u s)
        = wordDeriv k α (timeSliceDeriv u s) + wordDeriv k α (convective (u s) (u s)) +
            wordDeriv k α (pressureGradient (p s)) -
            wordDeriv k α (convective (u s) (u s)) -
            wordDeriv k α (pressureGradient (p s)) := by abel
    _ = wordDeriv k α (fun x => ν • laplacian (u s) x) -
          wordDeriv k α (convective (u s) (u s)) -
          wordDeriv k α (pressureGradient (p s)) := by rw [this]

lemma convective_decomp (k : ℕ) (α : Fin k → Fin 3) (u : VelocityField) :
    wordDeriv k α (convective u u) =
      convective u (wordDeriv k α u) + convectiveCommutator k α u := by
  funext x
  simp [convectiveCommutator, Pi.add_apply, sub_eq_add_neg]


lemma integral_sub_real {f g : T3 → ℝ} (hf : Integrable f) (hg : Integrable g) :
    ∫ x, f x - g x ∂volume = ∫ x, f x ∂volume - ∫ x, g x ∂volume :=
  MeasureTheory.integral_sub (μ := volume) hf hg

lemma integral_add_real {f g : T3 → ℝ} (hf : Integrable f) (hg : Integrable g) :
    ∫ x, f x + g x ∂volume = ∫ x, f x ∂volume + ∫ x, g x ∂volume :=
  MeasureTheory.integral_add (μ := volume) hf hg

/-- Termwise energy identity at one multi-index, after applying the momentum
equation, the commutator decomposition, and mixed-partial commutation. -/
lemma pairing_term_eq {ν T : ℝ} {u₀ : VelocityField}
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hu : IsFeffermanSolutionOn ν T u₀ u p)
    (hform : H3EnergyRightDerivativeFormula T u)
    (hcommute : ∀ t ∈ Ico (0 : ℝ) T, H3PartialCommutation (u t) (p t))
    (hibp : ∀ t ∈ Ico (0 : ℝ) T, H3IBPVanishingFlux (u t) (p t))
    {s : ℝ} (hs : s ∈ Ico (0 : ℝ) T) {k : ℕ} (hk : k ∈ Finset.range 4)
    (α : Fin k → Fin 3) :
    ∫ x, inner ℝ (wordDeriv k α (u s) x)
        (wordDeriv k α (timeSliceDeriv u s) x) ∂volume =
      ν * ∫ x, inner ℝ (wordDeriv k α (u s) x)
          (laplacian (wordDeriv k α (u s)) x) ∂volume -
      ∫ x, inner ℝ (wordDeriv k α (u s) x)
          (convective (u s) (wordDeriv k α (u s)) x) ∂volume -
      ∫ x, inner ℝ (wordDeriv k α (u s) x)
          (convectiveCommutator k α (u s) x) ∂volume -
      ∫ x, inner ℝ (wordDeriv k α (u s) x)
          (pressureGradient (wordDerivScalar k α (p s)) x) ∂volume := by
  have hk3 : k ≤ 3 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hwd := wordDeriv_timeSlice_eq hu hform hs α hk3
  have hcomm := hcommute s hs
  have hIBP := hibp s hs k hk α
  have huS : ContDiff ℝ ∞ (u s) := contDiff_u_slice hu hs
  have hΔk : ContDiff ℝ k (laplacian (u s)) :=
    contDiff_of_infty (contDiff_laplacian huS)
  have hsmul := wordDeriv_const_smul α ν hΔk
  -- Rewrite the time-derivative word by the NS identity and commutation.
  have hfield : wordDeriv k α (timeSliceDeriv u s) =
      (fun x => ν • laplacian (wordDeriv k α (u s)) x) -
        convective (u s) (wordDeriv k α (u s)) -
        convectiveCommutator k α (u s) -
        pressureGradient (wordDerivScalar k α (p s)) := by
    rw [hwd, hsmul, hcomm.wordDeriv_laplacian k hk α,
      hcomm.wordDeriv_pressureGradient k hk α, convective_decomp]
    funext x
    simp [Pi.sub_apply, Pi.add_apply]
    abel
  have hinter :
      (fun x => inner ℝ (wordDeriv k α (u s) x)
          (wordDeriv k α (timeSliceDeriv u s) x)) =
        fun x =>
          ν * inner ℝ (wordDeriv k α (u s) x) (laplacian (wordDeriv k α (u s)) x) -
          inner ℝ (wordDeriv k α (u s) x) (convective (u s) (wordDeriv k α (u s)) x) -
          inner ℝ (wordDeriv k α (u s) x) (convectiveCommutator k α (u s) x) -
          inner ℝ (wordDeriv k α (u s) x)
            (pressureGradient (wordDerivScalar k α (p s)) x) := by
    funext x
    rw [hfield]
    simp only [Pi.sub_apply, inner_sub_right, inner_smul_right]
  have hintA : Integrable (fun x =>
      ν * inner ℝ (wordDeriv k α (u s) x) (laplacian (wordDeriv k α (u s)) x)) :=
    hIBP.integrable_viscous.const_mul ν
  have hintB := hIBP.integrable_transport
  have hintC := hIBP.integrable_commutator
  have hintD := hIBP.integrable_pressure_pair
  -- `pressure_pairing` uses `gradient`, which agrees with `pressureGradient`.
  have hintD' : Integrable (fun x => inner ℝ (wordDeriv k α (u s) x)
      (pressureGradient (wordDerivScalar k α (p s)) x)) := by
    simpa [pressureGradient] using hintD
  have hsplit := MeasureTheory.integral_congr_ae (μ := volume)
    (Filter.Eventually.of_forall fun x => congrFun hinter x)
  rw [hsplit]
  -- Split the four-term integrand.
  have hintABC : Integrable (fun x =>
      ν * inner ℝ (wordDeriv k α (u s) x) (laplacian (wordDeriv k α (u s)) x) -
        inner ℝ (wordDeriv k α (u s) x) (convective (u s) (wordDeriv k α (u s)) x) -
        inner ℝ (wordDeriv k α (u s) x) (convectiveCommutator k α (u s) x)) :=
    ((hintA.sub hintB).sub hintC)
  have hinter2 :
      (fun x =>
        ν * inner ℝ (wordDeriv k α (u s) x) (laplacian (wordDeriv k α (u s)) x) -
        inner ℝ (wordDeriv k α (u s) x) (convective (u s) (wordDeriv k α (u s)) x) -
        inner ℝ (wordDeriv k α (u s) x) (convectiveCommutator k α (u s) x) -
        inner ℝ (wordDeriv k α (u s) x)
          (pressureGradient (wordDerivScalar k α (p s)) x)) =
      (fun x =>
        (ν * inner ℝ (wordDeriv k α (u s) x) (laplacian (wordDeriv k α (u s)) x) -
          inner ℝ (wordDeriv k α (u s) x) (convective (u s) (wordDeriv k α (u s)) x) -
          inner ℝ (wordDeriv k α (u s) x) (convectiveCommutator k α (u s) x)) -
        inner ℝ (wordDeriv k α (u s) x)
          (pressureGradient (wordDerivScalar k α (p s)) x)) := rfl
  rw [integral_sub_real hintABC hintD']
  have hinter3 :
      (fun x =>
        ν * inner ℝ (wordDeriv k α (u s) x) (laplacian (wordDeriv k α (u s)) x) -
          inner ℝ (wordDeriv k α (u s) x) (convective (u s) (wordDeriv k α (u s)) x) -
          inner ℝ (wordDeriv k α (u s) x) (convectiveCommutator k α (u s) x)) =
      (fun x =>
        (ν * inner ℝ (wordDeriv k α (u s) x) (laplacian (wordDeriv k α (u s)) x) -
          inner ℝ (wordDeriv k α (u s) x) (convective (u s) (wordDeriv k α (u s)) x)) -
        inner ℝ (wordDeriv k α (u s) x) (convectiveCommutator k α (u s) x)) := by
    funext x; ring
  erw [integral_sub_real (hintA.sub hintB) hintC]
  have hinter4 :
      (fun x =>
        ν * inner ℝ (wordDeriv k α (u s) x) (laplacian (wordDeriv k α (u s)) x) -
          inner ℝ (wordDeriv k α (u s) x) (convective (u s) (wordDeriv k α (u s)) x)) =
      (fun x =>
        ν * inner ℝ (wordDeriv k α (u s) x) (laplacian (wordDeriv k α (u s)) x) +
          -inner ℝ (wordDeriv k α (u s) x) (convective (u s) (wordDeriv k α (u s)) x)) := by
    funext x; ring
  erw [integral_add_real hintA hintB.neg, MeasureTheory.integral_neg,
    MeasureTheory.integral_const_mul (μ := volume)]
  ring

/-- The transport, pressure and viscous contributions to a single multi-index
pairing are respectively `0`, `0` and `≤ 0` (`ν ≥ 0`). -/
lemma pairing_term_le_neg_commutator {ν T : ℝ} {u₀ : VelocityField}
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hν : 0 ≤ ν)
    (hu : IsFeffermanSolutionOn ν T u₀ u p)
    (hform : H3EnergyRightDerivativeFormula T u)
    (hcommute : ∀ t ∈ Ico (0 : ℝ) T, H3PartialCommutation (u t) (p t))
    (hibp : ∀ t ∈ Ico (0 : ℝ) T, H3IBPVanishingFlux (u t) (p t))
    {s : ℝ} (hs : s ∈ Ico (0 : ℝ) T) {k : ℕ} (hk : k ∈ Finset.range 4)
    (α : Fin k → Fin 3) :
    ∫ x, inner ℝ (wordDeriv k α (u s) x)
        (wordDeriv k α (timeSliceDeriv u s) x) ∂volume ≤
      -∫ x, inner ℝ (wordDeriv k α (u s) x)
          (convectiveCommutator k α (u s) x) ∂volume := by
  have heq := pairing_term_eq hu hform hcommute hibp hs hk α
  have hIBP := hibp s hs k hk α
  have hC := hcommute s hs
  have huS : ContDiff ℝ ∞ (u s) := contDiff_u_slice hu hs
  have hpS : ContDiff ℝ ∞ (p s) := contDiff_p_slice hu hs
  have hw : ContDiff ℝ ∞ (wordDeriv k α (u s)) := contDiff_wordDeriv α huS
  have hq : ContDiff ℝ ∞ (wordDerivScalar k α (p s)) := by
    unfold wordDerivScalar
    have h : ContDiff ℝ ∞ (iteratedFDeriv ℝ k (p s)) :=
      hpS.iteratedFDeriv_right (by
        rw [show (k : WithTop ℕ∞) = ((k : ℕ∞) : WithTop ℕ∞) from rfl, ← WithTop.coe_add,
          top_add])
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => T3) ℝ
        (fun j => EuclideanSpace.single (α j) (1 : ℝ))).contDiff.comp h
  -- Transport cancellation.
  have htr : ∫ x, inner ℝ (wordDeriv k α (u s) x)
      (convective (u s) (wordDeriv k α (u s)) x) ∂volume = 0 :=
    transport_pairing_vanishes (u s) (wordDeriv k α (u s))
      (fun x => div_u_slice hu hs x)
      (fun x => differentiableAt_of_contDiff huS x)
      (fun x => differentiableAt_of_contDiff hw x)
      hIBP.integrable_transport_pair hIBP.integrable_transport_div
      hIBP.flux_transport
  -- Pressure cancellation (uses `div (∂^α u) = 0` from mixed partials).
  have hpr : ∫ x, inner ℝ (wordDeriv k α (u s) x)
      (pressureGradient (wordDerivScalar k α (p s)) x) ∂volume = 0 :=
    pressure_pairing_vanishes (wordDeriv k α (u s)) (wordDerivScalar k α (p s))
      (fun x => hC.div_wordDeriv (fun y => div_u_slice hu hs y) k hk α x)
      (fun x => differentiableAt_of_contDiff hw x)
      (fun x => (hq.of_le (by exact_mod_cast le_top :
        (1 : WithTop ℕ∞) ≤ ∞)).contDiffAt.differentiableAt_one)
      hIBP.integrable_pressure_pair hIBP.integrable_pressure_div
      hIBP.flux_pressure
  -- Viscous dissipation ≤ 0, multiplied by `ν ≥ 0`.
  have hvisc : ∫ x, inner ℝ (wordDeriv k α (u s) x)
      (laplacian (wordDeriv k α (u s)) x) ∂volume ≤ 0 :=
    inner_laplacian_nonpos (wordDeriv k α (u s)) hIBP.viscous
  have hviscν :
      ν * ∫ x, inner ℝ (wordDeriv k α (u s) x)
        (laplacian (wordDeriv k α (u s)) x) ∂volume ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hν hvisc
  linarith [heq, htr, hpr, hviscν]

/-- **Kato–Ponce H³ energy inequality** for Fefferman-class solutions.

There is a constant `C_k ≥ 0` (namely twice the constant in
`H3CommutatorEstimate`) such that for every viscosity `ν ≥ 0`, every local
Fefferman-class solution with finite H³ energy, and every time `s` in the
existence interval, the map `t ↦ ‖u(t)‖²_{H³}` has a right derivative
`d ≤ C_k ‖∇u(s)‖_∞ ‖u(s)‖²_{H³}`.

The hypothesis `0 ≤ ν` is added because the target upper bound has no
viscous term, and `∫ ⟨∂^α u, Δ ∂^α u⟩ ≤ 0` can be dropped only when
`ν` is nonnegative. (`KatoMaximalSolution` does not itself quantify a
sign on `ν`; Clay (A) takes `ν > 0`.)

The other added hypotheses are `H3EnergyRightDerivativeFormula` (time
differentiability of the energy, with the pairing formula),
`H3PartialCommutation` (mixed partials), `H3IBPVanishingFlux` (decay at
infinity for IBP), and `H3CommutatorEstimate` (the remaining commutator
bound). None of them changes the form of the conclusion. -/
theorem katoPonce_h3_energy (hcommEst : H3CommutatorEstimate) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧
      ∀ (ν T : ℝ) (u₀ : VelocityField) (u : TimeDependentVelocity)
        (p : TimeDependentPressure),
        0 ≤ ν →
        IsFeffermanSolutionOn ν T u₀ u p →
        (∀ t ∈ Ico (0 : ℝ) T, sobolevEnergy 3 (u t) < ⊤) →
        H3EnergyRightDerivativeFormula T u →
        (∀ t ∈ Ico (0 : ℝ) T, H3PartialCommutation (u t) (p t)) →
        (∀ t ∈ Ico (0 : ℝ) T, H3IBPVanishingFlux (u t) (p t)) →
        ∀ s ∈ Ico (0 : ℝ) T,
          ∃ d : ℝ, HasDerivWithinAt (fun t => hsSq 3 (u t)) d (Ici s) s ∧
            d ≤ Ck * gradSup (u s) * hsSq 3 (u s) := by
  obtain ⟨C, hC, hCbd⟩ := hcommEst
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro ν T u₀ u p hν hu hfin hform hcommute hibp s hs
  refine ⟨h3EnergyPairing u s, hform.hasDeriv s hs (hfin s hs), ?_⟩
  -- Bound the pairing by twice the commutator pairing, then apply the estimate.
  have hterm : ∀ k ∈ Finset.range 4, ∀ α : Fin k → Fin 3,
      ∫ x, inner ℝ (wordDeriv k α (u s) x)
          (wordDeriv k α (timeSliceDeriv u s) x) ∂volume ≤
        -∫ x, inner ℝ (wordDeriv k α (u s) x)
            (convectiveCommutator k α (u s) x) ∂volume :=
    fun k hk α => pairing_term_le_neg_commutator hν hu hform hcommute hibp hs hk α
  have hsum :
      ∑ k ∈ Finset.range 4, ∑ α : Fin k → Fin 3,
          ∫ x, inner ℝ (wordDeriv k α (u s) x)
            (wordDeriv k α (timeSliceDeriv u s) x) ∂volume ≤
        -∑ k ∈ Finset.range 4, ∑ α : Fin k → Fin 3,
          ∫ x, inner ℝ (wordDeriv k α (u s) x)
            (convectiveCommutator k α (u s) x) ∂volume := by
    have h1 := Finset.sum_le_sum (s := Finset.range 4) fun k hk =>
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k → Fin 3)))
        fun α _ => hterm k hk α
    simp [Finset.sum_neg_distrib] at h1
    exact h1
  have hpair : h3EnergyPairing u s ≤
      -2 * ∑ k ∈ Finset.range 4, ∑ α : Fin k → Fin 3,
        ∫ x, inner ℝ (wordDeriv k α (u s) x)
          (convectiveCommutator k α (u s) x) ∂volume := by
    unfold h3EnergyPairing
    have h2 : 0 ≤ (2 : ℝ) := by norm_num
    linarith [mul_le_mul_of_nonneg_left hsum h2]
  have huS : ContDiff ℝ ∞ (u s) := contDiff_u_slice hu hs
  have hCest := hCbd (u s) huS (hfin s hs)
  have habs :
      -∑ k ∈ Finset.range 4, ∑ α : Fin k → Fin 3,
          ∫ x, inner ℝ (wordDeriv k α (u s) x)
            (convectiveCommutator k α (u s) x) ∂volume ≤
        |∑ k ∈ Finset.range 4, ∑ α : Fin k → Fin 3,
          ∫ x, inner ℝ (wordDeriv k α (u s) x)
            (convectiveCommutator k α (u s) x) ∂volume| :=
    neg_le_abs _
  have hfinal : h3EnergyPairing u s ≤ 2 * C * gradSup (u s) * hsSq 3 (u s) := by
    have : -2 * ∑ k ∈ Finset.range 4, ∑ α : Fin k → Fin 3,
        ∫ x, inner ℝ (wordDeriv k α (u s) x)
          (convectiveCommutator k α (u s) x) ∂volume ≤
        2 * |∑ k ∈ Finset.range 4, ∑ α : Fin k → Fin 3,
          ∫ x, inner ℝ (wordDeriv k α (u s) x)
            (convectiveCommutator k α (u s) x) ∂volume| := by
      have hnn : 0 ≤ (2 : ℝ) := by norm_num
      linarith [mul_le_mul_of_nonneg_left habs hnn]
    have hC2 : 2 * |∑ k ∈ Finset.range 4, ∑ α : Fin k → Fin 3,
        ∫ x, inner ℝ (wordDeriv k α (u s) x)
          (convectiveCommutator k α (u s) x) ∂volume| ≤
        2 * (C * gradSup (u s) * hsSq 3 (u s)) :=
      mul_le_mul_of_nonneg_left hCest (by norm_num)
    linarith [hpair, this, hC2]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hfinal

#print axioms KatoPonce.katoPonce_h3_energy
#print axioms KatoPonce.transport_pairing_vanishes
#print axioms KatoPonce.inner_laplacian_nonpos

end KatoPonce
