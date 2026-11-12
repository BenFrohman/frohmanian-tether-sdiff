import Scratch.KatoPonce
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Discharge of `H3PartialCommutation`

This file proves `KatoPonce.H3PartialCommutation` for every pair of
`C^∞` fields, and therefore for every time slice of a
`IsFeffermanSolutionOn` solution (via `contDiff_u_slice` and
`contDiff_p_slice`). The three fields of the structure are equality of
mixed partials for `wordDeriv`: it commutes with `Δ` and with `∇`, and
it preserves `div = 0`. No energy, decay, or integrability hypothesis
is used, and the statements in `KatoPonce.lean` are unchanged.

`H3IBPVanishingFlux` is **not** discharged. `IsFeffermanSolutionOn`
together with finite `sobolevEnergy 3` on each slice gives joint
`C^∞` of `(u, p)`, the momentum and divergence equations, the Leray
`L²` energy inequality, and `L²` spatial derivatives of `u` through
order 3 (and, via `GradBound`, `‖∇u‖_∞ < ∞`). That package does not
give the integrability and vanishing-flux fields of `WordIBP`:

* Pressure. The equation determines `∇p` only up to a function of time,
  and supplies no spatial integrability of `p` or of `∂^α p`. In
  particular `integrable_pressure_pair`, `integrable_pressure`, and
  `flux_pressure` require `⟨∂^α u, ∇ ∂^α p⟩ ∈ L¹` and
  `(∂^α p)(∂^α u) ∈ L¹`. From the momentum equation,
  `∇p = ν Δu − ∂ₜu − (u·∇)u`, the term `∂ₜu` is not known to lie in
  any `L^p`; `IsFeffermanSolutionOn` does not record spatial
  integrability of the one-sided time derivative, and this file does
  not use `H3EnergyRightDerivativeFormula` (owned by another worker).
  Even that formula only gives integrability of the pairings
  `⟨∂^α u, ∂^α ∂ₜu⟩` and `C^∞` of the time-slice derivative, not
  `∂ₜu ∈ L²` nor `L²` control of `∂^α ∇p`. A Poisson reconstruction
  `Δp = −div div(u ⊗ u)` with Calderón–Zygmund estimates is not in
  this repository, and the Fefferman class does not fix the Newtonian
  gauge.

* Derivatives past order 3. For `|α| ∈ {2, 3}`,
  `integrable_laplacian` and `ViscousDissipationIBP.integrable_inner`
  ask for `⟨∂^α u, ∂^α Δu⟩ ∈ L¹`, i.e. a pairing against `D^{4}` or
  `D^{5}u`. The `PartialIBP` fields for `v = ∂^α u` likewise need
  `|∂ᵢ vⱼ|² ∈ L¹`, which for `|α| = 3` is the `Ḣ⁴` seminorm. Finite
  `H³` energy does not provide these. The same obstruction hits
  `integrable_transport` / `integrable_convective` /
  `integrable_commutator` at `|α| = 3`, which contain `∇ ∂^α u`.

* Vanishing flux at infinity. `IBPWholeSpace.integral_partial_mul` and
  `integral_partial_inner_of_contDiff` give
  `∫ (∂ᵢ f) g = −∫ f (∂ᵢ g)` when the three products, including `f g`,
  are integrable; they do not by themselves give `∫ div F = 0`, because
  the constant function `1` is not in `L¹(ℝ³)`. A cutoff argument would
  need `F ∈ L¹` and `div F ∈ L¹`, which for the pressure flux
  `F = (∂^α p) ∂^α u` and for the viscous fluxes of
  `(vⱼ ∂ᵢ vⱼ) eᵢ` at `|α| = 3` is exactly the missing integrability
  above. `FeffermanDecay` is assumed only of the initial datum `u₀`,
  not of the slices `u(t)`, `p(t)`.

The definition `H3IBPVanishingFlux` is therefore not a theorem of
`IsFeffermanSolutionOn` plus finite `H³` energy, and it is left as
stated. No statement is weakened.

Nothing in this file is a `sorry`, a custom axiom, or an `opaque` trick.
-/

open MeasureTheory hiding volume
open NavierStokes3D FrohmanianTether RepairedTether KatoPonce Set
open scoped ContDiff InnerProductSpace

set_option autoImplicit false

noncomputable section
namespace KatoPonceHypotheses

/-- The standard basis vector `eᵢ`. -/
local notation "e" => fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)

/-- Finite-order smoothness from `C^∞`. Generalized from
`KatoPonce.contDiff_of_infty` (which is stated only for `VelocityField`). -/
lemma contDiff_nat {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ} {f : E → F}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ n f :=
  hf.of_le (by exact_mod_cast le_top)

/-! ## Word-derivative recurrences -/

lemma wordDeriv_succ {k : ℕ} (α : Fin (k + 1) → Fin 3) {f : VelocityField}
    (hf : ContDiff ℝ ∞ f) :
    wordDeriv (k + 1) α f =
      fun x => fderiv ℝ (wordDeriv k (Fin.tail α) f) x (e (α 0)) := by
  funext x
  simp only [wordDeriv]
  rw [iteratedFDeriv_succ_apply_left]
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x :=
    (hf.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) x
  show _ = fderiv ℝ (fun y => iteratedFDeriv ℝ k f y
      (fun j => EuclideanSpace.single (Fin.tail α j) (1 : ℝ))) x _
  rw [fderiv_continuousMultilinear_apply_const_apply hd]
  rfl

lemma wordDerivScalar_zero (α : Fin 0 → Fin 3) (p : PressureField) :
    wordDerivScalar 0 α p = p := by
  funext x
  exact iteratedFDeriv_zero_apply _

lemma wordDerivScalar_succ {k : ℕ} (α : Fin (k + 1) → Fin 3) {p : PressureField}
    (hp : ContDiff ℝ ∞ p) :
    wordDerivScalar (k + 1) α p =
      fun x => fderiv ℝ (wordDerivScalar k (Fin.tail α) p) x (e (α 0)) := by
  funext x
  simp only [wordDerivScalar]
  rw [iteratedFDeriv_succ_apply_left]
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k p) x :=
    (hp.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) x
  show _ = fderiv ℝ (fun y => iteratedFDeriv ℝ k p y
      (fun j => EuclideanSpace.single (Fin.tail α j) (1 : ℝ))) x _
  rw [fderiv_continuousMultilinear_apply_const_apply hd]
  rfl

lemma contDiff_wordDerivScalar {k : ℕ} (α : Fin k → Fin 3) {p : PressureField}
    (hp : ContDiff ℝ ∞ p) : ContDiff ℝ ∞ (wordDerivScalar k α p) := by
  unfold wordDerivScalar
  have h : ContDiff ℝ ∞ (iteratedFDeriv ℝ k p) :=
    hp.iteratedFDeriv_right (by
      rw [show (k : WithTop ℕ∞) = ((k : ℕ∞) : WithTop ℕ∞) from rfl, ← WithTop.coe_add,
        top_add])
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => T3) ℝ
      (fun j => EuclideanSpace.single (α j) (1 : ℝ))).contDiff.comp h

/-! ## Equality of mixed partials -/

/-- Applying a constant increment commutes with `fderiv`. -/
lemma fderiv_fderiv_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x : E) (v w : E) (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    (fderiv ℝ (fun y => fderiv ℝ f y v) x) w = (fderiv ℝ (fderiv ℝ f) x) w v := by
  have happ : HasFDerivAt (fun y => fderiv ℝ f y v)
      ((ContinuousLinearMap.apply ℝ F v).comp (fderiv ℝ (fderiv ℝ f) x)) x :=
    (ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp x hf.hasFDerivAt
  rw [happ.fderiv]
  rfl

/-- Schwarz: `∂_w (Df · v) = ∂_v (Df · w)` at a `C²` point. -/
lemma fderiv_fderiv_apply_symm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x : E) (v w : E) (hf : ContDiffAt ℝ 2 f x) :
    (fderiv ℝ (fun y => fderiv ℝ f y v) x) w =
      (fderiv ℝ (fun y => fderiv ℝ f y w) x) v := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsymm : IsSymmSndFDerivAt ℝ f x :=
    hf.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  rw [fderiv_fderiv_apply f x v w hfd, fderiv_fderiv_apply f x w v hfd]
  exact hsymm.eq w v

/-- `∂_v (Δ f) = Δ (∂_v f)`. -/
lemma fderiv_laplacian {f : VelocityField} (hf : ContDiff ℝ ∞ f) (x : T3) (v : T3) :
    (fderiv ℝ (laplacian f) x) v = laplacian (fun y => (fderiv ℝ f y) v) x := by
  let g : Fin 3 → VelocityField := fun i y => (fderiv ℝ f y) (e i)
  have hg (i : Fin 3) : ContDiff ℝ ∞ (g i) :=
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3)) (e i)).contDiff.comp
      (hf.fderiv_right (m := ∞) le_rfl)
  have hgi (i : Fin 3) : ContDiff ℝ ∞ (fun z => (fderiv ℝ (g i) z) (e i)) :=
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3)) (e i)).contDiff.comp
      ((hg i).fderiv_right (m := ∞) le_rfl)
  have hsum :
      fderiv ℝ (fun z => ∑ i : Fin 3, (fderiv ℝ (g i) z) (e i)) x =
        ∑ i : Fin 3, fderiv ℝ (fun z => (fderiv ℝ (g i) z) (e i)) x :=
    fderiv_fun_sum fun i _ => (hgi i).differentiable (by simp) x
  have hdef : laplacian f = fun z => ∑ i : Fin 3, (fderiv ℝ (g i) z) (e i) := rfl
  have hL : (fderiv ℝ (laplacian f) x) v =
      ∑ i : Fin 3, (fderiv ℝ (fun z => (fderiv ℝ (g i) z) (e i)) x) v := by
    rw [hdef, hsum, ContinuousLinearMap.sum_apply]
  refine hL.trans ?_
  unfold laplacian
  refine Finset.sum_congr rfl fun i _ => ?_
  have hφ : ContDiffAt ℝ 2 (g i) x := (contDiff_nat (n := 2) (hg i)).contDiffAt
  have hswap := fderiv_fderiv_apply_symm (g i) x (e i) v hφ
  have heq : (fun z => (fderiv ℝ (g i) z) v) =
      fun z => (fderiv ℝ (fun y => (fderiv ℝ f y) v) z) (e i) := by
    funext z
    have hf2 : ContDiffAt ℝ 2 f z := (contDiff_nat (n := 2) hf).contDiffAt
    simpa [g] using fderiv_fderiv_apply_symm f z (e i) v hf2
  rw [hswap, heq]

/-- `wordDeriv` commutes with `Δ`. -/
lemma wordDeriv_laplacian_eq {k : ℕ} (α : Fin k → Fin 3) {f : VelocityField}
    (hf : ContDiff ℝ ∞ f) :
    wordDeriv k α (laplacian f) = laplacian (wordDeriv k α f) := by
  induction k with
  | zero =>
    funext x
    simp [wordDeriv_zero]
  | succ k ih =>
    funext x
    have hlap : ContDiff ℝ ∞ (laplacian f) := contDiff_laplacian hf
    have hwd : ContDiff ℝ ∞ (wordDeriv k (Fin.tail α) f) :=
      contDiff_wordDeriv (Fin.tail α) hf
    calc
      wordDeriv (k + 1) α (laplacian f) x
          = (fderiv ℝ (wordDeriv k (Fin.tail α) (laplacian f)) x) (e (α 0)) :=
            congrFun (wordDeriv_succ α hlap) x
      _ = (fderiv ℝ (laplacian (wordDeriv k (Fin.tail α) f)) x) (e (α 0)) := by
            rw [ih (Fin.tail α)]
      _ = laplacian (fun y => (fderiv ℝ (wordDeriv k (Fin.tail α) f) y) (e (α 0))) x :=
            fderiv_laplacian hwd x (e (α 0))
      _ = laplacian (wordDeriv (k + 1) α f) x := by
            congr 1
            exact (wordDeriv_succ α hf).symm

/-- `∂_v (∇q) = ∇(∂_v q)`. -/
lemma fderiv_pressureGradient {q : PressureField} (hq : ContDiff ℝ ∞ q)
    (x : T3) (v : T3) :
    (fderiv ℝ (pressureGradient q) x) v =
      pressureGradient (fun y => (fderiv ℝ q y) v) x := by
  have hgrad : ContDiff ℝ ∞ (pressureGradient q) := contDiff_pressureGradient hq
  have hq1 : Differentiable ℝ q := hq.differentiable (by simp)
  have hv : ContDiff ℝ ∞ (fun y => (fderiv ℝ q y) v) :=
    (ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp (hq.fderiv_right (m := ∞) le_rfl)
  ext j
  have hL : ((fderiv ℝ (pressureGradient q) x) v) j =
      (fderiv ℝ (fun y => pressureGradient q y j) x) v :=
    fderiv_field_coord (pressureGradient q) x j v (hgrad.differentiable (by simp) x)
  have hcoord : (fun y => pressureGradient q y j) =
      fun y => (fderiv ℝ q y) (e j) := by
    funext y
    simpa [pressureGradient] using gradient_coord q y j (hq1 y)
  have hswap : (fderiv ℝ (fun y => (fderiv ℝ q y) (e j)) x) v =
      (fderiv ℝ (fun y => (fderiv ℝ q y) v) x) (e j) :=
    fderiv_fderiv_apply_symm q x (e j) v ((contDiff_nat (n := 2) hq).contDiffAt)
  have hR : pressureGradient (fun y => (fderiv ℝ q y) v) x j =
      (fderiv ℝ (fun y => (fderiv ℝ q y) v) x) (e j) := by
    simpa [pressureGradient] using
      gradient_coord (fun y => (fderiv ℝ q y) v) x j (hv.differentiable (by simp) x)
  rw [hL, hcoord, hswap, hR]

/-- `wordDeriv` commutes with `∇` on a scalar. -/
lemma wordDeriv_pressureGradient_eq {k : ℕ} (α : Fin k → Fin 3)
    {p : PressureField} (hp : ContDiff ℝ ∞ p) :
    wordDeriv k α (pressureGradient p) =
      pressureGradient (wordDerivScalar k α p) := by
  induction k with
  | zero =>
    funext x
    simp [wordDeriv_zero, wordDerivScalar_zero]
  | succ k ih =>
    funext x
    have hgrad : ContDiff ℝ ∞ (pressureGradient p) := contDiff_pressureGradient hp
    have hwd : ContDiff ℝ ∞ (wordDerivScalar k (Fin.tail α) p) :=
      contDiff_wordDerivScalar (Fin.tail α) hp
    calc
      wordDeriv (k + 1) α (pressureGradient p) x
          = (fderiv ℝ (wordDeriv k (Fin.tail α) (pressureGradient p)) x) (e (α 0)) :=
            congrFun (wordDeriv_succ α hgrad) x
      _ = (fderiv ℝ (pressureGradient (wordDerivScalar k (Fin.tail α) p)) x)
            (e (α 0)) := by
            rw [ih (Fin.tail α)]
      _ = pressureGradient
            (fun y => (fderiv ℝ (wordDerivScalar k (Fin.tail α) p) y) (e (α 0))) x :=
            fderiv_pressureGradient hwd x (e (α 0))
      _ = pressureGradient (wordDerivScalar (k + 1) α p) x := by
            congr 1
            exact (wordDerivScalar_succ α hp).symm

/-- `∂_v (div f) = div (∂_v f)`. -/
lemma fderiv_div {f : VelocityField} (hf : ContDiff ℝ ∞ f) (x : T3) (v : T3) :
    (fderiv ℝ (div f) x) v = div (fun y => (fderiv ℝ f y) v) x := by
  have hcoord (i : Fin 3) : ContDiff ℝ ∞ (fun y => f y i) := by
    let L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
      PiLp.proj (p := 2) (fun _ : Fin 3 => ℝ) i
    have hfun : (fun y => f y i) = fun y => L (f y) := rfl
    rw [hfun]
    exact L.contDiff.comp hf
  have hgi (i : Fin 3) :
      ContDiff ℝ ∞ (fun z => (fderiv ℝ (fun y => f y i) z) (e i)) :=
    (ContinuousLinearMap.apply ℝ ℝ (e i)).contDiff.comp
      ((hcoord i).fderiv_right (m := ∞) le_rfl)
  have hsum :
      fderiv ℝ (fun z => ∑ i : Fin 3, (fderiv ℝ (fun y => f y i) z) (e i)) x =
        ∑ i : Fin 3, fderiv ℝ (fun z => (fderiv ℝ (fun y => f y i) z) (e i)) x :=
    fderiv_fun_sum fun i _ => (hgi i).differentiable (by simp) x
  have hdef : div f = fun z => ∑ i : Fin 3, (fderiv ℝ (fun y => f y i) z) (e i) :=
    rfl
  have hL : (fderiv ℝ (div f) x) v =
      ∑ i : Fin 3, (fderiv ℝ (fun z => (fderiv ℝ (fun y => f y i) z) (e i)) x) v := by
    rw [hdef, hsum, ContinuousLinearMap.sum_apply]
  refine hL.trans ?_
  unfold div
  refine Finset.sum_congr rfl fun i _ => ?_
  have hswap : (fderiv ℝ (fun z => (fderiv ℝ (fun y => f y i) z) (e i)) x) v =
      (fderiv ℝ (fun z => (fderiv ℝ (fun y => f y i) z) v) x) (e i) :=
    fderiv_fderiv_apply_symm (fun y => f y i) x (e i) v
      ((contDiff_nat (n := 2) (hcoord i)).contDiffAt)
  have heq : (fun z => (fderiv ℝ (fun y => f y i) z) v) =
      fun z => (fderiv ℝ f z v) i := by
    funext z
    exact (fderiv_field_coord f z i v (hf.differentiable (by simp) z)).symm
  have hR : (fderiv ℝ (fun y => (fderiv ℝ f y v) i) x) (e i) =
      (fderiv ℝ (fun z => (fderiv ℝ (fun y => f y i) z) v) x) (e i) := by
    have hfun :
        (fun y => (fderiv ℝ f y v) i) =
          fun z => (fderiv ℝ (fun y => f y i) z) v := by
      funext z
      exact fderiv_field_coord f z i v (hf.differentiable (by simp) z)
    rw [hfun]
  rw [hswap, ← hR]

/-- If `div f = 0`, then `div (∂^α f) = 0`. -/
lemma div_wordDeriv_eq {k : ℕ} (α : Fin k → Fin 3) {f : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hdiv : ∀ x, div f x = 0) :
    ∀ x, div (wordDeriv k α f) x = 0 := by
  induction k with
  | zero =>
    intro x
    simpa [wordDeriv_zero] using hdiv x
  | succ k ih =>
    intro x
    have hwd : ContDiff ℝ ∞ (wordDeriv k (Fin.tail α) f) :=
      contDiff_wordDeriv (Fin.tail α) hf
    have ih0 : div (wordDeriv k (Fin.tail α) f) = fun _ => 0 :=
      funext fun y => ih (Fin.tail α) y
    have hcomm := fderiv_div hwd x (e (α 0))
    have : div (fun y => (fderiv ℝ (wordDeriv k (Fin.tail α) f) y) (e (α 0))) x =
        (fderiv ℝ (div (wordDeriv k (Fin.tail α) f)) x) (e (α 0)) := hcomm.symm
    have hwd_succ :
        wordDeriv (k + 1) α f =
          fun y => (fderiv ℝ (wordDeriv k (Fin.tail α) f) y) (e (α 0)) :=
      wordDeriv_succ α hf
    rw [hwd_succ, this, ih0]
    simp

/-! ## The commutation package -/

/-- `H3PartialCommutation` for every pair of `C^∞` fields. -/
theorem h3PartialCommutation_of_contDiff {u : VelocityField} {p : PressureField}
    (hu : ContDiff ℝ ∞ u) (hp : ContDiff ℝ ∞ p) : H3PartialCommutation u p where
  wordDeriv_laplacian := fun _k _hk α => wordDeriv_laplacian_eq α hu
  wordDeriv_pressureGradient := fun _k _hk α => wordDeriv_pressureGradient_eq α hp
  div_wordDeriv := fun hdiv _k _hk α => div_wordDeriv_eq α hu hdiv

/-- Every time slice of a Fefferman-class solution satisfies
`H3PartialCommutation`. Finite `H³` energy is not required. -/
theorem h3PartialCommutation {ν T : ℝ} {u₀ : VelocityField}
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hu : IsFeffermanSolutionOn ν T u₀ u p) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    H3PartialCommutation (u t) (p t) :=
  h3PartialCommutation_of_contDiff (contDiff_u_slice hu ht) (contDiff_p_slice hu ht)

#print axioms KatoPonceHypotheses.wordDeriv_laplacian_eq
#print axioms KatoPonceHypotheses.wordDeriv_pressureGradient_eq
#print axioms KatoPonceHypotheses.div_wordDeriv_eq
#print axioms KatoPonceHypotheses.h3PartialCommutation_of_contDiff
#print axioms KatoPonceHypotheses.h3PartialCommutation

end KatoPonceHypotheses
