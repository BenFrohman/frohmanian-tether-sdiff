import Scratch.SobolevFourier
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.LinearAlgebra.Multilinear.Basic

/-! # Fefferman data is Schwartz, and Fourier inversion is pointwise

Under `ContDiff ℝ ∞` and `FeffermanDecay`, the complexified field `cplx ∘ f` is a
Schwartz map `𝓢(ℝ³, ℂ³)`. Consequently `𝓕⁻ (𝓕 (cplx ∘ f)) = cplx ∘ f` pointwise. -/

open MeasureTheory FourierTransform Real SchwartzMap
open scoped ENNReal ContDiff InnerProductSpace

set_option autoImplicit false

noncomputable section
namespace FeffermanSchwartz

open LerayHeat SobolevFourier
open NavierStokes3D (VelocityField T3)
open RepairedTether (FeffermanDecay)

/-- The Euclidean basis expansion `x = ∑ i, x i • eᵢ`. -/
lemma euclidean_eq_sum (x : E3) :
    x = ∑ i : Fin 3, x i • EuclideanSpace.single i (1 : ℝ) := by
  simpa [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
    ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x).symm

/-- Operator-norm bound: a continuous multilinear map on `(ℝ³)^n` is controlled by its
values on the standard-basis tuples. -/
lemma norm_cmul_le_sum_basis {n : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => E3) E3) :
    ‖L‖ ≤ ∑ α : Fin n → Fin 3,
      ‖L fun j => EuclideanSpace.single (α j) (1 : ℝ)‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    fun v => ?_
  have hv : v = fun j => ∑ i : Fin 3, v j i • EuclideanSpace.single i (1 : ℝ) := by
    funext j; exact euclidean_eq_sum (v j)
  -- expand, then estimate
  calc ‖L v‖
      = ‖L.toMultilinearMap
          fun j => ∑ i : Fin 3, v j i • EuclideanSpace.single i (1 : ℝ)‖ := by
        congr 1; exact congrArg L hv
    _ = ‖∑ α : Fin n → Fin 3,
          L.toMultilinearMap
            fun j => v j (α j) • EuclideanSpace.single (α j) (1 : ℝ)‖ := by
        rw [MultilinearMap.map_sum]
    _ = ‖∑ α : Fin n → Fin 3,
          (∏ j, v j (α j)) • L fun j => EuclideanSpace.single (α j) (1 : ℝ)‖ := by
        refine congrArg norm (Finset.sum_congr rfl fun α _ => ?_)
        exact L.toMultilinearMap.map_smul_univ _ _
    _ ≤ ∑ α : Fin n → Fin 3,
          ‖(∏ j, v j (α j)) • L fun j => EuclideanSpace.single (α j) (1 : ℝ)‖ :=
        norm_sum_le _ _
    _ = ∑ α : Fin n → Fin 3,
          |∏ j, v j (α j)| * ‖L fun j => EuclideanSpace.single (α j) (1 : ℝ)‖ := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ α : Fin n → Fin 3,
          (∏ j, ‖v j‖) * ‖L fun j => EuclideanSpace.single (α j) (1 : ℝ)‖ := by
        refine Finset.sum_le_sum fun α _ => mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have : |∏ j, v j (α j)| = ∏ j, |v j (α j)| := by
          simp [Finset.abs_prod]
        rw [this]
        refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun j _ => ?_
        rw [← Real.norm_eq_abs]
        exact PiLp.norm_apply_le _ _
    _ = (∑ α : Fin n → Fin 3,
          ‖L fun j => EuclideanSpace.single (α j) (1 : ℝ)‖) * ∏ j, ‖v j‖ := by
        rw [mul_comm, Finset.mul_sum]

/-- The `n`-th derivative of a field is bounded by the sum of its Fefferman multi-index terms. -/
lemma norm_iteratedFDeriv_le_sum_basis {f : VelocityField} (n : ℕ) (x : T3) :
    ‖iteratedFDeriv ℝ n f x‖ ≤
      ∑ α : Fin n → Fin 3,
        ‖iteratedFDeriv ℝ n f x (fun j => EuclideanSpace.single (α j) (1 : ℝ))‖ :=
  (norm_cmul_le_sum_basis (iteratedFDeriv ℝ n f x)).trans_eq rfl

lemma pow_mul_inv_one_add_le (x : E3) (k : ℕ) :
    ‖x‖ ^ k * (1 + ‖x‖) ^ (-(k : ℝ)) ≤ 1 := by
  have hw : 0 < 1 + ‖x‖ := by positivity
  have hle : ‖x‖ ≤ 1 + ‖x‖ := le_add_of_nonneg_left zero_le_one
  have hfrac : 0 ≤ ‖x‖ / (1 + ‖x‖) := div_nonneg (norm_nonneg _) hw.le
  have hfrac1 : ‖x‖ / (1 + ‖x‖) ≤ 1 := (div_le_one hw).2 hle
  have : (‖x‖ / (1 + ‖x‖)) ^ k ≤ 1 := pow_le_one₀ hfrac hfrac1
  calc ‖x‖ ^ k * (1 + ‖x‖) ^ (-(k : ℝ))
      = ‖x‖ ^ k * (1 + ‖x‖)⁻¹ ^ k := by
        rw [Real.rpow_neg hw.le, Real.rpow_natCast, inv_pow]
    _ = (‖x‖ / (1 + ‖x‖)) ^ k := by
        rw [← mul_pow, div_eq_mul_inv]
    _ ≤ 1 := this

/-- Fefferman decay implies the Schwartz seminorm bound of every order. -/
lemma decay_of_feffermanDecay {f : VelocityField} (h : FeffermanDecay f)
    (k n : ℕ) : ∃ C : ℝ, ∀ x : T3, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  -- For each multi-index, take the Fefferman constant at exponent `K = k`.
  have hα : ∀ α : Fin n → Fin 3, ∃ C : ℝ, ∀ x : T3,
      ‖iteratedFDeriv ℝ n f x (fun j => EuclideanSpace.single (α j) (1 : ℝ))‖ ≤
        C * (1 + ‖x‖) ^ (-(k : ℝ)) := fun α => h n α (k : ℝ)
  choose C0 hC0 using hα
  let C : (Fin n → Fin 3) → ℝ := fun α => max (C0 α) 0
  have hC : ∀ α x, ‖iteratedFDeriv ℝ n f x (fun j => EuclideanSpace.single (α j) (1 : ℝ))‖ ≤
      C α * (1 + ‖x‖) ^ (-(k : ℝ)) := fun α x =>
    (hC0 α x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hCpos : ∀ α, 0 ≤ C α := fun α => le_max_right _ _
  refine ⟨∑ α : Fin n → Fin 3, C α, fun x => ?_⟩
  have hsum :
      ‖iteratedFDeriv ℝ n f x‖ ≤
        (∑ α : Fin n → Fin 3, C α * (1 + ‖x‖) ^ (-(k : ℝ))) := by
    refine (norm_iteratedFDeriv_le_sum_basis n x).trans ?_
    exact Finset.sum_le_sum fun α _ => hC α x
  have hfactor :
      ∑ α : Fin n → Fin 3, C α * (1 + ‖x‖) ^ (-(k : ℝ)) =
        (∑ α : Fin n → Fin 3, C α) * (1 + ‖x‖) ^ (-(k : ℝ)) := by
    simp [Finset.sum_mul]
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖
      ≤ ‖x‖ ^ k * ((∑ α : Fin n → Fin 3, C α) * (1 + ‖x‖) ^ (-(k : ℝ))) := by
        rw [← hfactor]; exact mul_le_mul_of_nonneg_left hsum (pow_nonneg (norm_nonneg _) _)
    _ = (∑ α : Fin n → Fin 3, C α) * (‖x‖ ^ k * (1 + ‖x‖) ^ (-(k : ℝ))) := by
        ring
    _ ≤ (∑ α : Fin n → Fin 3, C α) * 1 :=
        mul_le_mul_of_nonneg_left (pow_mul_inv_one_add_le x k)
          (Finset.sum_nonneg fun α _ => hCpos α)
    _ = ∑ α : Fin n → Fin 3, C α := by rw [mul_one]

-- The last `?_` for nonnegativity of C α may fail: FeffermanDecay does not force C ≥ 0.
-- We'll fix after the first compile.

lemma norm_iteratedFDeriv_cplx_le {f : VelocityField} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (x : T3) :
    ‖iteratedFDeriv ℝ n (cplx ∘ f) x‖ ≤ ‖iteratedFDeriv ℝ n f x‖ := by
  have hcomp :=
    cplx.iteratedFDeriv_comp_left (hf.contDiffAt (x := x))
      (mod_cast le_top : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  -- After composition, the derivative is cplx applied to the original multilinear map.
  -- Since ‖cplx y‖ = ‖y‖, the operator norms agree up to ≤ ‖cplx‖ = 1.
  have hnorm : ‖cplx.compContinuousMultilinearMap (iteratedFDeriv ℝ n f x)‖ ≤
      ‖cplx‖ * ‖iteratedFDeriv ℝ n f x‖ :=
    ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
  have hc : ‖cplx‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound cplx (by norm_num) fun y => by
      rw [one_mul, norm_cplx]
  have : ‖iteratedFDeriv ℝ n (cplx ∘ f) x‖ ≤ ‖cplx‖ * ‖iteratedFDeriv ℝ n f x‖ := by
    rw [hcomp]; exact hnorm
  exact this.trans ((mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (one_mul _))

lemma decay_cplx_of_feffermanDecay {f : VelocityField} (hf : ContDiff ℝ ∞ f)
    (h : FeffermanDecay f) (k n : ℕ) :
    ∃ C : ℝ, ∀ x : T3, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (cplx ∘ f) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := decay_of_feffermanDecay h k n
  refine ⟨C, fun x => ?_⟩
  exact (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_cplx_le hf n x)
    (pow_nonneg (norm_nonneg _) k)).trans (hC x)

/-- The complexified Fefferman field as a Schwartz map `𝓢(ℝ³, ℂ³)`. -/
def toSchwartz (f : VelocityField) (hf : ContDiff ℝ ∞ f) (h : FeffermanDecay f) :
    𝓢(E3, V) where
  toFun := cplx ∘ f
  smooth' := cplx.contDiff.comp hf
  decay' := decay_cplx_of_feffermanDecay hf h

lemma toSchwartz_apply (f : VelocityField) (hf : ContDiff ℝ ∞ f) (h : FeffermanDecay f)
    (x : E3) : toSchwartz f hf h x = cplx (f x) := rfl

/-- **Fourier inversion for Fefferman data**: `𝓕⁻ (𝓕 (cplx ∘ f)) = cplx ∘ f` pointwise. -/
theorem fourierInv_fourier_cplx_of_fefferman {f : VelocityField}
    (hf : ContDiff ℝ ∞ f) (h : FeffermanDecay f) :
    𝓕⁻ (𝓕 (cplx ∘ f)) = cplx ∘ f := by
  set g := toSchwartz f hf h
  have hfun : (g : E3 → V) = cplx ∘ f := rfl
  rw [← hfun]
  exact g.continuous.fourierInv_fourier_eq g.integrable (by
    rw [← fourier_coe g]
    exact (𝓕 g).integrable)

#print axioms FeffermanSchwartz.norm_cmul_le_sum_basis
#print axioms FeffermanSchwartz.norm_iteratedFDeriv_le_sum_basis
#print axioms FeffermanSchwartz.decay_of_feffermanDecay
#print axioms FeffermanSchwartz.toSchwartz
#print axioms FeffermanSchwartz.fourierInv_fourier_cplx_of_fefferman

end FeffermanSchwartz
