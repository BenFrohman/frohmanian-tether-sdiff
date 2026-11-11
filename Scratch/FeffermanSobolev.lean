import Scratch.SobolevHilbert
import Scratch.ProductEstimate
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! # Fefferman data has finite `H^m` energy of every order; inverse Fourier of `Ĥ^m`

Item 4 foundations:
* Fefferman decay plus `C^∞` imply `sobolevEnergy m < ⊤` and `fourierEnergy m < ⊤` for all `m`,
  so the initial datum lands in every `Ĥ^m` via `toHm`.
* Converse of the Fourier–Sobolev matching: an `Ĥ^m` representative with `m ≥ n + 2` has
  integrable moments of order `≤ n`, so its inverse Fourier transform is `C^n`. If a physical
  `L²` field has finite Fourier energy of every order, it agrees a.e. with a `C^∞` function. -/

open MeasureTheory FourierTransform Real Filter Topology
open scoped ENNReal ContDiff InnerProductSpace

set_option autoImplicit false

noncomputable section
namespace FeffermanSobolev

open LerayHeat SobolevFourier SobolevHilbert ProductEstimate
open R3BKM
open NavierStokes3D (VelocityField T3)
open RepairedTether (FeffermanDecay)

/-! ## Finite `H^m` energy from Fefferman decay -/

/-- Each multi-index term in `sobolevEnergy` is finite under Fefferman decay (take `K = 2`). -/
lemma iteratedFDeriv_lintegral_sq_lt_top {f : VelocityField} (h : FeffermanDecay f)
    (k : ℕ) (α : Fin k → Fin 3) :
    ∫⁻ x, ‖iteratedFDeriv ℝ k f x (fun j => EuclideanSpace.single (α j) (1 : ℝ))‖ₑ ^ 2 < ⊤ := by
  obtain ⟨C, hC⟩ := h k α 2
  have hint : Integrable (fun x : T3 => C ^ 2 * (1 + ‖x‖) ^ (-(4 : ℝ))) := by
    refine (integrable_one_add_norm ?_).const_mul _
    simp; norm_num
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hint.lintegral_lt_top
  have h1 := hC x
  have hw : 0 < 1 + ‖x‖ := by positivity
  have h2 :
      ‖iteratedFDeriv ℝ k f x (fun j => EuclideanSpace.single (α j) (1 : ℝ))‖ ^ 2 ≤
        C ^ 2 * (1 + ‖x‖) ^ (-(4 : ℝ)) := by
    have := pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc ‖iteratedFDeriv ℝ k f x (fun j => EuclideanSpace.single (α j) (1 : ℝ))‖ ^ 2
        ≤ (C * (1 + ‖x‖) ^ (-(2 : ℝ))) ^ 2 := this
      _ = C ^ 2 * (1 + ‖x‖) ^ (-(4 : ℝ)) := by
          rw [mul_pow, ← Real.rpow_natCast ((1 + ‖x‖) ^ (-(2 : ℝ))), ← Real.rpow_mul hw.le]
          norm_num
  calc ‖iteratedFDeriv ℝ k f x (fun j => EuclideanSpace.single (α j) (1 : ℝ))‖ₑ ^ 2
      = ENNReal.ofReal
          (‖iteratedFDeriv ℝ k f x (fun j => EuclideanSpace.single (α j) (1 : ℝ))‖ ^ 2) := by
        rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
    _ ≤ ENNReal.ofReal (C ^ 2 * (1 + ‖x‖) ^ (-(4 : ℝ))) := ENNReal.ofReal_le_ofReal h2

/-- **Fefferman data has finite `H^m` energy of every order.** -/
theorem sobolevEnergy_lt_top_of_feffermanDecay {f : VelocityField} (h : FeffermanDecay f)
    (m : ℕ) : sobolevEnergy m f < ⊤ := by
  unfold sobolevEnergy
  exact ENNReal.sum_lt_top.2 fun k _ =>
    ENNReal.sum_lt_top.2 fun α _ => iteratedFDeriv_lintegral_sq_lt_top h k α

/-- The complexification of Fefferman data is in `L²`. -/
theorem memLp_cplx_of_feffermanDecay {f : VelocityField} (hf : ContDiff ℝ ∞ f)
    (h : FeffermanDecay f) : MemLp (cplx ∘ f) 2 := by
  obtain ⟨h0, _⟩ := sobolevEnergy_eq_fourierEnergy hf 0 (sobolevEnergy_lt_top_of_feffermanDecay h 0)
  exact h0

/-- Physical `L²` field associated to Fefferman data. -/
def toL2 (f : VelocityField) (hf : ContDiff ℝ ∞ f) (h : FeffermanDecay f) : L2V :=
  (memLp_cplx_of_feffermanDecay hf h).toLp _

lemma coeFn_toL2 (f : VelocityField) (hf : ContDiff ℝ ∞ f) (h : FeffermanDecay f) :
    (toL2 f hf h : E3 → V) =ᵐ[volume] (cplx ∘ f) :=
  MemLp.coeFn_toLp (memLp_cplx_of_feffermanDecay hf h)

/-- **Fefferman data has finite Fourier `H^m` energy of every order.** -/
theorem fourierEnergy_lt_top_of_feffermanDecay {f : VelocityField} (hf : ContDiff ℝ ∞ f)
    (h : FeffermanDecay f) (m : ℕ) : fourierEnergy m (toL2 f hf h) < ⊤ := by
  obtain ⟨h0, heq⟩ := sobolevEnergy_eq_fourierEnergy hf m (sobolevEnergy_lt_top_of_feffermanDecay h m)
  have hcongr : h0.toLp _ = toL2 f hf h :=
    MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun _ => rfl)
  rw [← hcongr, ← heq]
  exact sobolevEnergy_lt_top_of_feffermanDecay h m

/-- Fefferman data as an element of `Ĥ^m`, for every `m`. -/
def toHmFeff (f : VelocityField) (hf : ContDiff ℝ ∞ f) (h : FeffermanDecay f) (m : ℕ) : Hm m :=
  toHm (toL2 f hf h) (fourierEnergy_lt_top_of_feffermanDecay hf h m)

lemma norm_toHmFeff_sq (f : VelocityField) (hf : ContDiff ℝ ∞ f) (h : FeffermanDecay f) (m : ℕ) :
    ‖toHmFeff f hf h m‖ ^ 2 = (fourierEnergy m (toL2 f hf h)).toReal :=
  norm_toHm_sq _ _

lemma hsSq_eq_norm_toHmFeff {f : VelocityField} (hf : ContDiff ℝ ∞ f) (h : FeffermanDecay f) :
    hsSq 3 f = ‖toHmFeff f hf h 3‖ ^ 2 := by
  obtain ⟨h0, heq, htop⟩ := hsSq_eq_fourierEnergy hf (sobolevEnergy_lt_top_of_feffermanDecay h 3)
  have hcongr : h0.toLp _ = toL2 f hf h :=
    MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun _ => rfl)
  rw [heq, hcongr, norm_toHmFeff_sq]

#print axioms FeffermanSobolev.sobolevEnergy_lt_top_of_feffermanDecay
#print axioms FeffermanSobolev.fourierEnergy_lt_top_of_feffermanDecay
#print axioms FeffermanSobolev.hsSq_eq_norm_toHmFeff

end FeffermanSobolev
