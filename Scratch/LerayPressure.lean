import Scratch.ProductHm
import Scratch.NonlinearHm
import Scratch.FourierInvBCF
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! # Leray pressure of an `Ĥ^m` velocity slice

This file packages the Fourier-side Leray pressure

  `p̂(ξ) = -∑_{i,j} (ξᵢ ξⱼ / |ξ|²) (uᵢ uⱼ)^(ξ)`

of a velocity representative `u ∈ Ĥ^s` (`s ≥ 3`) as an element of `Ĥ^s`,
then realizes it as a physical scalar via `fourierInvBCF`. Statements are
written in terms of `fourierInvBCF` so that `𝓕⁻` does not appear in
elaborated types.

The symbol `ξᵢ ξⱼ / |ξ|²` is bounded by `1` (and is defined as `0` at
`ξ = 0`), so `p̂` is controlled by the Fourier-side products `(uᵢ uⱼ)^`,
which exist in `Ĥ^s` by `ProductHm.norm_mulF_le`.

**Momentum / `KatoMaximalSolution`.** `R3BKM.KatoMaximalSolution` is an
abstract existence Prop: it supplies some Fefferman-class pair `(u, p)`
with an H³ energy bound, but it does not identify `p` with the Leray
pressure of `u`, nor does it identify `u(t)` with the inverse Fourier
transform of a mild `Ĥ^m` path. `FeffermanMild.physicalMild` realizes
the persisted mild velocity, but this repository does not (yet) construct
a matching physical pressure or prove that
`(physicalMild, lerayPressure of the mild slice)` satisfies the momentum
equation, nor that this pair is the `(u, p)` of a `KatoMaximalSolution`.
The Fourier-side identity `N(u) = ℙ ∇·(u ⊗ u)` (`NonlinearHm.NSN`) is
consistent with that construction, but the physical-side identification
`(u·∇)u + ∇p = inverse Fourier of divTensor` is not formalized here.
That link is reported as a remaining gap; it is not assumed.

**Physical L² of `∂^α p`.** The Fourier representative `lerayPressureHm u` belongs
to `Ĥ^s` (hence to unweighted `L²` by `memLp_coe_Hm`). Realizing the *physical*
field `lerayPressure` in `L²`, or any spatial derivative of it, requires
identifying the pointwise inverse Fourier transform packaged by
`fourierInvBCF` with the `L²` isometry `Lp.fourierTransformₗᵢ` on
`L¹ ∩ L²`. Mathlib has this identification for Schwartz maps
(`SchwartzMap.toLp_fourierInv_eq`) and Plancherel on `L²` and on Schwartz,
but not for a general `Ĥ^m` representative. That identification is not
formalized in this repository, so the physical-side `L²` bounds on
`∂^α p` (and therefore the integrability and vanishing-flux fields of
`WordIBP`) are not claimed here.

Nothing in this file is a `sorry`, a custom axiom, or an `opaque` trick.
-/

open MeasureTheory Real Filter Topology Set BoundedContinuousFunction
open scoped ENNReal ContDiff Convolution

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
namespace LerayPressure

open LerayHeat SobolevFourier SobolevHilbert ProductHm NonlinearHm
open Nonlinear (coordCLM embedCLM embedCLM_apply norm_embedCLM_apply
  norm_coordCLM_apply)
open InverseSobolev FourierInvBCF
open NavierStokes3D (PressureField T3)

lemma two_le_of_three {s : ℕ} (hs : 3 ≤ s) : 2 ≤ s :=
  le_trans (by norm_num : 2 ≤ 3) hs

/-- Real-linear projection onto the `e₀` coordinate of `ℂ³`. -/
def coord0ℝ : V →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun v => v 0
      map_add' := fun _ _ => by simp
      map_smul' := fun c v => by
        change (c • v) 0 = c • v 0
        simp [Complex.real_smul] }
    1 fun v => (PiLp.norm_apply_le v 0).trans_eq (one_mul _).symm

lemma coord0ℝ_apply (v : V) : coord0ℝ v = v 0 := rfl

/-! ## The Riesz symbol `ξᵢ ξⱼ / |ξ|²` -/

/-- Homogeneous degree-zero symbol, defined as `0` at the origin so that it
is defined on all of `ℝ³`. It is bounded by `1` (the `1/|ξ|²` singularity
is cancelled by `ξᵢ ξⱼ`). -/
def rieszCoeff (i j : Fin 3) (ξ : E3) : ℝ :=
  if ‖ξ‖ = 0 then 0 else ξ i * ξ j / ‖ξ‖ ^ 2

lemma abs_coord_le_norm (ξ : E3) (i : Fin 3) : |ξ i| ≤ ‖ξ‖ := by
  have hsq : ξ i ^ 2 ≤ ‖ξ‖ ^ 2 := by
    have hsum := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 3)))
      (f := fun k : Fin 3 => ξ k ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
    have hnorm : ‖ξ‖ ^ 2 = ∑ k : Fin 3, ξ k ^ 2 := by
      simp [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    exact hsum.trans_eq hnorm.symm
  exact abs_le_of_sq_le_sq hsq (norm_nonneg ξ)

lemma abs_rieszCoeff_le (i j : Fin 3) (ξ : E3) : |rieszCoeff i j ξ| ≤ 1 := by
  unfold rieszCoeff
  split_ifs with h
  · simp
  · have hi := abs_coord_le_norm ξ i
    have hj := abs_coord_le_norm ξ j
    have hξ : 0 < ‖ξ‖ := lt_of_le_of_ne (norm_nonneg ξ) (Ne.symm h)
    rw [abs_div, abs_mul]
    have hden : 0 < ‖ξ‖ ^ 2 := pow_pos hξ 2
    rw [abs_pow, abs_norm, div_le_one hden]
    have hnum : |ξ i| * |ξ j| ≤ ‖ξ‖ * ‖ξ‖ :=
      mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)
    simpa [pow_two] using hnum

lemma measurable_rieszCoeff (i j : Fin 3) : Measurable (rieszCoeff i j) := by
  have hset : MeasurableSet {ξ : E3 | ‖ξ‖ = 0} :=
    (isClosed_eq continuous_norm continuous_const).measurableSet
  unfold rieszCoeff
  exact Measurable.ite hset measurable_const
    ((((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable).mul
        (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable).div
      (continuous_norm.measurable.pow_const 2))

/-- The same symbol as a multiplier on `ℂ³`. -/
def rieszSym (i j : Fin 3) (ξ : E3) : V →L[ℂ] V :=
  (rieszCoeff i j ξ : ℂ) • ContinuousLinearMap.id ℂ V

lemma rieszSym_apply (i j : Fin 3) (ξ : E3) (v : V) :
    rieszSym i j ξ v = (rieszCoeff i j ξ : ℂ) • v := by
  simp [rieszSym]

lemma rieszSym_norm_le (i j : Fin 3) (ξ : E3) : ‖rieszSym i j ξ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [rieszSym_apply, norm_smul]
  have hcoeff : ‖(rieszCoeff i j ξ : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real] using abs_rieszCoeff_le i j ξ
  exact mul_le_mul_of_nonneg_right hcoeff (norm_nonneg v)

lemma rieszSym_meas (i j : Fin 3) (g : E3 → V) (hg : AEStronglyMeasurable g) :
    AEStronglyMeasurable (fun ξ => rieszSym i j ξ (g ξ)) := by
  have hfun : (fun ξ => rieszSym i j ξ (g ξ)) =
      fun ξ => (rieszCoeff i j ξ : ℂ) • g ξ :=
    funext fun ξ => rieszSym_apply i j ξ (g ξ)
  rw [hfun]
  have hc : AEStronglyMeasurable (fun ξ : E3 => (rieszCoeff i j ξ : ℂ)) :=
    (Complex.ofRealCLM.continuous.measurable.comp (measurable_rieszCoeff i j)).aestronglyMeasurable
  exact hc.smul hg

lemma bound_riesz (i j : Fin 3) (s : ℕ) (ξ : E3) :
    sobW s ξ * ‖rieszSym i j ξ‖ₑ ^ 2 ≤ ENNReal.ofReal 1 * sobW s ξ := by
  have hn : ‖rieszSym i j ξ‖ ≤ 1 := rieszSym_norm_le i j ξ
  have h1 : ‖rieszSym i j ξ‖ₑ ^ 2 ≤ 1 := by
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (pow_le_one₀ (norm_nonneg _) hn)
  rw [ENNReal.ofReal_one, one_mul]
  simpa [mul_one] using mul_le_mul_of_nonneg_left h1 (zero_le (sobW s ξ))

/-- Bounded multiplier `Ĥ^s → Ĥ^s` given by `ξᵢ ξⱼ / |ξ|²`. -/
def rieszMul (i j : Fin 3) (s : ℕ) : Hm s →L[ℂ] Hm s :=
  wmul (rieszSym i j) (rieszSym_meas i j) 1 zero_le_one (bound_riesz i j s)

lemma norm_rieszMul_le (i j : Fin 3) (s : ℕ) (G : Hm s) :
    ‖rieszMul i j s G‖ ≤ ‖G‖ := by
  simpa using
    norm_wmul_le (rieszSym i j) (rieszSym_meas i j) 1 zero_le_one (bound_riesz i j s) G

/-! ## The product bilinear maps `(u, v) ↦ (uᵢ vⱼ) e₀` -/

/-- Bilinear map `(u, v) ↦ (uᵢ vⱼ) e₀`, so that the scalar product lives in
a fixed slot of an `Ĥ^s` representative. -/
def Lprod (i j : Fin 3) : V →L[ℂ] V →L[ℂ] V :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (fun u v => embedCLM 0 (coordCLM i u * coordCLM j v))
      (fun u₁ u₂ v => by simp [add_mul])
      (fun c u v => by
        change embedCLM 0 (coordCLM i (c • u) * coordCLM j v) =
          c • embedCLM 0 (coordCLM i u * coordCLM j v)
        rw [map_smul, smul_mul_assoc, map_smul])
      (fun u v₁ v₂ => by simp [mul_add])
      (fun c u v => by
        change embedCLM 0 (coordCLM i u * coordCLM j (c • v)) =
          c • embedCLM 0 (coordCLM i u * coordCLM j v)
        rw [map_smul, mul_smul_comm, map_smul]))
    1 fun u v => by
      rw [LinearMap.mk₂_apply, one_mul, norm_embedCLM_apply, norm_mul]
      exact mul_le_mul (norm_coordCLM_apply i u) (norm_coordCLM_apply j v)
        (norm_nonneg _) (norm_nonneg _)

lemma Lprod_apply (i j : Fin 3) (u v : V) :
    Lprod i j u v = embedCLM 0 (coordCLM i u * coordCLM j v) :=
  rfl

lemma opNorm_Lprod_le (i j : Fin 3) : ‖Lprod i j‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg zero_le_one (norm_nonneg u)) fun v => ?_
  change ‖Lprod i j u v‖ ≤ 1 * ‖u‖ * ‖v‖
  rw [Lprod_apply, one_mul, norm_embedCLM_apply, norm_mul]
  exact mul_le_mul (norm_coordCLM_apply i u) (norm_coordCLM_apply j v)
    (norm_nonneg _) (norm_nonneg _)

/-! ## Fourier-side Leray pressure, as an `Ĥ^s` representative -/

/-- Fourier-side Leray pressure of `u ∈ Ĥ^s`, as an element of `Ĥ^s`. -/
def lerayPressureHm {s : ℕ} (hs : 3 ≤ s) (u : Hm s) : Hm s :=
  -∑ i : Fin 3, ∑ j : Fin 3, rieszMul i j s (mulF (Lprod i j) hs u u)

lemma norm_lerayPressureHm_le {s : ℕ} (hs : 3 ≤ s) (u : Hm s) :
    ‖lerayPressureHm hs u‖ ≤
      9 * Cm s * (‖u‖ * ‖incl hs u‖ + ‖incl hs u‖ * ‖u‖) := by
  unfold lerayPressureHm
  have hterm : ∀ i j : Fin 3,
      ‖rieszMul i j s (mulF (Lprod i j) hs u u)‖ ≤
        Cm s * (‖u‖ * ‖incl hs u‖ + ‖incl hs u‖ * ‖u‖) := by
    intro i j
    have hR := norm_rieszMul_le i j s (mulF (Lprod i j) hs u u)
    have hM := norm_mulF_le (Lprod i j) hs u u
    have hL := opNorm_Lprod_le i j
    have hC : 0 ≤ Cm s := Cm_nonneg s
    have hsum : 0 ≤ ‖u‖ * ‖incl hs u‖ + ‖incl hs u‖ * ‖u‖ :=
      add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have hmul : ‖mulF (Lprod i j) hs u u‖ ≤
        Cm s * (‖u‖ * ‖incl hs u‖ + ‖incl hs u‖ * ‖u‖) := by
      refine hM.trans ?_
      calc Cm s * ‖Lprod i j‖ * (‖u‖ * ‖incl hs u‖ + ‖incl hs u‖ * ‖u‖)
          ≤ Cm s * 1 * _ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL hC) hsum
        _ = _ := by ring
    exact hR.trans hmul
  have hsum₁ :
      ‖∑ i : Fin 3, ∑ j : Fin 3, rieszMul i j s (mulF (Lprod i j) hs u u)‖ ≤
        ∑ i : Fin 3, ∑ j : Fin 3,
          ‖rieszMul i j s (mulF (Lprod i j) hs u u)‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
  have hsum₂ :
      ∑ i : Fin 3, ∑ j : Fin 3,
          ‖rieszMul i j s (mulF (Lprod i j) hs u u)‖ ≤
        ∑ _i : Fin 3, ∑ _j : Fin 3,
          Cm s * (‖u‖ * ‖incl hs u‖ + ‖incl hs u‖ * ‖u‖) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  have hcard : ∑ _i : Fin 3, ∑ _j : Fin 3,
      Cm s * (‖u‖ * ‖incl hs u‖ + ‖incl hs u‖ * ‖u‖) =
        9 * Cm s * (‖u‖ * ‖incl hs u‖ + ‖incl hs u‖ * ‖u‖) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
    ring
  have : ‖∑ i : Fin 3, ∑ j : Fin 3, rieszMul i j s (mulF (Lprod i j) hs u u)‖ ≤
      9 * Cm s * (‖u‖ * ‖incl hs u‖ + ‖incl hs u‖ * ‖u‖) :=
    hsum₁.trans (hsum₂.trans_eq hcard)
  simpa [norm_neg] using this

/-! ## Unweighted `L²` of an `Ĥ^m` representative (Fourier side) -/

/-- Because `sobW m ≥ 1`, membership in `Ĥ^m` implies unweighted `L²`. -/
lemma eLpNorm_coe_Hm_le_weighted {m : ℕ} (G : Hm m) :
    eLpNorm (G : E3 → V) 2 volume ≤ eLpNorm (G : E3 → V) 2 (μw m) := by
  have hsq : eLpNorm (G : E3 → V) 2 volume ^ 2 ≤
      eLpNorm (G : E3 → V) 2 (μw m) ^ 2 := by
    rw [eLpNorm_sq, eLpNorm_sq, lintegral_μw]
    refine lintegral_mono fun ξ => ?_
    have h1 := mul_le_mul_left (one_le_sobW m ξ) (‖(G : E3 → V) ξ‖ₑ ^ 2)
    exact (one_mul _).symm.trans_le h1
  have hvol : eLpNorm (G : E3 → V) 2 volume ^ (2 : ℝ) =
      eLpNorm (G : E3 → V) 2 volume ^ 2 := ENNReal.rpow_natCast _ 2
  have hμ : eLpNorm (G : E3 → V) 2 (μw m) ^ (2 : ℝ) =
      eLpNorm (G : E3 → V) 2 (μw m) ^ 2 := ENNReal.rpow_natCast _ 2
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).1
    (hvol.trans_le (hsq.trans_eq hμ.symm))

lemma memLp_coe_Hm {m : ℕ} (G : Hm m) : MemLp (G : E3 → V) 2 volume :=
  ⟨(Lp.aestronglyMeasurable G).mono_ac (ac_vol m),
    (eLpNorm_coe_Hm_le_weighted G).trans_lt (Lp.eLpNorm_lt_top G)⟩

lemma eLpNorm_coe_Hm_le {m : ℕ} (G : Hm m) :
    eLpNorm (G : E3 → V) 2 volume ≤ ENNReal.ofReal ‖G‖ := by
  refine (eLpNorm_coe_Hm_le_weighted G).trans ?_
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top G)]

/-- The Fourier-side Leray pressure is in unweighted `L²`. -/
lemma memLp_lerayPressureHm {s : ℕ} (hs : 3 ≤ s) (u : Hm s) :
    MemLp (lerayPressureHm hs u : E3 → V) 2 volume :=
  memLp_coe_Hm _

/-! ## Physical Leray pressure, packaged through `fourierInvBCF` -/

/-- Inverse Fourier of an `Ĥ^m` representative, as an unbundled map.
Marked irreducible so that elaborated types do not unfold to `𝓕⁻`. -/
irreducible_def physicalInv {m : ℕ} (hm : 2 ≤ m) (G : Hm m) : E3 → V :=
  ⇑(fourierInvBCF hm G)

lemma physicalInv_irrel {m : ℕ} (h1 h2 : 2 ≤ m) (G : Hm m) :
    physicalInv h1 G = physicalInv h2 G := by
  unfold physicalInv
  rfl

lemma continuous_physicalInv {m : ℕ} (hm : 2 ≤ m) (G : Hm m) :
    Continuous (physicalInv hm G) := by
  rw [physicalInv]
  exact (fourierInvBCF hm G).continuous

lemma norm_physicalInv_le {m : ℕ} (hm : 2 ≤ m) (G : Hm m) (x : E3) :
    ‖physicalInv hm G x‖ ≤ ‖fourierInvBCF hm G‖ := by
  rw [physicalInv]
  exact BoundedContinuousFunction.norm_coe_le_norm _ x

/-- Physical Leray pressure of an `Ĥ^s` slice: the real part of the `e₀`
component of `physicalInv` of `lerayPressureHm`. -/
def lerayPressure {s : ℕ} (hs : 3 ≤ s) (u : Hm s) : PressureField :=
  fun x => (physicalInv (two_le_of_three hs) (lerayPressureHm hs u) x 0).re

lemma continuous_lerayPressure {s : ℕ} (hs : 3 ≤ s) (u : Hm s) :
    Continuous (lerayPressure hs u) := by
  have hBCF := continuous_physicalInv (two_le_of_three hs) (lerayPressureHm hs u)
  exact Complex.continuous_re.comp (coord0ℝ.continuous.comp hBCF)

lemma abs_lerayPressure_le {s : ℕ} (hs : 3 ≤ s) (u : Hm s) (x : E3) :
    |lerayPressure hs u x| ≤
      ‖fourierInvBCF (two_le_of_three hs) (lerayPressureHm hs u)‖ := by
  have h2 := two_le_of_three hs
  have hv := norm_physicalInv_le h2 (lerayPressureHm hs u) x
  have hre : |lerayPressure hs u x| ≤
      ‖physicalInv h2 (lerayPressureHm hs u) x‖ := by
    unfold lerayPressure
    have hr : |((physicalInv h2 (lerayPressureHm hs u) x) 0).re| ≤
        ‖(physicalInv h2 (lerayPressureHm hs u) x) 0‖ :=
      Complex.abs_re_le_norm _
    exact hr.trans (PiLp.norm_apply_le _ 0)
  exact hre.trans hv

lemma bddAbove_lerayPressure {s : ℕ} (hs : 3 ≤ s) (u : Hm s) :
    BddAbove (range fun x => |lerayPressure hs u x|) := by
  refine ⟨‖fourierInvBCF (two_le_of_three hs) (lerayPressureHm hs u)‖, ?_⟩
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  exact abs_lerayPressure_le hs u x

lemma two_le_of_add {n m : ℕ} (hn : n + 2 ≤ m) : 2 ≤ m :=
  (Nat.le_add_left 2 n).trans hn

/-- Inverse Fourier of an `Ĥ^m` representative is `C^n` for `m ≥ n + 2`.
The statement is packaged through `physicalInv` so that `𝓕⁻` does not
appear in the elaborated type. -/
theorem contDiff_physicalInv {m n : ℕ} (hn : n + 2 ≤ m) (G : Hm m) :
    ContDiff ℝ n (physicalInv (two_le_of_add hn) G) := by
  rw [physicalInv]
  exact contDiff_fourierInv_of_Hm hn G

/-- The physical Leray pressure is `C^n` as soon as `s ≥ n + 2`. -/
theorem contDiff_lerayPressure {s n : ℕ} (hs : 3 ≤ s) (hn : n + 2 ≤ s)
    (u : Hm s) : ContDiff ℝ n (lerayPressure hs u) := by
  have hinv := contDiff_physicalInv hn (lerayPressureHm hs u)
  have hinv' : ContDiff ℝ n
      (physicalInv (two_le_of_three hs) (lerayPressureHm hs u)) := by
    rw [physicalInv_irrel (two_le_of_three hs) (two_le_of_add hn)]
    exact hinv
  exact Complex.reCLM.contDiff.comp (coord0ℝ.contDiff.comp hinv')

/-- For `s ≥ 2 + 2 = 4`, the Leray pressure is in particular `C²`, hence
every first- and second-order partial exists and is continuous. -/
theorem contDiff_two_lerayPressure {s : ℕ} (hs : 4 ≤ s) (u : Hm s) :
    ContDiff ℝ 2 (lerayPressure (le_trans (by norm_num : 3 ≤ 4) hs) u) :=
  contDiff_lerayPressure (le_trans (by norm_num : 3 ≤ 4) hs)
    (by exact hs) u

/-- For `s ≥ 5 + 2 = 7`, the Leray pressure is `C^5`, which is the
spatial regularity used by the order-three fields of `WordIBP`
(third derivatives of a `C²` pressure). -/
theorem contDiff_five_lerayPressure {s : ℕ} (hs : 7 ≤ s) (u : Hm s) :
    ContDiff ℝ 5 (lerayPressure (le_trans (by norm_num : 3 ≤ 7) hs) u) :=
  contDiff_lerayPressure (le_trans (by norm_num : 3 ≤ 7) hs)
    (by exact hs) u

#print axioms LerayPressure.memLp_coe_Hm
#print axioms LerayPressure.memLp_lerayPressureHm
#print axioms LerayPressure.abs_rieszCoeff_le
#print axioms LerayPressure.contDiff_physicalInv
#print axioms LerayPressure.norm_rieszMul_le
#print axioms LerayPressure.norm_lerayPressureHm_le
#print axioms LerayPressure.continuous_lerayPressure
#print axioms LerayPressure.bddAbove_lerayPressure
#print axioms LerayPressure.contDiff_lerayPressure
#print axioms LerayPressure.contDiff_five_lerayPressure

end LerayPressure
