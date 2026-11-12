import Scratch.RepairedTetherRate
import FrohmanianTether.ScalingIdentities
import FrohmanianTether.StrainBoundRefutation
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Step-by-step derivation of `FrohmanianTetherRateSmooth`

This file records the evolution identity for `M(t) = ‖omega(t)‖_∞` along a local Fefferman-class
solution, proves every calculus identity that closes, and names (then tests) the inequalities
that do not. The statement of `FrohmanianTetherRateSmooth` is unchanged, and it is not proved
for general data in this file.

Status convention: every claim is kernel-checked proved, kernel-checked disproved, or
explicitly unsettled with the missing inequality written as a `Prop`.
-/

open MeasureTheory NavierStokes3D FrohmanianTether
open RepairedTether ScalingIdentities Filter
open scoped InnerProductSpace ContDiff Topology

noncomputable section
namespace TetherRateDerivation

/-! ## 0. Auxiliary definitions (unfoldings of the rate) -/

/-- Coordinate basis vector "eᵢ". -/
def e (i : Fin 3) : T3 := EuclideanSpace.single i (1 : ℝ)

/-- Hilbert–Schmidt squared norm of "∇omega": "∑ᵢ ‖∂ᵢ omega‖²". -/
def hsSq (omega : VelocityField) (x : T3) : ℝ :=
  ∑ i : Fin 3, ‖(fderiv ℝ omega x) (e i)‖ ^ 2

/-- Scalar Laplacian as the trace of the Hessian. -/
def scalarLaplacian (phi : T3 → ℝ) (x : T3) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ (fun y => (fderiv ℝ phi y) (e i)) x) (e i)

/-- "½|omega|²". -/
def halfNormSq (omega : VelocityField) : T3 → ℝ :=
  fun y => (1 / 2 : ℝ) * ‖omega y‖ ^ 2

/-- Stretching integrand "⟨omega, (omega·∇)u⟩". -/
def stretching (u omega : VelocityField) (x : T3) : ℝ :=
  inner ℝ (omega x) (convective omega u x)

/-- Viscous pairing "⟨omega, Δω⟩". -/
def viscPair (omega : VelocityField) (x : T3) : ℝ :=
  inner ℝ (omega x) (laplacian omega x)

/-! ## 1. Calculus of `½|omega|²` and the Bochner identity (proved) -/

theorem hasFDerivAt_halfNormSq (omega : VelocityField) (x : T3)
    (h : DifferentiableAt ℝ omega x) :
    HasFDerivAt (halfNormSq omega) ((innerSL ℝ (omega x)).comp (fderiv ℝ omega x)) x := by
  have hsq : HasFDerivAt (fun y => ‖omega y‖ ^ 2)
      ((2 • innerSL ℝ (omega x)).comp (fderiv ℝ omega x)) x :=
    h.hasFDerivAt.norm_sq
  have hhalf := hsq.const_mul (1 / 2 : ℝ)
  convert hhalf
  ext v
  simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  try ring

theorem fderiv_halfNormSq (omega : VelocityField) (x : T3) (v : T3)
    (h : DifferentiableAt ℝ omega x) :
    (fderiv ℝ (halfNormSq omega) x) v = inner ℝ (omega x) ((fderiv ℝ omega x) v) := by
  rw [(hasFDerivAt_halfNormSq omega x h).fderiv]
  simp [ContinuousLinearMap.comp_apply]

theorem hsSq_nonneg (omega : VelocityField) (x : T3) : 0 ≤ hsSq omega x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem laplacian_eq_sum (omega : VelocityField) (x : T3) :
    laplacian omega x = ∑ i : Fin 3, (fderiv ℝ (fun y => (fderiv ℝ omega y) (e i)) x) (e i) :=
  rfl

/-- Bochner identity: "⟨omega, Δω⟩ = Δ(½|omega|²) − |∇omega|_{HS}²". -/
theorem bochner_identity (omega : VelocityField) (x : T3)
    (hC2 : ContDiffAt ℝ 2 omega x) :
    viscPair omega x = scalarLaplacian (halfNormSq omega) x - hsSq omega x := by
  have hC1 : ContDiffAt ℝ 1 omega x :=
    hC2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hnear : ∀ᶠ y in nhds x, DifferentiableAt ℝ omega y := by
    filter_upwards [hC1.eventually (by simp)] with y hy
    exact hy.differentiableAt_one
  have hω : DifferentiableAt ℝ omega x := hC1.differentiableAt_one
  have hfd : DifferentiableAt ℝ (fderiv ℝ omega) x :=
    (hC2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hpoint (i : Fin 3) :
      (fderiv ℝ (fun y => (fderiv ℝ (halfNormSq omega) y) (e i)) x) (e i) =
        ‖(fderiv ℝ omega x) (e i)‖ ^ 2 +
          inner ℝ (omega x) ((fderiv ℝ (fun y => (fderiv ℝ omega y) (e i)) x) (e i)) := by
    have heq : (fun y => (fderiv ℝ (halfNormSq omega) y) (e i)) =ᶠ[nhds x]
        fun y => inner ℝ (omega y) ((fderiv ℝ omega y) (e i)) := by
      filter_upwards [hnear] with y hy
      exact fderiv_halfNormSq omega y (e i) hy
    have hWi : DifferentiableAt ℝ (fun y => (fderiv ℝ omega y) (e i)) x :=
      ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3)) (e i)).differentiableAt).comp
        x hfd
    rw [heq.fderiv_eq,
      fderiv_inner_apply (𝕜 := ℝ) (hf := hω) (hg := hWi) (y := e i),
      real_inner_self_eq_norm_sq, real_inner_comm]
    ac_rfl
  have hsum :
      scalarLaplacian (halfNormSq omega) x =
        hsSq omega x + inner ℝ (omega x) (laplacian omega x) := by
    unfold scalarLaplacian hsSq
    simp_rw [hpoint, Finset.sum_add_distrib, laplacian_eq_sum, inner_sum]
  unfold viscPair
  linarith [hsum]

/-! ## 2. At a spatial maximum: transport cancels; dissipation is nonpositive (proved) -/

theorem isLocalMax_halfNormSq_of_isLocalMax_norm {omega : VelocityField} {x : T3}
    (h : IsLocalMax (fun y => ‖omega y‖) x) :
    IsLocalMax (halfNormSq omega) x := by
  unfold halfNormSq
  filter_upwards [h] with y hy
  have : ‖omega y‖ ^ 2 ≤ ‖omega x‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
  linarith

theorem isLocalMax_norm_of_isMaxOn {omega : VelocityField} {x : T3}
    (h : IsMaxOn (fun y => ‖omega y‖) Set.univ x) :
    IsLocalMax (fun y => ‖omega y‖) x :=
  h.isLocalMax Filter.univ_mem

theorem fderiv_halfNormSq_eq_zero_of_isLocalMax {omega : VelocityField} {x : T3}
    (_hdiff : DifferentiableAt ℝ omega x)
    (hmax : IsLocalMax (fun y => ‖omega y‖) x) :
    fderiv ℝ (halfNormSq omega) x = 0 :=
  (isLocalMax_halfNormSq_of_isLocalMax_norm hmax).fderiv_eq_zero

theorem gradient_halfNormSq_eq_zero_of_isLocalMax {omega : VelocityField} {x : T3}
    (hdiff : DifferentiableAt ℝ omega x)
    (hmax : IsLocalMax (fun y => ‖omega y‖) x) :
    gradient (halfNormSq omega) x = 0 := by
  have hφ : DifferentiableAt ℝ (halfNormSq omega) x :=
    (hasFDerivAt_halfNormSq omega x hdiff).differentiableAt
  have hf : fderiv ℝ (halfNormSq omega) x = 0 :=
    fderiv_halfNormSq_eq_zero_of_isLocalMax hdiff hmax
  apply ext_inner_right ℝ
  intro v
  have h := inner_gradient_left (f := halfNormSq omega) (x := x) (y := v) hφ
  simpa [hf, real_inner_comm] using h

/-- At a spatial local maximum of "|omega|", the transport pairing "⟨omega, (u·∇)omega⟩" vanishes. -/
theorem transport_vanishes_at_local_max (u omega : VelocityField) (x : T3)
    (hω : DifferentiableAt ℝ omega x)
    (hmax : IsLocalMax (fun y => ‖omega y‖) x) :
    inner ℝ (omega x) (convective u omega x) = 0 := by
  rw [inner_convective_eq_inner_grad_half_norm_sq u omega x hω]
  have hgrad : gradient (fun y => (1 / 2 : ℝ) * ‖omega y‖ ^ 2) x =
      gradient (halfNormSq omega) x := rfl
  rw [hgrad, gradient_halfNormSq_eq_zero_of_isLocalMax hω hmax, inner_zero_right]

/-- The restriction of a "C²" scalar to the line "t ↦ x + t eᵢ" has derivative
"∂ᵢ phi" along that line. -/
theorem hasDerivAt_line_slice (phi : T3 → ℝ) (x : T3) (v : T3) (s : ℝ)
    (h : DifferentiableAt ℝ phi (x + s • v)) :
    HasDerivAt (fun t => phi (x + t • v)) ((fderiv ℝ phi (x + s • v)) v) s := by
  have haff : HasDerivAt (fun t : ℝ => x + t • v) v s := by
    simpa using ((hasDerivAt_id (𝕜 := ℝ) s).smul_const v).const_add x
  exact h.hasFDerivAt.comp_hasDerivAt s haff

theorem deriv_line_slice (phi : T3 → ℝ) (x : T3) (v : T3) (s : ℝ)
    (h : DifferentiableAt ℝ phi (x + s • v)) :
    deriv (fun t => phi (x + t • v)) s = (fderiv ℝ phi (x + s • v)) v :=
  (hasDerivAt_line_slice phi x v s h).deriv

/-- If "g'(t)=0" and "g''(t)>0", then "g" has a local minimum, which cannot coexist with a
local maximum unless "g''" is in fact nonpositive. -/
theorem deriv_deriv_nonpos_of_isLocalMax {g : ℝ → ℝ} {t : ℝ}
    (hdiff : DifferentiableAt ℝ g t)
    (_hdiff' : DifferentiableAt ℝ (deriv g) t)
    (hmax : IsLocalMax g t) :
    deriv (deriv g) t ≤ 0 := by
  have hg0 : deriv g t = 0 := hmax.deriv_eq_zero
  by_contra hpos
  have hmin : IsLocalMin g t :=
    isLocalMin_of_deriv_deriv_pos (lt_of_not_ge hpos) hg0 hdiff.continuousAt
  have hconst : ∀ᶠ y in nhds t, g y = g t := by
    filter_upwards [hmax, hmin] with y h1 h2
    exact le_antisymm h1 h2
  obtain ⟨ε, hεpos, hball⟩ := Metric.eventually_nhds_iff.mp hconst
  have hder0 : deriv g =ᶠ[nhds t] fun _ => (0 : ℝ) := by
    refine Metric.eventually_nhds_iff.mpr ?_
    refine ⟨ε, hεpos, fun y hy => ?_⟩
    have hyε : dist y t < ε := hy
    apply HasDerivAt.deriv
    refine (hasDerivAt_const y (g t)).congr_of_eventuallyEq ?_
    refine Metric.eventually_nhds_iff.mpr ?_
    refine ⟨ε - dist y t, sub_pos.mpr hyε, fun z hz => ?_⟩
    have : dist z t < ε :=
      lt_of_le_of_lt (dist_triangle z y t) (by linarith [hz, hyε, dist_comm y t])
    exact hball this
  have : deriv (deriv g) t = 0 := by
    have h := Filter.EventuallyEq.deriv_eq (f₁ := deriv g) (f := fun _ => (0 : ℝ)) hder0
    simpa using h
  linarith

/-- At a local maximum of a "C²" scalar, the Laplacian is nonpositive. -/
theorem scalarLaplacian_nonpos_of_isLocalMax {phi : T3 → ℝ} {x : T3}
    (hφ : ContDiffAt ℝ 2 phi x)
    (hmax : IsLocalMax phi x) :
    scalarLaplacian phi x ≤ 0 := by
  have hC1 : ContDiffAt ℝ 1 phi x :=
    hφ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hnearφ : ∀ᶠ y in nhds x, DifferentiableAt ℝ phi y := by
    filter_upwards [hC1.eventually (by simp)] with y hy
    exact hy.differentiableAt_one
  have hfd : DifferentiableAt ℝ (fderiv ℝ phi) x :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hterm (i : Fin 3) :
      (fderiv ℝ (fun y => (fderiv ℝ phi y) (e i)) x) (e i) ≤ 0 := by
    let g : ℝ → ℝ := fun t => phi (x + t • e i)
    have hgmax : IsLocalMax g 0 := by
      have hpath : ContinuousAt (fun t : ℝ => x + t • e i) 0 := by fun_prop
      have h0 : (fun t : ℝ => x + t • e i) 0 = x := by simp
      have hmax' : IsLocalMax phi ((fun t : ℝ => x + t • e i) 0) := by
        simpa [h0] using hmax
      simpa [g, Function.comp] using hmax'.comp_continuous (g := fun t : ℝ => x + t • e i) hpath
    have hnear : ∀ᶠ s in nhds (0 : ℝ), DifferentiableAt ℝ phi (x + s • e i) := by
      have hpathc : ContinuousAt (fun s : ℝ => x + s • e i) 0 := by fun_prop
      have h0 : (fun s : ℝ => x + s • e i) 0 = x := by simp
      have htend : Tendsto (fun s : ℝ => x + s • e i) (nhds (0 : ℝ)) (nhds x) := by
        have : Tendsto (fun s : ℝ => x + s • e i) (nhds (0 : ℝ))
            (nhds ((fun s : ℝ => x + s • e i) 0)) := hpathc
        simpa [h0] using this
      exact htend.eventually hnearφ
    have hgeq : deriv g =ᶠ[nhds (0 : ℝ)] fun s => (fderiv ℝ phi (x + s • e i)) (e i) := by
      filter_upwards [hnear] with s hs
      exact deriv_line_slice phi x (e i) s hs
    have hg0 : DifferentiableAt ℝ g 0 :=
      (hasDerivAt_line_slice phi x (e i) 0 (by simpa using hC1.differentiableAt_one)).differentiableAt
    have hψ : DifferentiableAt ℝ (fun y => (fderiv ℝ phi y) (e i)) x :=
      ((ContinuousLinearMap.apply ℝ ℝ (e i)).differentiableAt).comp x hfd
    have hψ0 : DifferentiableAt ℝ (fun y => (fderiv ℝ phi y) (e i)) (x + (0 : ℝ) • e i) := by
      simpa using hψ
    have hcomp : DifferentiableAt ℝ (fun s : ℝ => (fderiv ℝ phi (x + s • e i)) (e i)) 0 := by
      have haff : DifferentiableAt ℝ (fun s : ℝ => x + s • e i) 0 := by fun_prop
      exact hψ0.comp 0 haff
    have hg' : DifferentiableAt ℝ (deriv g) 0 := hcomp.congr_of_eventuallyEq hgeq
    have hdd := deriv_deriv_nonpos_of_isLocalMax hg0 hg' hgmax
    have hident : deriv (deriv g) 0 =
        (fderiv ℝ (fun y => (fderiv ℝ phi y) (e i)) x) (e i) := by
      have := hgeq.deriv_eq
      have hψ0' : DifferentiableAt ℝ (fun y => (fderiv ℝ phi y) (e i)) (x + (0 : ℝ) • e i) := by
        simpa using hψ
      have hline := deriv_line_slice (fun y => (fderiv ℝ phi y) (e i)) x (e i) 0 hψ0'
      simpa [hline] using this
    exact hident ▸ hdd
  unfold scalarLaplacian
  exact Finset.sum_nonpos fun i _ => hterm i

/-- At a spatial local maximum of "|omega|", "⟨omega, Δω⟩ ≤ −|∇omega|_{HS}² ≤ 0". -/
theorem viscPair_le_neg_hsSq_at_local_max (omega : VelocityField) (x : T3)
    (hC2 : ContDiffAt ℝ 2 omega x)
    (hmax : IsLocalMax (fun y => ‖omega y‖) x) :
    viscPair omega x ≤ -hsSq omega x := by
  have hφ : ContDiffAt ℝ 2 (halfNormSq omega) x := by
    have hsq : ContDiffAt ℝ 2 (fun y => inner ℝ (omega y) (omega y)) x :=
      hC2.inner (𝕜 := ℝ) hC2
    have hc : ContDiffAt ℝ 2 (fun _ : T3 => (1 / 2 : ℝ)) x := contDiffAt_const
    have hmul := hc.mul hsq
    convert hmul using 1
    ext y
    simp [halfNormSq]
  have hlap := scalarLaplacian_nonpos_of_isLocalMax hφ
    (isLocalMax_halfNormSq_of_isLocalMax_norm hmax)
  have hboch := bochner_identity omega x hC2
  linarith [hlap]

theorem viscPair_nonpos_at_local_max (omega : VelocityField) (x : T3)
    (hC2 : ContDiffAt ℝ 2 omega x)
    (hmax : IsLocalMax (fun y => ‖omega y‖) x) :
    viscPair omega x ≤ 0 :=
  le_trans (viscPair_le_neg_hsSq_at_local_max omega x hC2 hmax) (neg_nonpos.mpr (hsSq_nonneg omega x))

/-! ## 3. Time derivative of `|omega|` along a path (proved) -/

theorem hasDerivAt_halfNormSq_time (w : ℝ → EuclideanSpace ℝ (Fin 3)) (t : ℝ)
    (hw : DifferentiableAt ℝ w t) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * ‖w s‖ ^ 2) (inner ℝ (w t) (deriv w t)) t := by
  have hsq : HasDerivAt (fun s => ‖w s‖ ^ 2) (2 * inner ℝ (w t) (deriv w t)) t :=
    hw.hasDerivAt.norm_sq
  have hhalf := hsq.const_mul (1 / 2 : ℝ)
  convert hhalf using 1
  ring

/-- If "w(t) ≠ 0", then "d/dt ‖w‖ = ⟨w, w'⟩ / ‖w‖". -/
theorem hasDerivAt_norm_of_ne_zero (w : ℝ → EuclideanSpace ℝ (Fin 3)) (t : ℝ)
    (hw : DifferentiableAt ℝ w t) (hpos : w t ≠ 0) :
    HasDerivAt (fun s => ‖w s‖) (inner ℝ (w t) (deriv w t) / ‖w t‖) t := by
  have hsq : HasDerivAt (fun s => ‖w s‖ ^ 2) (2 * inner ℝ (w t) (deriv w t)) t :=
    hw.hasDerivAt.norm_sq
  have hnormpos : 0 < ‖w t‖ := norm_pos_iff.mpr hpos
  have hvalpos : 0 < ‖w t‖ ^ 2 := sq_pos_of_pos hnormpos
  have hsqrt : HasDerivAt Real.sqrt ((1 : ℝ) / (2 * Real.sqrt (‖w t‖ ^ 2))) (‖w t‖ ^ 2) :=
    Real.hasDerivAt_sqrt hvalpos.ne'
  have hcomp := hsqrt.comp t hsq
  have hfun : (fun s => ‖w s‖) = Real.sqrt ∘ fun s => ‖w s‖ ^ 2 := by
    funext s; exact (Real.sqrt_sq (norm_nonneg _)).symm
  have hident :
      (1 / (2 * Real.sqrt (‖w t‖ ^ 2))) * (2 * inner ℝ (w t) (deriv w t)) =
        inner ℝ (w t) (deriv w t) / ‖w t‖ := by
    have : Real.sqrt (‖w t‖ ^ 2) = ‖w t‖ := Real.sqrt_sq (norm_nonneg _)
    rw [this]
    field
  rw [hfun]
  convert hcomp using 1
  exact hident.symm

/-- Envelope theorem along a differentiable maximizing trajectory: if
"M(s) = |omega(s, x(s))|", the spatial gradient of "½|omega|²" vanishes at "x(t)", and the
path derivative splits into "∂t omega + (x'·∇)omega", then
"M'(t) = ⟨omega, ∂t omega⟩ / M(t)". -/
theorem envelope_along_differentiable_maximizer
    (omega : ℝ → VelocityField) (x : ℝ → T3) (M : ℝ → ℝ) (t : ℝ)
    (hM : M = fun s => ‖omega s (x s)‖)
    (hw : DifferentiableAt ℝ (fun s => omega s (x s)) t)
    (hpos : 0 < M t)
    (hgrad : fderiv ℝ (halfNormSq (omega t)) (x t) = 0)
    (hsplit : deriv (fun s => omega s (x s)) t =
      deriv (fun s => omega s (x t)) t + (fderiv ℝ (omega t) (x t)) (deriv x t))
    (hspace : DifferentiableAt ℝ (omega t) (x t)) :
    HasDerivAt M
      (inner ℝ (omega t (x t)) (deriv (fun s => omega s (x t)) t) / M t) t := by
  have hwne : omega t (x t) ≠ 0 := by
    have : ‖omega t (x t)‖ = M t := by rw [hM]
    exact norm_pos_iff.mp (this ▸ hpos)
  have hpath := hasDerivAt_norm_of_ne_zero (fun s => omega s (x s)) t hw hwne
  have hsp :
      inner ℝ (omega t (x t)) (deriv (fun s => omega s (x s)) t) =
        inner ℝ (omega t (x t)) (deriv (fun s => omega s (x t)) t) := by
    have hterm :
        inner ℝ (omega t (x t)) ((fderiv ℝ (omega t) (x t)) (deriv x t)) =
          (fderiv ℝ (halfNormSq (omega t)) (x t)) (deriv x t) :=
      (fderiv_halfNormSq (omega t) (x t) (deriv x t) hspace).symm
    rw [hsplit, inner_add_right, hterm, hgrad]
    simp
  have hMt : M t = ‖omega t (x t)‖ := by rw [hM]
  have hpath' : HasDerivAt (fun s => ‖omega s (x s)‖)
      (inner ℝ (omega t (x t)) (deriv (fun s => omega s (x t)) t) / ‖omega t (x t)‖) t := by
    convert hpath using 1
    rw [hsp]
  simpa [hM, hMt] using hpath'

/-- Difference-quotient form of Danskin's inequality: a maximizer at time "t+h"
gives an upper bound in terms of the increment of "|omega|" at that (moving) point.
The opposite comparison, using a maximizer only at time "t", goes the wrong way. -/
theorem danskin_difference_quotient
    (omega : ℝ → VelocityField) (M : ℝ → ℝ) (t h : ℝ) (xh : T3)
    (hh : 0 < h)
    (hmax_h : ‖omega (t + h) xh‖ = M (t + h))
    (hbelow : ‖omega t xh‖ ≤ M t) :
    (M (t + h) - M t) / h ≤ (‖omega (t + h) xh‖ - ‖omega t xh‖) / h := by
  have : M (t + h) - M t ≤ ‖omega (t + h) xh‖ - ‖omega t xh‖ := by
    linarith
  exact (div_le_div_iff_of_pos_right hh).mpr this

/-! ## 4. Stretching bound by the strain (proved, linear algebra) -/

theorem stretching_le_strain_mul_norm_sq (w v : VelocityField) (x : T3)
    (hv : DifferentiableAt ℝ v x)
    (hbdd : BddAbove (Set.range fun y => ‖fderiv ℝ v y‖)) :
    stretching v w x ≤ strain_sup_norm v * ‖w x‖ ^ 2 :=
  inner_convective_le_strain w v x hv hbdd

/-! ## 5. Algebraic reduction to the cubic rate (proved) -/

/-- If "M>0", "M' ≤ (stretching + ν visc) / M", stretching is at most "C M³", and
viscous dissipation is at most "−κ M⁴", then "M' ≤ C M² − κ M³". -/
theorem cubic_rate_of_stretching_and_visc
    (M M' stretch visc ν C kap : ℝ)
    (hM : 0 < M) (_hν : 0 ≤ ν)
    (hident : M' ≤ (stretch + ν * visc) / M)
    (hstretch : stretch ≤ C * M ^ 3)
    (hvisc : ν * visc ≤ -kap * M ^ 4) :
    M' ≤ C * M ^ 2 - kap * M ^ 3 := by
  have hsum : stretch + ν * visc ≤ C * M ^ 3 - kap * M ^ 4 := by linarith
  have hdiv : (stretch + ν * visc) / M ≤ (C * M ^ 3 - kap * M ^ 4) / M :=
    div_le_div_of_nonneg_right hsum hM.le
  have hring : (C * M ^ 3 - kap * M ^ 4) / M = C * M ^ 2 - kap * M ^ 3 := by
    have : M ≠ 0 := hM.ne'
    field
  linarith

/-- The same reduction with the Bochner sign "visc ≤ − hs" already built in:
"ν visc ≤ −ν hsSq", and the coercivity "hsSq ≥ kap M⁴" produces the cubic sink. -/
theorem cubic_rate_of_strain_and_hsSq
    (M M' stretch visc ν C kap hs : ℝ)
    (hM : 0 < M) (hν : 0 ≤ ν)
    (hident : M' ≤ (stretch + ν * visc) / M)
    (hstretch : stretch ≤ C * M ^ 3)
    (hvisc_le : visc ≤ -hs)
    (hcoer : kap * M ^ 4 ≤ hs) :
    M' ≤ C * M ^ 2 - ν * kap * M ^ 3 := by
  have hvisc : ν * visc ≤ -(ν * kap) * M ^ 4 := by
    have h1 : ν * visc ≤ ν * (-hs) := mul_le_mul_of_nonneg_left hvisc_le hν
    have h2 : ν * hs ≥ ν * (kap * M ^ 4) := mul_le_mul_of_nonneg_left hcoer hν
    linarith
  exact cubic_rate_of_stretching_and_visc M M' stretch visc ν C (ν * kap)
    hM hν hident hstretch hvisc

/-! ## 6. Interior Fefferman regularity and two-sided time derivatives (proved) -/

theorem Ico_mem_nhds_of_mem_Ioo {T t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    Set.Ico (0 : ℝ) T ∈ nhds t :=
  Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Ico_self

theorem fefferman_u_contDiffAt_interior
    {ν T : ℝ} {u₀ : VelocityField} {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hu : IsFeffermanSolutionOn ν T u₀ u p)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3) :
    ContDiffAt ℝ ∞ (fun q : T3 × ℝ => u q.2 q.1) (x, t) :=
  hu.1.contDiffAt (prod_mem_nhds (by simp) (Ico_mem_nhds_of_mem_Ioo ht))

theorem fefferman_p_contDiffAt_interior
    {ν T : ℝ} {u₀ : VelocityField} {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hu : IsFeffermanSolutionOn ν T u₀ u p)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3) :
    ContDiffAt ℝ ∞ (fun q : T3 × ℝ => p q.2 q.1) (x, t) :=
  hu.2.1.contDiffAt (prod_mem_nhds (by simp) (Ico_mem_nhds_of_mem_Ioo ht))

theorem derivWithin_Ici_eq_deriv_of_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {t : ℝ} (ht : 0 < t) :
    derivWithin f (Set.Ici (0 : ℝ)) t = deriv f t :=
  derivWithin_of_mem_nhds (Ici_mem_nhds ht)

/-- On "(0, T)", the Fefferman one-sided momentum equation is the two-sided equation. -/
theorem fefferman_two_sided_eq_interior
    {ν T : ℝ} {u₀ : VelocityField} {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hu : IsFeffermanSolutionOn ν T u₀ u p)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3) :
    time_deriv u t x + convective (u t) (u t) x + pressureGradient (p t) x =
        ν • laplacian (u t) x ∧
      div (u t) x = 0 := by
  have heq := hu.2.2.1 t ⟨ht.1.le, ht.2⟩ x
  have hdt : derivWithin (fun s => u s x) (Set.Ici (0 : ℝ)) t = time_deriv u t x :=
    derivWithin_Ici_eq_deriv_of_pos (fun s => u s x) ht.1
  simpa [hdt] using heq

/-! ## 7. Named missing inequalities (unsettled as general statements) -/

/-- Existence of a global spatial maximizer of "|omega(t)|" on "ℝ³", for every time in "[0, T)".
Not implied by "IsFeffermanSolutionOn" as written (smoothness plus an energy inequality
does not give decay or attainment of the supremum). UNSETTLED. -/
def VorticityMaximumAttained (u : TimeDependentVelocity) (T : ℝ) (x_max : ℝ → T3) : Prop :=
  ∀ t ∈ Set.Ico (0 : ℝ) T,
    IsMaxOn (fun y => ‖vorticity (u t) y‖) Set.univ (x_max t)

/-- A differentiable-in-time maximizing trajectory on the open interval "(0, T)".
Used by the envelope theorem. UNSETTLED (existence). -/
def DifferentiableMaximizer (x_max : ℝ → T3) (T : ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) T, DifferentiableAt ℝ x_max t

/-- Uniform-in-time Calderón–Zygmund / Biot–Savart control of strain by vorticity,
with a constant depending only on the local solution (hence, in the rate, only on
"u₀, ν"). UNSETTLED along Fefferman solutions. A *universal* pointwise bound
"‖Du(x)‖ ≤ C ‖omega‖_∞" for arbitrary (not necessarily decaying, not necessarily
Biot–Savart) fields is kernel-checked disproved by
"StrainBoundRefutation.not_forall_strain_le_sup_vorticity". That counterexample is
irrotational and does not decay, so it does not by itself disprove the bound on
Fefferman-class snapshots. -/
def StrainControlledByVorticity (u : TimeDependentVelocity) (T C : ℝ) : Prop :=
  0 < C ∧
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      BddAbove (Set.range fun y => ‖fderiv ℝ (u t) y‖) ∧
      strain_sup_norm (u t) ≤ C * Mω u t

/-- Coercivity of direction curvature (or equivalently of "|∇omega|_{HS}") at an attained
spatial maximum: "hsSq(omega(t), x_max(t)) ≥ κ M(t)⁴", with "κ > 0" independent of "t".
This is the source of the cubic sink "−κ M³" after dividing by "M". UNSETTLED along
Navier–Stokes trajectories. For *arbitrary* divergence-free snapshots the same
lower bound is kernel-checked disproved in "Scratch/TetherRateStaticTests.lean". -/
def DirectionCoercivityAtMax (u : TimeDependentVelocity) (T kap : ℝ) (x_max : ℝ → T3) : Prop :=
  0 < kap ∧
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      kap * Mω u t ^ 4 ≤ hsSq (vorticity (u t)) (x_max t)

/-- Danskin's limiting inequality at time "t": the right derivative of "M" is at most
the normalized pairing "⟨omega, ∂t omega⟩ / M" at a maximizer. Proved along a differentiable
maximizing path by "envelope_along_differentiable_maximizer"; taken as a hypothesis
when only existence of maximizers (no path regularity) is assumed. -/
def DanskinRateAt (u : TimeDependentVelocity) (t : ℝ) (x : T3) (d : ℝ) : Prop :=
  0 < Mω u t →
    d ≤ inner ℝ (vorticity (u t) x)
      (time_deriv (fun s => vorticity (u s)) t x) / Mω u t

/-! ## 8. Navier–Stokes parabolic scaling of `M` (proved) -/

/-- Spacetime rescaling "u_λ(x,t) = λ u(λ x, λ² t)". -/
def rescaleFlow (lam : ℝ) (u : TimeDependentVelocity) : TimeDependentVelocity :=
  fun t x => lam • u (lam ^ 2 * t) (lam • x)

theorem rescaleFlow_eq_rescale (lam : ℝ) (u : TimeDependentVelocity) (t : ℝ) :
    rescaleFlow lam u t = rescale lam (u (lam ^ 2 * t)) :=
  rfl

/-- Pointwise: "ω_λ(x,t) = λ² omega(λ x, λ² t)", under componentwise differentiability. -/
theorem vorticity_rescaleFlow (lam : ℝ) (u : TimeDependentVelocity) (t : ℝ) (x : T3)
    (hd : ∀ i, DifferentiableAt ℝ (fun y => u (lam ^ 2 * t) y i) (lam • x)) :
    vorticity (rescaleFlow lam u t) x =
      lam ^ 2 • vorticity (u (lam ^ 2 * t)) (lam • x) := by
  simpa [rescaleFlow_eq_rescale] using vorticity_rescale lam (u (lam ^ 2 * t)) x hd

theorem norm_vorticity_rescaleFlow (lam : ℝ) (u : TimeDependentVelocity) (t : ℝ) (x : T3)
    (hd : ∀ i, DifferentiableAt ℝ (fun y => u (lam ^ 2 * t) y i) (lam • x)) :
    ‖vorticity (rescaleFlow lam u t) x‖ =
      |lam| ^ 2 * ‖vorticity (u (lam ^ 2 * t)) (lam • x)‖ := by
  rw [vorticity_rescaleFlow lam u t x hd, norm_smul, Real.norm_eq_abs, abs_pow, sq_abs]

/-- If "λ ≠ 0" and every snapshot "u(λ² t)" is componentwise differentiable, then
"M(u_λ, t) = λ² M(u, λ² t)" (absolute value: "M(u_λ,t) = |λ|² M(u,λ² t)"). -/
theorem Mω_rescaleFlow (lam : ℝ) (u : TimeDependentVelocity) (t : ℝ) (hlam : lam ≠ 0)
    (hd : ∀ z i, DifferentiableAt ℝ (fun y => u (lam ^ 2 * t) y i) z)
    (hbdd : BddAbove (Set.range fun z => ‖vorticity (u (lam ^ 2 * t)) z‖)) :
    Mω (rescaleFlow lam u) t = |lam| ^ 2 * Mω u (lam ^ 2 * t) := by
  have hinv_smul (z : T3) : lam • (lam⁻¹ • z) = z := by
    rw [smul_smul, mul_inv_cancel₀ hlam, one_smul]
  have hbddLam : BddAbove (Set.range fun x => ‖vorticity (rescaleFlow lam u t) x‖) := by
    refine ⟨|lam| ^ 2 * vorticity_sup_norm (vorticity (u (lam ^ 2 * t))), ?_⟩
    rintro _ ⟨x, rfl⟩
    have hx := norm_vorticity_rescaleFlow lam u t x (fun i => hd (lam • x) i)
    simp only [hx]
    exact mul_le_mul_of_nonneg_left (le_vorticity_sup_norm _ _ hbdd) (sq_nonneg _)
  apply le_antisymm
  · refine ciSup_le fun x => ?_
    have hx := norm_vorticity_rescaleFlow lam u t x (fun i => hd (lam • x) i)
    simp only [hx]
    exact mul_le_mul_of_nonneg_left (le_vorticity_sup_norm _ _ hbdd) (sq_nonneg _)
  · have hpt (z : T3) :
        |lam| ^ 2 * ‖vorticity (u (lam ^ 2 * t)) z‖ ≤
          vorticity_sup_norm (vorticity (rescaleFlow lam u t)) := by
      have hd' : ∀ i, DifferentiableAt ℝ (fun y => u (lam ^ 2 * t) y i)
          (lam • (lam⁻¹ • z)) := fun i => by
        simpa [hinv_smul z] using hd z i
      have hnorm := norm_vorticity_rescaleFlow lam u t (lam⁻¹ • z) hd'
      have := le_vorticity_sup_norm (vorticity (rescaleFlow lam u t)) (lam⁻¹ • z) hbddLam
      simpa [hnorm, hinv_smul z] using this
    have hlam2 : 0 < |lam| ^ 2 := sq_pos_of_ne_zero (abs_ne_zero.mpr hlam)
    have hle : Mω u (lam ^ 2 * t) ≤ (|lam| ^ 2)⁻¹ * Mω (rescaleFlow lam u) t :=
      ciSup_le fun z => (le_inv_mul_iff₀ hlam2).2 (hpt z)
    have := mul_le_mul_of_nonneg_left hle hlam2.le
    have hcancel : |lam| ^ 2 * ((|lam| ^ 2)⁻¹ * Mω (rescaleFlow lam u) t) =
        Mω (rescaleFlow lam u) t := by
      field
    linarith [hcancel]

theorem hasDerivAt_Mω_rescale_of_hasDerivAt
    (M : ℝ → ℝ) (lam t d : ℝ) (_hlam : 0 < lam)
    (hM : HasDerivAt M d (lam ^ 2 * t)) :
    HasDerivAt (fun s => lam ^ 2 * M (lam ^ 2 * s)) (lam ^ 4 * d) t := by
  have hscale : HasDerivAt (fun s : ℝ => lam ^ 2 * s) (lam ^ 2) t := by
    simpa using (hasDerivAt_id t).const_mul (lam ^ 2)
  have hcomp := hM.comp t hscale
  have hmul := hcomp.const_mul (lam ^ 2)
  convert hmul using 1
  ring

/-- Homogeneity of the proposed rate. For "λ > 0",
"d/dt M_λ(t) ≤ C M_λ(t)² − κ M_λ(t)³" holds at time "t" with the *same* "(C,κ)"
if and only if "M'(s) ≤ C M(s)² − κ λ² M(s)³" at "s = λ² t".
The cubic sink is therefore one degree supercritical for Navier–Stokes scaling:
any "(C,κ)" that is independent of the concentration parameter "λ" cannot be
preserved under rescaling of a single profile. This does not disprove
"FrohmanianTetherRateSmooth", whose constants are allowed to depend on "u₀". -/
theorem rate_form_rescale_iff
    (M : ℝ → ℝ) (lam t d C kap : ℝ) (hlam : 0 < lam)
    (_hM : HasDerivAt M d (lam ^ 2 * t)) :
    let s := lam ^ 2 * t
    let Mlam := fun τ => lam ^ 2 * M (lam ^ 2 * τ)
    (lam ^ 4 * d ≤ C * (Mlam t) ^ 2 - kap * (Mlam t) ^ 3) ↔
      (d ≤ C * (M s) ^ 2 - kap * lam ^ 2 * (M s) ^ 3) := by
  intro s Mlam
  have hMlam : Mlam t = lam ^ 2 * M s := rfl
  constructor
  · intro h
    have : lam ^ 4 * d ≤ C * (lam ^ 2 * M s) ^ 2 - kap * (lam ^ 2 * M s) ^ 3 := by
      simpa [hMlam] using h
    have hlampos : 0 < lam ^ 4 := pow_pos hlam 4
    -- divide the identity by λ⁴
    have hring :
        C * (lam ^ 2 * M s) ^ 2 - kap * (lam ^ 2 * M s) ^ 3 =
          lam ^ 4 * (C * (M s) ^ 2 - kap * lam ^ 2 * (M s) ^ 3) := by
      ring
    rw [hring] at this
    exact (mul_le_mul_iff_of_pos_left hlampos).mp this
  · intro h
    have hring :
        C * (Mlam t) ^ 2 - kap * (Mlam t) ^ 3 =
          lam ^ 4 * (C * (M s) ^ 2 - kap * lam ^ 2 * (M s) ^ 3) := by
      simp [hMlam]; ring
    have := mul_le_mul_of_nonneg_left h (pow_nonneg hlam.le 4)
    linarith [hring]

/-! ## 9. What this file does not prove -/

/-- The repaired rate, copied here only as a documentation hook. Its statement is
exactly "RepairedTether.FrohmanianTetherRateSmooth" and is not changed. UNSETTLED
for general Fefferman data. The zero datum is proved:
"RepairedTether.frohmanianTetherRateSmooth_zero". -/
def RateStatement (u₀ : VelocityField) (ν : ℝ) : Prop :=
  FrohmanianTetherRateSmooth u₀ ν

/- The chain that *would* close the rate, recorded as hypotheses. This theorem does
not claim those hypotheses, and it does not prove `FrohmanianTetherRateSmooth`. -/

theorem cubic_rate_from_named_hypotheses
    (M M' stretch visc ν C kap hs : ℝ)
    (hM : 0 < M) (hν : 0 ≤ ν)
    (hident : M' ≤ (stretch + ν * visc) / M)
    (hstrain : stretch ≤ C * M ^ 3)
    (hvisc_le : visc ≤ -hs)
    (hcoer : kap * M ^ 4 ≤ hs) :
    M' ≤ C * M ^ 2 - ν * kap * M ^ 3 :=
  cubic_rate_of_strain_and_hsSq M M' stretch visc ν C kap hs hM hν hident hstrain hvisc_le hcoer

end TetherRateDerivation

#print axioms TetherRateDerivation.bochner_identity
#print axioms TetherRateDerivation.transport_vanishes_at_local_max
#print axioms TetherRateDerivation.viscPair_le_neg_hsSq_at_local_max
#print axioms TetherRateDerivation.scalarLaplacian_nonpos_of_isLocalMax
#print axioms TetherRateDerivation.envelope_along_differentiable_maximizer
#print axioms TetherRateDerivation.danskin_difference_quotient
#print axioms TetherRateDerivation.stretching_le_strain_mul_norm_sq
#print axioms TetherRateDerivation.cubic_rate_of_stretching_and_visc
#print axioms TetherRateDerivation.cubic_rate_of_strain_and_hsSq
#print axioms TetherRateDerivation.fefferman_two_sided_eq_interior
#print axioms TetherRateDerivation.vorticity_rescaleFlow
#print axioms TetherRateDerivation.Mω_rescaleFlow
#print axioms TetherRateDerivation.hasDerivAt_Mω_rescale_of_hasDerivAt
#print axioms TetherRateDerivation.rate_form_rescale_iff
#print axioms TetherRateDerivation.hasDerivAt_norm_of_ne_zero
