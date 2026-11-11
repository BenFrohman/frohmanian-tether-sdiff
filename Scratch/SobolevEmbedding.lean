import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Elementary Sobolev embedding on ℝ³ (unit-cube averaging)

For `h : ℝ³ → ℝ` smooth, `|h x| ≤ ∑_{b ∈ {0,1}³} ‖D₂^{b₂} D₁^{b₁} D₀^{b₀} h‖_{L²(ℝ³)}`.
No decay or compact support is assumed. -/

open MeasureTheory Set
open scoped ContDiff ENNReal

noncomputable section
namespace SobolevR3

abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Coordinate unit vector. -/
abbrev e (i : Fin 3) : E3 := EuclideanSpace.single i (1 : ℝ)

/-- Directional derivative along `e i`. -/
def D (i : Fin 3) (g : E3 → ℝ) : E3 → ℝ := fun y => fderiv ℝ g y (e i)

lemma contDiff_D {g : E3 → ℝ} (hg : ContDiff ℝ ∞ g) (i : Fin 3) : ContDiff ℝ ∞ (D i g) :=
  (hg.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

/-- One-dimensional averaging: `|γ 0| ≤ ∫₀¹ |γ| + ∫₀¹ |γ'|`. -/
lemma abs_le_avg_1d {γ : ℝ → ℝ} (hγ : ContDiff ℝ 1 γ) :
    ENNReal.ofReal |γ 0| ≤ (∫⁻ s in Ioc (0 : ℝ) 1, ‖γ s‖ₑ) + ∫⁻ s in Ioc (0 : ℝ) 1, ‖deriv γ s‖ₑ := by
  have hd : ∀ t, HasDerivAt γ (deriv γ t) t := fun t =>
    (hγ.differentiable one_ne_zero t).hasDerivAt
  have hcd : Continuous (deriv γ) := hγ.continuous_deriv_one
  set c : ℝ := ∫ s in (0 : ℝ)..1, |deriv γ s|
  have hpt : ∀ t ∈ Ioc (0 : ℝ) 1, |γ 0| ≤ |γ t| + c := by
    intro t ht
    have hftc : ∫ s in (0 : ℝ)..t, deriv γ s = γ t - γ 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
        (hcd.intervalIntegrable _ _)
    have h1 : |∫ s in (0 : ℝ)..t, deriv γ s| ≤ ∫ s in (0 : ℝ)..t, |deriv γ s| :=
      intervalIntegral.abs_integral_le_integral_abs ht.1.le
    have h2 : ∫ s in (0 : ℝ)..t, |deriv γ s| ≤ c :=
      intervalIntegral.integral_mono_interval le_rfl ht.1.le ht.2
        (Filter.Eventually.of_forall fun _ => abs_nonneg _) (hcd.abs.intervalIntegrable _ _)
    have : γ 0 = γ t - ∫ s in (0 : ℝ)..t, deriv γ s := by rw [hftc]; ring
    rw [this]
    calc |γ t - ∫ s in (0 : ℝ)..t, deriv γ s| ≤ |γ t| + |∫ s in (0 : ℝ)..t, deriv γ s| :=
          abs_sub _ _
      _ ≤ |γ t| + c := by linarith
  have hc : ENNReal.ofReal c = ∫⁻ s in Ioc (0 : ℝ) 1, ‖deriv γ s‖ₑ := by
    simp only [c, intervalIntegral.integral_of_le zero_le_one]
    rw [← ofReal_integral_norm_eq_lintegral_enorm]
    · simp [Real.norm_eq_abs]
    · exact (hcd.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hvol : volume (Ioc (0 : ℝ) 1) = 1 := by simp
  calc ENNReal.ofReal |γ 0| = ∫⁻ _ in Ioc (0 : ℝ) 1, ENNReal.ofReal |γ 0| := by
        rw [setLIntegral_const, hvol, mul_one]
    _ ≤ ∫⁻ s in Ioc (0 : ℝ) 1, (‖γ s‖ₑ + ENNReal.ofReal c) := by
        refine setLIntegral_mono ((hγ.continuous.measurable.enorm).add measurable_const) fun t ht => ?_
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, ← ENNReal.ofReal_add (abs_nonneg _)
          (intervalIntegral.integral_nonneg zero_le_one fun _ _ => abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (hpt t ht)
    _ = _ := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const, hvol, mul_one, hc]

/-- `A i F y = ∫₀¹ F (y + s eᵢ) ds`. -/
def A (i : Fin 3) (F : E3 → ℝ≥0∞) : E3 → ℝ≥0∞ :=
  fun y => ∫⁻ s in Ioc (0 : ℝ) 1, F (y + s • e i)

/-- `N g = |g|` as an extended nonnegative function. -/
def N (g : E3 → ℝ) : E3 → ℝ≥0∞ := fun z => ‖g z‖ₑ

lemma measurable_A {i : Fin 3} {F : E3 → ℝ≥0∞} (hF : Measurable F) : Measurable (A i F) := by
  have : Measurable fun q : E3 × ℝ => F (q.1 + q.2 • e i) :=
    hF.comp (measurable_fst.add (measurable_snd.smul_const _))
  exact this.lintegral_prod_right'

lemma measurable_N {g : E3 → ℝ} (hg : Continuous g) : Measurable (N g) :=
  hg.measurable.enorm

lemma A_le_add {i : Fin 3} {F G₁ G₂ : E3 → ℝ≥0∞} (hG₁ : Measurable G₁)
    (h : ∀ z, F z ≤ G₁ z + G₂ z) (y : E3) : A i F y ≤ A i G₁ y + A i G₂ y := by
  unfold A
  calc ∫⁻ s in Ioc (0 : ℝ) 1, F (y + s • e i)
      ≤ ∫⁻ s in Ioc (0 : ℝ) 1, (G₁ (y + s • e i) + G₂ (y + s • e i)) :=
        lintegral_mono fun s => h _
    _ = _ := lintegral_add_left (hG₁.comp (measurable_const.add (measurable_id.smul_const _))) _

/-- Averaging along the line `y + s eᵢ`. -/
lemma N_le_line {g : E3 → ℝ} (hg : ContDiff ℝ ∞ g) (i : Fin 3) (y : E3) :
    N g y ≤ A i (N g) y + A i (N (D i g)) y := by
  set γ : ℝ → ℝ := fun s => g (y + s • e i)
  have hγ : ContDiff ℝ 1 γ :=
    (hg.of_le (by norm_cast)).comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hder : ∀ s, deriv γ s = D i g (y + s • e i) := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => y + s • e i) (e i) s := by
      simpa using (HasDerivAt.smul_const (hasDerivAt_id s) (e i)).const_add y
    have h2 := ((hg.differentiable (by simp)) (y + s • e i)).hasFDerivAt.comp_hasDerivAt s h1
    exact h2.deriv
  have := abs_le_avg_1d hγ
  simp only [γ, zero_smul, add_zero, hder] at this
  simpa [N, A, ← ofReal_norm_eq_enorm, Real.norm_eq_abs] using this

/-- Two directions. -/
lemma N_le_12 {g : E3 → ℝ} (hg : ContDiff ℝ ∞ g) (y : E3) :
    N g y ≤ A 1 (A 2 (N g)) y + A 1 (A 2 (N (D 2 g))) y +
      (A 1 (A 2 (N (D 1 g))) y + A 1 (A 2 (N (D 2 (D 1 g)))) y) := by
  have h1g := contDiff_D hg 1
  refine (N_le_line hg 1 y).trans (add_le_add ?_ ?_)
  · exact A_le_add (measurable_A (measurable_N hg.continuous)) (N_le_line hg 2) y
  · exact A_le_add (measurable_A (measurable_N h1g.continuous)) (N_le_line h1g 2) y

/-- `T F x = ∫_{[0,1]³} F(x + s₀e₀ + s₁e₁ + s₂e₂)`. -/
def T (F : E3 → ℝ≥0∞) : E3 → ℝ≥0∞ := A 0 (A 1 (A 2 F))

/-- Three directions: eight mixed-derivative terms. -/
lemma N_le_T {h : E3 → ℝ} (hh : ContDiff ℝ ∞ h) (x : E3) :
    N h x ≤ (T (N h) x + T (N (D 2 h)) x + (T (N (D 1 h)) x + T (N (D 2 (D 1 h))) x)) +
      (T (N (D 0 h)) x + T (N (D 2 (D 0 h))) x +
        (T (N (D 1 (D 0 h))) x + T (N (D 2 (D 1 (D 0 h)))) x)) := by
  have h0 := contDiff_D hh 0
  have hm : ∀ {g : E3 → ℝ}, ContDiff ℝ ∞ g →
      Measurable (fun z => A 1 (A 2 (N g)) z + A 1 (A 2 (N (D 2 g))) z) := fun hg =>
    (measurable_A (measurable_A (measurable_N hg.continuous))).add
      (measurable_A (measurable_A (measurable_N (contDiff_D hg 2).continuous)))
  have hm' : ∀ {g : E3 → ℝ}, ContDiff ℝ ∞ g → Measurable (A 1 (A 2 (N g))) := fun hg =>
    measurable_A (measurable_A (measurable_N hg.continuous))
  have key : ∀ {g : E3 → ℝ}, ContDiff ℝ ∞ g → ∀ y, A 0 (N g) y ≤
      T (N g) y + T (N (D 2 g)) y + (T (N (D 1 g)) y + T (N (D 2 (D 1 g))) y) := by
    intro g hg y
    have hg1 := contDiff_D hg 1
    refine (A_le_add (hm hg) (N_le_12 hg) y).trans (add_le_add ?_ ?_)
    · exact A_le_add (hm' hg) (fun z => le_rfl) y
    · exact A_le_add (hm' hg1) (fun z => le_rfl) y
  exact (N_le_line hh 0 x).trans (add_le_add (key hh x) (key h0 x))

/-! ### The unit cube in product coordinates -/

/-- `ψ (a, b, c) = a e₀ + b e₁ + c e₂`, as a composite of volume-preserving equivalences. -/
def ψ : ℝ × ℝ × ℝ → E3 := fun p =>
  WithLp.toLp 2 ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm
    (p.1, MeasurableEquiv.finTwoArrow.symm p.2))

lemma measurePreserving_ψ : MeasurePreserving ψ := by
  have h1 : MeasurePreserving (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.finTwoArrow (α := ℝ)).symm)
      (volume : Measure (ℝ × ℝ × ℝ)) (volume : Measure (ℝ × (Fin 2 → ℝ))) :=
    (MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ).symm
  have h2 := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm
  exact (PiLp.volume_preserving_toLp (Fin 3)).comp (h2.comp h1)

lemma ψ_apply (a b c : ℝ) : ψ (a, b, c) = a • e 0 + b • e 1 + c • e 2 := by
  ext i
  fin_cases i <;> (simp [ψ, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.finTwoArrow]; try rfl)

/-- The cube integral equals an integral over `[0,1]³` in product coordinates. -/
lemma T_eq {F : E3 → ℝ≥0∞} (hF : Measurable F) (x : E3) :
    T F x = ∫⁻ p in Ioc (0 : ℝ) 1 ×ˢ (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1), F (x + ψ p) := by
  have hFψ : Measurable fun p : ℝ × ℝ × ℝ => F (x + ψ p) :=
    hF.comp (measurable_const.add measurePreserving_ψ.measurable)
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.volume_eq_prod,
    ← Measure.prod_restrict, lintegral_prod _ hFψ.aemeasurable]
  unfold T A
  refine lintegral_congr fun a => ?_
  rw [lintegral_prod (fun q : ℝ × ℝ => F (x + ψ (a, q)))
    (hFψ.comp measurable_prodMk_left).aemeasurable]
  refine lintegral_congr fun b => lintegral_congr fun c => ?_
  simp only [ψ_apply, add_assoc]

/-- Cauchy–Schwarz on the unit cube and translation invariance:
`T F x ≤ (∫_{ℝ³} F²)^{1/2}`. -/
lemma T_le_L2 {F : E3 → ℝ≥0∞} (hF : Measurable F) (x : E3) :
    T F x ≤ (∫⁻ y, F y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  set C := Ioc (0 : ℝ) 1 ×ˢ (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1)
  set μ := (volume : Measure (ℝ × ℝ × ℝ)).restrict C
  have hFψ : Measurable fun p : ℝ × ℝ × ℝ => F (x + ψ p) :=
    hF.comp (measurable_const.add measurePreserving_ψ.measurable)
  have hμ : μ univ = 1 := by
    simp only [μ, Measure.restrict_apply_univ, C, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    hFψ.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, hμ] at hCS
  rw [T_eq hF x]
  refine hCS.trans ?_
  gcongr
  calc ∫⁻ p, F (x + ψ p) ^ (2 : ℝ) ∂μ ≤ ∫⁻ p, F (x + ψ p) ^ (2 : ℝ) :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ y, F y ^ (2 : ℝ) := by
        have hmp := (measurePreserving_add_left volume x).comp measurePreserving_ψ
        exact hmp.lintegral_comp (hF.pow_const _)

/-- **Elementary Sobolev embedding on ℝ³.** For smooth `h : ℝ³ → ℝ` (no decay assumed),
`|h x| ≤ ∑ over the eight mixed derivatives `D₂^{c} D₁^{b} D₀^{a} h` of their `L²(ℝ³)` norms. -/
theorem abs_le_sum_L2 {h : E3 → ℝ} (hh : ContDiff ℝ ∞ h) (x : E3) :
    ENNReal.ofReal |h x| ≤
      ((∫⁻ y, ‖h y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) + (∫⁻ y, ‖D 2 h y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) +
        ((∫⁻ y, ‖D 1 h y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) +
          (∫⁻ y, ‖D 2 (D 1 h) y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))) +
      ((∫⁻ y, ‖D 0 h y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) +
          (∫⁻ y, ‖D 2 (D 0 h) y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) +
        ((∫⁻ y, ‖D 1 (D 0 h) y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) +
          (∫⁻ y, ‖D 2 (D 1 (D 0 h)) y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))) := by
  have hN : ENNReal.ofReal |h x| = N h x := by simp [N, ← ofReal_norm_eq_enorm, Real.norm_eq_abs]
  have m := fun {g : E3 → ℝ} (hg : ContDiff ℝ ∞ g) => T_le_L2 (measurable_N hg.continuous) x
  have d0 := contDiff_D hh 0
  have d1 := contDiff_D hh 1
  have d10 := contDiff_D d0 1
  rw [hN]
  refine (N_le_T hh x).trans ?_
  gcongr
  · exact m hh
  · exact m (contDiff_D hh 2)
  · exact m d1
  · exact m (contDiff_D d1 2)
  · exact m d0
  · exact m (contDiff_D d0 2)
  · exact m d10
  · exact m (contDiff_D d10 2)

end SobolevR3

#print axioms SobolevR3.abs_le_avg_1d
#print axioms SobolevR3.abs_le_sum_L2
