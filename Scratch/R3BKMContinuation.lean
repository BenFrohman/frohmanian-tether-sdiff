import Scratch.RepairedTetherRate
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! # Toward `R3BKMContinuation` (classical continuation on ℝ³)

Decomposition of the classical hypothesis `RepairedTether.R3BKMContinuationAt` into
named analytic inputs, with every logical / ODE step between them kernel-checked.

* `KatoMaximalSolution ν u₀`: OPEN in Lean. Existence of a Fefferman-class solution
  on a time set `S` (`[0, ∞)` or `[0, T*)`) with finite, continuous, right-differentiable
  `H³` energy satisfying `d/dt ‖u‖²_{H³} ≤ C_k ‖∇u‖_∞ ‖u‖²_{H³}`, and the `H³`
  blow-up alternative if `T* < ∞`.
* `BKMLogInequality` (Beale–Kato–Majda 1984, log-Sobolev / Brezis–Gallouet type bound
  `‖∇f‖_∞ ≤ C (1 + ‖f‖₂² + ‖curl f‖_∞ (1 + log(1 + ‖f‖²_{H³})))`): proved in
  `LogBoundLocal.bkmLogInequality`. The Prop asserts that `∇f` is bounded, not
  that `curl f` is bounded.
* PROVED here: the BKM Gronwall argument (`hsSq_bounded_of_vorticity_bounded`),
  the blow-up exclusion (`katoBKMMaximal_of_kato_of_log`), the passage from a global
  Fefferman-class local family to Fefferman's global solution (`feffermanGlobalSolution_of_forall`),
  finiteness of the initial energy from Fefferman decay (`lintegral_sq_lt_top_of_feffermanDecay`),
  and the assembly `r3BKMContinuation_of_kato_of_log`.
-/

open MeasureTheory NavierStokes3D FrohmanianTether RepairedTether Set Filter Topology
open scoped ContDiff

noncomputable section
namespace R3BKM

/-! ## Concrete Sobolev quantities (Mathlib has no `H^s` on `ℝ³`) -/

/-- `‖f‖²_{H^m} := ∑_{k ≤ m} ∑_{α : Fin k → Fin 3} ∫ |∂_{α 0} ⋯ ∂_{α (k-1)} f(x)|² dx`
(Euclidean norm of each partial derivative; ordered tuples, so each multi-index is counted with
a positive integer multiplicity: an equivalent `H^m` norm, as in Majda–Bertozzi §3.2). -/
def sobolevEnergy (m : ℕ) (f : VelocityField) : ENNReal :=
  ∑ k ∈ Finset.range (m + 1), ∑ α : Fin k → Fin 3,
    ∫⁻ x, ‖iteratedFDeriv ℝ k f x (fun j => EuclideanSpace.single (α j) (1 : ℝ))‖ₑ ^ 2

/-- Real value of `‖f‖²_{H^m}` (meaningful when `sobolevEnergy m f < ⊤`). -/
def hsSq (m : ℕ) (f : VelocityField) : ℝ := (sobolevEnergy m f).toReal

/-- `‖f‖₂²` as a real number. -/
def l2Sq (f : VelocityField) : ℝ := (∫⁻ x, ‖f x‖ₑ ^ 2).toReal

/-- `‖∇f‖_∞` (real `iSup`; junk `0` if unbounded, so statements below also assert `BddAbove`). -/
def gradSup (f : VelocityField) : ℝ := ⨆ x, ‖fderiv ℝ f x‖

lemma hsSq_nonneg (m : ℕ) (f : VelocityField) : 0 ≤ hsSq m f := ENNReal.toReal_nonneg

lemma gradSup_nonneg (f : VelocityField) : 0 ≤ gradSup f :=
  Real.iSup_nonneg fun _ => norm_nonneg _

lemma mω_nonneg (u : TimeDependentVelocity) (t : ℝ) : 0 ≤ Mω u t :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/-! ## Named inputs (precisely stated sub-Props).
`BKMLogInequality` is proved in `LogBoundLocal`; `KatoMaximalSolution` is not proved here. -/

/-- **BKM logarithmic inequality** (Beale–Kato–Majda 1984, eq. (3.2)–(3.5); m = 3 > 5/2).
There is a constant `C > 0` such that for every smooth divergence-free `f` with
finite `H³` energy, `∇f` is bounded and
`‖∇f‖_∞ ≤ C (1 + ‖f‖₂² + ‖curl f‖_∞ (1 + log (1 + ‖f‖²_{H³})))`. -/
def BKMLogInequality : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f : VelocityField, ContDiff ℝ ∞ f → (∀ x, div f x = 0) →
    sobolevEnergy 3 f < ⊤ →
      BddAbove (range fun x => ‖fderiv ℝ f x‖) ∧
      gradSup f ≤ C * (1 + l2Sq f +
        vorticity_sup_norm (vorticity f) * (1 + Real.log (1 + hsSq 3 f)))

/-- **Kato maximal solution.** There exist a time set `S`, a pair `(u, p)`, and a
constant `C_k ≥ 0` such that: on every `[0, T) ⊆ S`, `(u, p)` is a Fefferman-class
solution from `u₀`; `‖u(t)‖²_{H³}` is finite at every `t ∈ S` and continuous on
`S`; at every `s ∈ S` the map `t ↦ ‖u(t)‖²_{H³}` has a right derivative
`d ≤ C_k ‖∇u(s)‖_∞ ‖u(s)‖²_{H³}`; and either `S = [0, ∞)` or `S = [0, T*)` for
some `T* > 0` with `‖u‖²_{H³}` unbounded on `S`. OPEN in Lean. -/
def KatoMaximalSolution (ν : ℝ) (u₀ : VelocityField) : Prop :=
  ∃ (S : Set ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure) (Ck : ℝ), 0 ≤ Ck ∧
    (∀ T : ℝ, Ico (0 : ℝ) T ⊆ S → IsFeffermanSolutionOn ν T u₀ u p) ∧
    (∀ t ∈ S, sobolevEnergy 3 (u t) < ⊤) ∧
    ContinuousOn (fun t => hsSq 3 (u t)) S ∧
    (∀ s ∈ S, ∃ d : ℝ, HasDerivWithinAt (fun t => hsSq 3 (u t)) d (Ici s) s ∧
      d ≤ Ck * gradSup (u s) * hsSq 3 (u s)) ∧
    (S = Ici 0 ∨ ∃ Tstar : ℝ, 0 < Tstar ∧ S = Ico 0 Tstar ∧
      ∀ B : ℝ, ∃ t ∈ S, B < hsSq 3 (u t))

/-- **Maximal solution with BKM vorticity blow-up alternative** (the BKM theorem in the form
used by Clay (A)): either the Fefferman-class solution is global, or it lives on `[0, T*)` and
no single ceiling bounds `‖ω‖_∞` there. Derived below from the two named inputs. -/
def KatoBKMMaximal (ν : ℝ) (u₀ : VelocityField) : Prop :=
  ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
    (∀ T : ℝ, IsFeffermanSolutionOn ν T u₀ u p) ∨
    ∃ Tstar : ℝ, 0 < Tstar ∧ IsFeffermanSolutionOn ν Tstar u₀ u p ∧
      ¬ ∃ Y : ℝ, ∀ t ∈ Ico (0 : ℝ) Tstar,
        BddAbove (range fun x => ‖vorticity (u t) x‖) ∧ Mω u t ≤ Y

/-! ## Proved: initial energy is finite under Fefferman decay -/

lemma lintegral_sq_lt_top_of_feffermanDecay {u₀ : VelocityField} (h : FeffermanDecay u₀) :
    ∫⁻ x, ‖u₀ x‖ₑ ^ 2 < ⊤ := by
  obtain ⟨C, hC⟩ := h 0 Fin.elim0 2
  have hint : Integrable (fun x : T3 => C ^ 2 * (1 + ‖x‖) ^ (-(4 : ℝ))) := by
    refine (integrable_one_add_norm ?_).const_mul _
    simp; norm_num
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hint.lintegral_lt_top
  have h1 := hC x
  rw [iteratedFDeriv_zero_apply] at h1
  have hw : 0 < 1 + ‖x‖ := by positivity
  have h2 : ‖u₀ x‖ ^ 2 ≤ C ^ 2 * (1 + ‖x‖) ^ (-(4 : ℝ)) := by
    have := pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc ‖u₀ x‖ ^ 2 ≤ (C * (1 + ‖x‖) ^ (-(2 : ℝ))) ^ 2 := this
      _ = C ^ 2 * (1 + ‖x‖) ^ (-(4 : ℝ)) := by
        rw [mul_pow, ← Real.rpow_natCast ((1 + ‖x‖) ^ (-(2 : ℝ))), ← Real.rpow_mul hw.le]
        norm_num
  calc ‖u₀ x‖ₑ ^ 2 = ENNReal.ofReal (‖u₀ x‖ ^ 2) := by
        rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal h2

/-! ## Proved: a family of Fefferman-class local solutions on every `[0,T)` is a global
Fefferman solution -/

lemma feffermanGlobalSolution_of_forall {ν : ℝ} {u₀ : VelocityField}
    {u : TimeDependentVelocity} {p : TimeDependentPressure} (hdec : FeffermanDecay u₀)
    (h : ∀ T : ℝ, IsFeffermanSolutionOn ν T u₀ u p) : FeffermanGlobalSolution ν u₀ u p := by
  have hloc : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : T3 × ℝ → F),
      (∀ T : ℝ, ContDiffOn ℝ ∞ g (univ ×ˢ Ico (0 : ℝ) T)) →
        ContDiffOn ℝ ∞ g (univ ×ˢ Ici (0 : ℝ)) := by
    intro F _ _ g hg q hq
    refine (hg (q.2 + 1) q ⟨trivial, hq.2, by linarith⟩).mono_of_mem_nhdsWithin ?_
    refine mem_nhdsWithin.2 ⟨univ ×ˢ Iio (q.2 + 1), isOpen_univ.prod isOpen_Iio,
      ⟨trivial, by simp⟩, ?_⟩
    rintro r ⟨⟨-, hr1⟩, -, hr2⟩
    exact ⟨trivial, hr2, hr1⟩
  have hE := lintegral_sq_lt_top_of_feffermanDecay hdec
  refine ⟨hloc _ fun T => (h T).1, hloc _ fun T => (h T).2.1, fun t ht x => ?_,
    (h 1).2.2.2.1, ⟨(∫⁻ x, ‖u₀ x‖ₑ ^ 2).toReal + 1, fun t ht => ?_⟩⟩
  · exact (h (t + 1)).2.2.1 t ⟨ht, by linarith⟩ x
  · refine lt_of_le_of_lt ((h (t + 1)).2.2.2.2 t ⟨ht, by linarith⟩) ?_
    exact (ENNReal.lt_ofReal_iff_toReal_lt hE.ne).2 (by linarith)

/-! ## Proved: the BKM maximal form gives `R3BKMContinuationAt` -/

theorem r3BKMContinuationAt_of_katoBKMMaximal {ν : ℝ} {u₀ : VelocityField}
    (hdec : FeffermanDecay u₀) (hK : KatoBKMMaximal ν u₀) : R3BKMContinuationAt ν u₀ := by
  rintro ⟨Y, hY⟩
  obtain ⟨u, p, hglob | ⟨Tstar, -, hsol, hblow⟩⟩ := hK
  · exact ⟨u, p, feffermanGlobalSolution_of_forall hdec hglob⟩
  · exact absurd ⟨Y, hY Tstar u p hsol⟩ hblow

/-! ## Proved: the BKM Gronwall step (`log`-Gronwall) -/

/-- If `y ≥ 0` is continuous and right-differentiable on `[0,T)` with
`y' ≤ K (1 + log(1+y)) y`, then `y ≤ exp((1 + log(1 + y 0)) e^{KT})` on `[0,T)`. -/
theorem log_gronwall {y : ℝ → ℝ} {T K : ℝ} (hK : 0 ≤ K)
    (hy0 : ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ y t) (hc : ContinuousOn y (Ico (0 : ℝ) T))
    (hd' : ∀ s ∈ Ico (0 : ℝ) T, ∃ d : ℝ, HasDerivWithinAt y d (Ici s) s ∧
      d ≤ K * (1 + Real.log (1 + y s)) * y s) :
    ∀ t ∈ Ico (0 : ℝ) T, y t ≤ Real.exp ((1 + Real.log (1 + y 0)) * Real.exp (K * T)) := by
  choose! d hd using hd'
  intro t ht
  set f : ℝ → ℝ := fun s => 1 + Real.log (1 + y s) with hf
  have hsub : Icc (0 : ℝ) t ⊆ Ico 0 T := fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  have hpos : ∀ s ∈ Ico (0 : ℝ) T, 0 < 1 + y s := fun s hs => by linarith [hy0 s hs]
  have hL : ∀ s ∈ Ico (0 : ℝ) T, 0 ≤ Real.log (1 + y s) := fun s hs =>
    Real.log_nonneg (by linarith [hy0 s hs])
  have h0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, lt_of_le_of_lt ht.1 ht.2⟩
  have hcont : ContinuousOn f (Icc 0 t) := by
    refine continuousOn_const.add (ContinuousOn.log (continuousOn_const.add (hc.mono hsub)) ?_)
    exact fun s hs => (hpos s (hsub hs)).ne'
  have hderiv : ∀ s ∈ Ico (0 : ℝ) t,
      HasDerivWithinAt f (d s / (1 + y s)) (Ici s) s := fun s hs => by
    have hs' : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
    exact (((hd s hs').1.const_add 1).log (hpos s hs').ne').const_add 1
  have hbnd : ∀ s ∈ Ico (0 : ℝ) t, d s / (1 + y s) ≤ K * f s + 0 := by
    intro s hs
    have hs' : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
    have hb := (hd s hs').2
    have hy := hy0 s hs'
    have hl := hL s hs'
    have hKf : 0 ≤ K * (1 + Real.log (1 + y s)) := mul_nonneg hK (by linarith)
    rw [div_le_iff₀ (hpos s hs')]
    simp only [hf, add_zero]
    nlinarith
  have hG := le_gronwallBound_of_liminf_deriv_right_le (f := f) (f' := fun s => d s / (1 + y s))
    (K := K) (ε := 0) hcont
    (fun s hs r hr => (hderiv s hs).liminf_right_slope_le hr) le_rfl hbnd t ⟨ht.1, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at hG
  have hf0 : 0 ≤ f 0 := by simp only [hf]; linarith [hL 0 h0]
  have hKt : Real.exp (K * t) ≤ Real.exp (K * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2.le hK)
  have hft : Real.log (1 + y t) ≤ (1 + Real.log (1 + y 0)) * Real.exp (K * T) := by
    have := hG.trans (mul_le_mul_of_nonneg_left hKt hf0)
    simp only [hf] at this; linarith
  have := (Real.log_le_iff_le_exp (hpos t ht)).1 hft
  linarith

/-- Spatial slice of a jointly smooth field on `ℝ³ × [0,T)`. -/
lemma contDiff_slice {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : T3 × ℝ → F}
    {T t : ℝ} (hg : ContDiffOn ℝ ∞ g (univ ×ˢ Ico (0 : ℝ) T)) (ht : t ∈ Ico (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun x : T3 => g (x, t)) := by
  have hm : MapsTo (fun x : T3 => (x, t)) univ (univ ×ˢ Ico (0 : ℝ) T) :=
    fun _ _ => ⟨trivial, ht⟩
  have := hg.comp (contDiff_id.prodMk contDiff_const).contDiffOn hm
  exact contDiffOn_univ.1 this

/-! ## Proved: vorticity ceiling ⟹ `H³` bound (BKM's argument), hence no blow-up -/

/-- **BKM continuation, proved from the two named inputs.** -/
theorem katoBKMMaximal_of_kato_of_log {ν : ℝ} {u₀ : VelocityField} (hdec : FeffermanDecay u₀)
    (hlog : BKMLogInequality) (hK : KatoMaximalSolution ν u₀) : KatoBKMMaximal ν u₀ := by
  obtain ⟨S, u, p, Ck, hCk, hsol, hfin, hcont, hder, hS⟩ := hK
  rcases hS with rfl | ⟨Tstar, hT, rfl, hblow⟩
  · exact ⟨u, p, Or.inl fun T => hsol T Ico_subset_Ici_self⟩
  refine ⟨u, p, Or.inr ⟨Tstar, hT, hsol Tstar subset_rfl, ?_⟩⟩
  rintro ⟨Y, hY⟩
  obtain ⟨C, hC, hlogC⟩ := hlog
  have hs := hsol Tstar subset_rfl
  have hE := lintegral_sq_lt_top_of_feffermanDecay hdec
  set E0 := (∫⁻ x, ‖u₀ x‖ₑ ^ 2).toReal
  set Y' := max Y 0
  set K := Ck * (C * (1 + E0 + Y'))
  have hE0 : 0 ≤ E0 := ENNReal.toReal_nonneg
  have hKnn : 0 ≤ K := mul_nonneg hCk (mul_nonneg hC.le (by positivity))
  have hbound := log_gronwall (y := fun t => hsSq 3 (u t)) (T := Tstar) (K := K)
    hKnn
    (fun t _ => hsSq_nonneg _ _) hcont ?_
  · obtain ⟨t, ht, hlt⟩ := hblow (Real.exp ((1 + Real.log (1 + hsSq 3 (u 0))) *
      Real.exp (K * Tstar)))
    exact absurd (hbound t ht) (not_le.2 hlt)
  intro s hsS
  obtain ⟨d, hdd, hdle⟩ := hder s hsS
  refine ⟨d, hdd, hdle.trans ?_⟩
  have hsm : ContDiff ℝ ∞ (u s) := contDiff_slice (g := fun q : T3 × ℝ => u q.2 q.1) hs.1 hsS
  have hdiv : ∀ x, div (u s) x = 0 := fun x => (hs.2.2.1 s hsS x).2
  obtain ⟨-, hgrad⟩ := hlogC (u s) hsm hdiv (hfin s hsS)
  have hl2 : l2Sq (u s) ≤ E0 := ENNReal.toReal_mono hE.ne (hs.2.2.2.2 s hsS)
  have hM : Mω u s ≤ Y' := (hY s hsS).2.trans (le_max_left _ _)
  have hM0 : 0 ≤ Mω u s := mω_nonneg u s
  have hY0 : 0 ≤ Y' := le_max_right _ _
  set L := Real.log (1 + hsSq 3 (u s))
  have hL : 0 ≤ L := Real.log_nonneg (by linarith [hsSq_nonneg 3 (u s)])
  have hl20 : 0 ≤ l2Sq (u s) := ENNReal.toReal_nonneg
  have hin : 1 + l2Sq (u s) + Mω u s * (1 + L) ≤ (1 + E0 + Y') * (1 + L) := by
    nlinarith [mul_le_mul_of_nonneg_right hM (by linarith : (0 : ℝ) ≤ 1 + L)]
  have hG : gradSup (u s) ≤ C * ((1 + E0 + Y') * (1 + L)) :=
    hgrad.trans (mul_le_mul_of_nonneg_left (by simpa [Mω] using hin) hC.le)
  have hy := hsSq_nonneg 3 (u s)
  calc Ck * gradSup (u s) * hsSq 3 (u s)
      ≤ Ck * (C * ((1 + E0 + Y') * (1 + L))) * hsSq 3 (u s) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG hCk) hy
    _ = K * (1 + L) * hsSq 3 (u s) := by simp only [K]; ring

/-! ## Non-vacuity: the named Kato input holds at `u₀ = 0` -/

theorem katoMaximalSolution_zero (ν : ℝ) : KatoMaximalSolution ν 0 := by
  have hz : ∀ k, iteratedFDeriv ℝ k (fun _ : T3 => (0 : EuclideanSpace ℝ (Fin 3))) = 0 :=
    fun k => iteratedFDeriv_fun_zero
  have hE : sobolevEnergy 3 (0 : VelocityField) = 0 := by
    simp only [sobolevEnergy]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun α _ => ?_
    have : (0 : VelocityField) = fun _ => 0 := rfl
    simp [this, hz]
  refine ⟨Ici 0, fun _ => 0, fun _ _ => 0, 0, le_rfl, fun T _ => ?_, fun t _ => by simp [hE],
    continuousOn_const, fun s _ => ⟨0, hasDerivWithinAt_const _ _ _, by simp⟩, Or.inl rfl⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := feffermanGlobalSolution_zero ν
  refine ⟨h1.mono (prod_mono subset_rfl Ico_subset_Ici_self),
    h2.mono (prod_mono subset_rfl Ico_subset_Ici_self), fun t ht x => h3 t ht.1 x, h4,
    fun t _ => le_rfl⟩

/-! ## Assembly -/

/-- **Classical continuation on ℝ³ from the two named analytic inputs.** -/
theorem r3BKMContinuation_of_kato_of_log {ν : ℝ} (hlog : BKMLogInequality)
    (hK : ∀ u₀ : VelocityField, ContDiff ℝ ∞ u₀ → (∀ x, div u₀ x = 0) → FeffermanDecay u₀ →
      KatoMaximalSolution ν u₀) : R3BKMContinuation ν :=
  fun u₀ hs hd hdec =>
    r3BKMContinuationAt_of_katoBKMMaximal hdec
      (katoBKMMaximal_of_kato_of_log hdec hlog (hK u₀ hs hd hdec))

/-- **Clay (A) (Fefferman) from the repaired rate plus the two named classical inputs.** -/
theorem clay_A_fefferman_of_rate_of_kato_of_log
    (hrate : ∀ ν > (0 : ℝ), ∀ u₀ : VelocityField, ContDiff ℝ ∞ u₀ → (∀ x, div u₀ x = 0) →
      FeffermanDecay u₀ → FrohmanianTetherRateSmooth u₀ ν)
    (hlog : BKMLogInequality)
    (hK : ∀ ν > (0 : ℝ), ∀ u₀ : VelocityField, ContDiff ℝ ∞ u₀ → (∀ x, div u₀ x = 0) →
      FeffermanDecay u₀ → KatoMaximalSolution ν u₀) :
    Clay_A_Fefferman :=
  clay_A_fefferman_of_frohmanianTetherRateSmooth hrate
    fun ν hν => r3BKMContinuation_of_kato_of_log hlog (hK ν hν)

end R3BKM

#print axioms R3BKM.lintegral_sq_lt_top_of_feffermanDecay
#print axioms R3BKM.feffermanGlobalSolution_of_forall
#print axioms R3BKM.r3BKMContinuationAt_of_katoBKMMaximal
#print axioms R3BKM.log_gronwall
#print axioms R3BKM.katoMaximalSolution_zero
#print axioms R3BKM.katoBKMMaximal_of_kato_of_log
#print axioms R3BKM.r3BKMContinuation_of_kato_of_log
#print axioms R3BKM.clay_A_fefferman_of_rate_of_kato_of_log
