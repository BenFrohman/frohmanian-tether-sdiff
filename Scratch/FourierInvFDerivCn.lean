import Scratch.FourierInvFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Higher joint regularity of the uncurried inverse Fourier transform

Mutual induction: for every `n`, the uncurried map `(x, G) ↦ 𝓕⁻ G x` and the
evaluation map `x ↦ (G ↦ 𝓕⁻ G x)` are `C^n` whenever `m ≥ n + 3`.  The
successor step reuses the `C²` decomposition of `jointFDeriv` and the
operator expansion of `spatFDerivCLM`. -/

open MeasureTheory Filter Topology Set
open scoped ContDiff

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 200000

noncomputable section
namespace FourierInvFDeriv

open LerayHeat SobolevHilbert InverseSobolev NonlinearHm InclNSN
  FourierInvBCF SobolevFourier NonlinearSmooth VectorFourier

lemma two_le_of_add_three {n m : ℕ} (hm : n + 3 ≤ m) : 2 ≤ m := by
  omega

lemma three_le_of_add_three {n m : ℕ} (hm : n + 3 ≤ m) : 3 ≤ m := by
  omega

lemma four_le_of_succ_add {n m : ℕ} (hm : n + 1 + 3 ≤ m) : 4 ≤ m := by
  omega

lemma three_le_of_succ_add {n m : ℕ} (hm : n + 1 + 3 ≤ m) : 3 ≤ m := by
  omega

lemma le_of_succ_add_three {n m : ℕ} (hm : n + 1 + 3 ≤ m) : n + 3 ≤ m := by
  omega

lemma add_three_le_pred {n m : ℕ} (hm : n + 1 + 3 ≤ m) : n + 3 ≤ m - 1 := by
  omega

lemma three_le_pred_of_succ_add {n m : ℕ} (hm : n + 1 + 3 ≤ m) : 3 ≤ m - 1 := by
  omega

/-- The first-order multiplier as a real continuous linear map. -/
def dH_real {m : ℕ} (hm : 3 ≤ m) (j : Fin 3) : Hm m →L[ℝ] Hm (m - 1) :=
  (isBoundedLinearMap_restrictCLM
      (dH (one_le_of_three hm) j : Hm m →L[ℂ] Hm (m - 1))
      (fun c x => real_smul_eq_coe_smul c x)
      (fun c y => real_smul_eq_coe_smul c y)).toContinuousLinearMap

lemma dH_real_apply {m : ℕ} (hm : 3 ≤ m) (j : Fin 3) (G : Hm m) :
    dH_real hm j G = dH (one_le_of_three hm) j G :=
  rfl


/-- The term in the operator expansion of `G ↦ spatFDeriv G x`. -/
def spatTermCLM {m : ℕ} (hm : 3 ≤ m) (j : Fin 3) :
    (Hm (m - 1) →L[ℝ] V) →L[ℝ] (Hm m →L[ℝ] (E3 →L[ℝ] V)) :=
  (ContinuousLinearMap.compL ℝ (Hm m) V (E3 →L[ℝ] V)
      (isBoundedLinearMap_smulRight_proj j).toContinuousLinearMap).comp
    ((ContinuousLinearMap.compL ℝ (Hm m) (Hm (m - 1)) V).flip (dH_real hm j))

lemma spatTermCLM_apply {m : ℕ} (hm : 3 ≤ m) (j : Fin 3) (E : Hm (m - 1) →L[ℝ] V)
    (G : Hm m) (v : E3) :
    spatTermCLM hm j E G v = v j • E (dH (one_le_of_three hm) j G) := by
  rfl

lemma spatFDerivCLM_eq {m : ℕ} (hm : 3 ≤ m) (x : E3) :
    (isBoundedLinearMap_spatFDeriv hm x).toContinuousLinearMap =
      ∑ j : Fin 3, spatTermCLM hm j (evMap (two_le_pred_of_three hm) x) := by
  refine ContinuousLinearMap.ext fun G => ContinuousLinearMap.ext fun v => ?_
  show spatFDeriv hm G x v = _
  rw [spatFDeriv_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [spatTermCLM_apply, evMap_apply]
  rfl


/-- Operator-norm Lipschitz estimate for `evMap`. -/
lemma norm_evMap_sub_le {m : ℕ} (hm : 3 ≤ m) (x y : E3) :
    ‖evMap (two_le_of_three hm) y - evMap (two_le_of_three hm) x‖ ≤
      spatFDerivBound hm * ‖y - x‖ := by
  have hC0 : 0 ≤ spatFDerivBound hm := spatFDerivBound_nonneg hm
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hC0 (norm_nonneg (y - x))) ?_
  intro H
  have h := norm_fourierInvBCF_sub_le hm H y x
  have : ‖evMap (two_le_of_three hm) y H - evMap (two_le_of_three hm) x H‖ ≤
      spatFDerivBound hm * ‖H‖ * ‖y - x‖ := by
    simpa [evMap_apply] using h
  have hH : spatFDerivBound hm * ‖H‖ * ‖y - x‖ ≤
      (spatFDerivBound hm * ‖y - x‖) * ‖H‖ := by
    ring_nf
    exact le_of_eq rfl
  exact (this.trans hH)

lemma continuous_evMap {m : ℕ} (hm : 3 ≤ m) :
    Continuous (evMap (two_le_of_three hm) :
      E3 → (Hm m →L[ℝ] V)) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  refine (tendsto_iff_norm_sub_tendsto_zero
      (E := Hm m →L[ℝ] V)
      (f := (evMap (two_le_of_three hm) : E3 → (Hm m →L[ℝ] V)))
      (b := evMap (two_le_of_three hm) x)).2 ?_
  let C := spatFDerivBound hm
  have hle : ∀ y : E3,
      ‖evMap (two_le_of_three hm) y - evMap (two_le_of_three hm) x‖ ≤ C * ‖y - x‖ :=
    fun y => norm_evMap_sub_le hm x y
  have h0 : Tendsto (fun y : E3 => C * ‖y - x‖) (𝓝 x) (𝓝 0) := by
    have hnorm : Tendsto (fun y : E3 => ‖y - x‖) (𝓝 x) (𝓝 0) :=
      tendsto_norm_sub_self x
    have hmul := (tendsto_const_nhds (x := C)).mul hnorm
    simpa using hmul
  exact squeeze_zero
    (fun y => norm_nonneg (evMap (two_le_of_three hm) y - evMap (two_le_of_three hm) x))
    hle h0



/-- `G ↦ spatFDeriv G x` as a continuous linear map. -/
def spatCLM {m : ℕ} (hm : 3 ≤ m) (x : E3) : Hm m →L[ℝ] (E3 →L[ℝ] V) :=
  (isBoundedLinearMap_spatFDeriv hm x).toContinuousLinearMap

lemma contDiff_spatTermCLM {m : ℕ} {n : WithTop ℕ∞} (hm : 3 ≤ m) (j : Fin 3) :
    ContDiff ℝ n (spatTermCLM hm j) :=
  ContinuousLinearMap.contDiff _

/-- Flipping the arguments of an operator-valued operator. -/
def flipCLM (m : ℕ) : (Hm m →L[ℝ] (E3 →L[ℝ] V)) →L[ℝ] (E3 →L[ℝ] (Hm m →L[ℝ] V)) :=
  (ContinuousLinearMap.flipₗᵢ ℝ (Hm m) E3 V).toContinuousLinearEquiv.toContinuousLinearMap

lemma contDiff_flipCLM {m : ℕ} {n : WithTop ℕ∞} : ContDiff ℝ n (flipCLM m) :=
  ContinuousLinearMap.contDiff _

lemma evFDeriv_eq_flipCLM {m : ℕ} (hm : 3 ≤ m) (x : E3) :
    evFDeriv hm x = flipCLM m (spatCLM hm x) :=
  rfl

lemma contDiff_spatTermCLM_comp {m : ℕ} {n : WithTop ℕ∞} (hm : 3 ≤ m) (j : Fin 3)
    {f : E3 → (Hm (m - 1) →L[ℝ] V)} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => spatTermCLM hm j (f x)) :=
  (contDiff_spatTermCLM hm j).comp hf

lemma contDiff_evFDeriv_of {m : ℕ} {n : WithTop ℕ∞} (hm : 3 ≤ m)
    (h : ContDiff ℝ n (spatCLM hm)) : ContDiff ℝ n (evFDeriv hm) := by
  have hfun : evFDeriv hm = fun x => flipCLM m (spatCLM hm x) :=
    funext fun x => evFDeriv_eq_flipCLM hm x
  rw [hfun]
  exact contDiff_flipCLM.comp h

/-- Joint `C^n` regularity of the uncurried inverse Fourier transform and of
evaluation in the representative, for `m ≥ n + 3`. -/
lemma contDiff_uncurry_and_evMap (n : ℕ) :
    (∀ ⦃m : ℕ⦄ (hm : n + 3 ≤ m),
      ContDiff ℝ n (uncurryFourierInvBCF (two_le_of_add_three hm))) ∧
    (∀ ⦃m : ℕ⦄ (hm : n + 3 ≤ m),
      ContDiff ℝ n (evMap (two_le_of_add_three hm))) := by
  induction n with
  | zero =>
    refine ⟨?uncurry0, ?ev0⟩
    · intro m hm
      exact contDiff_zero.2 (continuous_uncurryFourierInvBCF (two_le_of_add_three hm))
    · intro m hm
      exact contDiff_zero.2 (continuous_evMap (three_le_of_add_three hm))
  | succ n ih =>
    refine ⟨?uncurryS, ?evS⟩
    · intro m hm
      have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 :=
        Nat.cast_succ n
      rw [hcast, contDiff_succ_iff_fderiv]
      refine ⟨differentiable_uncurryFourierInvBCF (three_le_of_succ_add hm),
        ?_, ?_⟩
      · intro hω
        exact ((WithTop.natCast_ne_top (α := ℕ∞) n) hω).elim
      · have hfun :
            fderiv ℝ (uncurryFourierInvBCF (two_le_of_add_three hm)) =
              fun p => jointFDeriv (three_le_of_succ_add hm) p.1 p.2 :=
          funext fun p =>
            fderiv_uncurryFourierInvBCF (three_le_of_succ_add hm) p.1 p.2
        refine hfun ▸ ?_
        have hdecomp :
            (fun p : E3 × Hm m => jointFDeriv (three_le_of_succ_add hm) p.1 p.2) =
              fun p =>
                compFstCLM m (spatFDeriv (three_le_of_succ_add hm) p.2 p.1) +
                  compSndCLM m (evMap (two_le_of_add_three hm) p.1) := by
          funext p
          exact jointFDeriv_eq_comp (three_le_of_succ_add hm) p.1 p.2
        rw [hdecomp]
        have hspat0 : ContDiff ℝ n (fun p : E3 × Hm m =>
            spatFDeriv (three_le_of_succ_add hm) p.2 p.1) := by
          have hunc : ContDiff ℝ n
              (uncurryFourierInvBCF (two_le_of_add_three (add_three_le_pred hm))) :=
            ih.1 (add_three_le_pred hm)
          have hterm : ∀ j : Fin 3,
              ContDiff ℝ n (fun p : E3 × Hm m =>
                (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight
                  (uncurryFourierInvBCF (two_le_of_add_three (add_three_le_pred hm))
                    (p.1, dH (one_le_of_three (three_le_of_succ_add hm)) j p.2))) := by
            intro j
            have hcomp : ContDiff ℝ n (fun p : E3 × Hm m =>
                uncurryFourierInvBCF (two_le_of_add_three (add_three_le_pred hm))
                  (p.1, dH (one_le_of_three (three_le_of_succ_add hm)) j p.2)) :=
              hunc.comp (contDiff_id_dH (three_le_of_succ_add hm) j)
            exact (isBoundedLinearMap_smulRight_proj j).contDiff.comp hcomp
          have heq :
              (fun p : E3 × Hm m => spatFDeriv (three_le_of_succ_add hm) p.2 p.1) =
                fun p => ∑ j : Fin 3,
                  (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight
                    (uncurryFourierInvBCF
                      (two_le_of_add_three (add_three_le_pred hm))
                      (p.1, dH (one_le_of_three (three_le_of_succ_add hm)) j p.2)) := by
            funext p
            exact ContinuousLinearMap.ext fun v => by
              rw [spatFDeriv_apply]
              rfl
          rw [heq]
          exact ContDiff.sum (fun j _ => hterm j)
        have hspat : ContDiff ℝ n (fun p : E3 × Hm m =>
            compFstCLM m (spatFDeriv (three_le_of_succ_add hm) p.2 p.1)) :=
          (compFstCLM m).contDiff.comp hspat0
        have hev : ContDiff ℝ n (fun p : E3 × Hm m =>
            compSndCLM m (evMap (two_le_of_add_three hm) p.1)) :=
          (compSndCLM m).contDiff.comp ((ih.2 (le_of_succ_add_three hm)).comp contDiff_fst)
        exact hspat.add hev
    · intro m hm
      have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 :=
        Nat.cast_succ n
      rw [hcast, contDiff_succ_iff_fderiv]
      refine ⟨differentiable_evMap (four_le_of_succ_add hm), ?_, ?_⟩
      · intro hω
        exact ((WithTop.natCast_ne_top (α := ℕ∞) n) hω).elim
      · have hfun :
            fderiv ℝ (evMap (two_le_of_add_three hm)) =
              evFDeriv (three_le_of_succ_add hm) :=
          funext fun x => fderiv_evMap (four_le_of_succ_add hm) x
        refine hfun ▸ ?_
        refine contDiff_evFDeriv_of (three_le_of_succ_add hm) ?_
        have heq : spatCLM (three_le_of_succ_add hm) =
            fun x => ∑ j : Fin 3, spatTermCLM (three_le_of_succ_add hm) j
              (evMap (two_le_of_add_three (add_three_le_pred hm)) x) :=
          funext fun x => spatFDerivCLM_eq (three_le_of_succ_add hm) x
        rw [heq]
        exact ContDiff.sum fun j _ =>
          contDiff_spatTermCLM_comp (three_le_of_succ_add hm) j (ih.2 (add_three_le_pred hm))

/-- The uncurried inverse Fourier transform is jointly `C^n` on `ℝ³ × Ĥ^m`
when `m ≥ n + 3`. -/
theorem contDiff_uncurryFourierInvBCF {m n : ℕ} (hm : n + 3 ≤ m) :
    ContDiff ℝ n (uncurryFourierInvBCF (two_le_of_add_three hm)) :=
  (contDiff_uncurry_and_evMap n).1 hm

/-- Evaluation in the representative is `C^n` in the spatial variable when
`m ≥ n + 3`. -/
theorem contDiff_evMap {m n : ℕ} (hm : n + 3 ≤ m) :
    ContDiff ℝ n (evMap (two_le_of_add_three hm)) :=
  (contDiff_uncurry_and_evMap n).2 hm

/-- Post-composing the uncurried inverse Fourier transform with a `C^n` path
in `Ĥ^m` (`m ≥ n + 3`) yields a jointly `C^n` field on `ℝ³ × [0, T)`. -/
theorem contDiffOn_uncurry_path {m n : ℕ} (hm : n + 3 ≤ m)
    {T : ℝ} {γ : ℝ → Hm m} (hγ : ContDiffOn ℝ n γ (Ico 0 T)) :
    ContDiffOn ℝ n
      (fun q : E3 × ℝ =>
        uncurryFourierInvBCF (two_le_of_add_three hm) (q.1, γ q.2))
      (univ ×ˢ Ico 0 T) := by
  have hpath : ContDiffOn ℝ n (fun q : E3 × ℝ => (q.1, γ q.2))
      (univ ×ˢ Ico 0 T) :=
    ContDiffOn.prodMk contDiff_fst.contDiffOn
      (hγ.comp contDiffOn_snd fun q hq => hq.2)
  exact (contDiff_uncurryFourierInvBCF hm).comp_contDiffOn hpath

theorem contDiffOn_uncurry_clm_path {m n : ℕ} (hm : n + 3 ≤ m)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : V →L[ℝ] F)
    {T : ℝ} {γ : ℝ → Hm m} (hγ : ContDiffOn ℝ n γ (Ico 0 T)) :
    ContDiffOn ℝ n (fun q : E3 × ℝ =>
      L (uncurryFourierInvBCF (two_le_of_add_three hm) (q.1, γ q.2)))
      (univ ×ˢ Ico 0 T) :=
  L.contDiff.comp_contDiffOn (contDiffOn_uncurry_path hm hγ)

#print axioms FourierInvFDeriv.continuous_evMap
#print axioms FourierInvFDeriv.contDiff_uncurryFourierInvBCF
#print axioms FourierInvFDeriv.contDiff_evMap
#print axioms FourierInvFDeriv.contDiffOn_uncurry_path
#print axioms FourierInvFDeriv.contDiffOn_uncurry_clm_path

end FourierInvFDeriv
