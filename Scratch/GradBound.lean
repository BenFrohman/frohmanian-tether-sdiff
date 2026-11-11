import Scratch.FourierCutoff
import Scratch.R3BKMContinuation

/-! # Bounded gradient from finite `H³` energy on ℝ³ (BKMLogInequality, item 1)

`‖∇u(x)‖ ≤ C ‖u‖_{H³}` for smooth `u : ℝ³ → ℝ³`, one absolute constant `C < ∞`
(no decay assumed); hence `sobolevEnergy 3 u < ⊤ → BddAbove (range ‖∇u‖)`. -/

open MeasureTheory FourierCutoff FourierEmb
open scoped ENNReal ContDiff

noncomputable section
namespace GradBound

/-- `y = ∑ y_i eᵢ` and `‖y‖ ≤ ∑ |y_i|`. -/
lemma norm_le_sum_coord (y : E3) : ‖y‖ ≤ ∑ i : Fin 3, |y i| := by
  conv_lhs => rw [eq_sum_basis y]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]

lemma norm_clm_le (L : E3 →L[ℝ] E3) :
    ‖L‖ ≤ ∑ k : Fin 3, ‖L (EuclideanSpace.single k (1 : ℝ))‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : L v = ∑ i : Fin 3, v i • L (EuclideanSpace.single i (1 : ℝ)) := by
    conv_lhs => rw [eq_sum_basis v]
    simp [map_sum]
  rw [hv, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ _) (norm_nonneg _)

/-- `∂ₖ uⱼ`. -/
def dkj (u : E3 → E3) (k j : Fin 3) : E3 → ℝ :=
  fun y => fderiv ℝ u y (EuclideanSpace.single k (1 : ℝ)) j

lemma U_snoc {m : ℕ} (α : Fin m → Fin 3) (k : Fin 3) :
    U (Fin.snoc α k : Fin (m + 1) → Fin 3) =
      Fin.snoc (U α) (EuclideanSpace.single k (1 : ℝ)) := by
  have := Fin.comp_snoc (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)) α k
  exact this

lemma iter_dkj {u : E3 → E3} (hu : ContDiff ℝ ∞ u) (k j : Fin 3) (m : ℕ)
    (α : Fin m → Fin 3) (y : E3) :
    iteratedFDeriv ℝ m (dkj u k j) y (U α) =
      iteratedFDeriv ℝ (m + 1) u y (U (Fin.snoc α k : Fin (m + 1) → Fin 3)) j := by
  have hF : ContDiff ℝ ∞ (fun y => fderiv ℝ u y (EuclideanSpace.single k (1 : ℝ))) :=
    (hu.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  have hc := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).iteratedFDeriv_comp_left
    (hF.contDiffAt (x := y)) (i := m) (by exact_mod_cast le_top)
  have h2 : dkj u k j = (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) ∘
      (fun y => fderiv ℝ u y (EuclideanSpace.single k (1 : ℝ))) := rfl
  rw [h2, hc, iteratedFDeriv_succ_apply_right, U_snoc, Fin.init_snoc, Fin.snoc_last]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  rw [iteratedFDeriv_clm_apply_const_apply (hu.fderiv_right (m := ∞) le_rfl)
    (by exact_mod_cast le_top)]
  rfl

/-- `‖∂ₖuⱼ‖²_{H²} ≤ ‖u‖²_{H³}`. -/
lemma energyR_dkj_le {u : E3 → E3} (hu : ContDiff ℝ ∞ u) (k j : Fin 3) :
    energyR 2 (dkj u k j) ≤ R3BKM.sobolevEnergy 3 u := by
  have step : ∀ m : ℕ, ∑ α : Fin m → Fin 3, ∫⁻ x, ‖iteratedFDeriv ℝ m (dkj u k j) x (U α)‖ₑ ^ 2
      ≤ ∑ β : Fin (m + 1) → Fin 3, ∫⁻ x, ‖iteratedFDeriv ℝ (m + 1) u x (U β)‖ₑ ^ 2 := by
    intro m
    have hinj : Set.InjOn (fun α : Fin m → Fin 3 => (Fin.snoc α k : Fin (m + 1) → Fin 3))
        (Finset.univ : Finset (Fin m → Fin 3)) := fun a _ b _ hab =>
      (Fin.snoc_injective2 hab).1
    calc _ ≤ ∑ α : Fin m → Fin 3, ∫⁻ x,
          ‖iteratedFDeriv ℝ (m + 1) u x (U (Fin.snoc α k : Fin (m + 1) → Fin 3))‖ₑ ^ 2 := by
          refine Finset.sum_le_sum fun α _ => lintegral_mono fun x => ?_
          rw [iter_dkj hu]
          gcongr
          exact PiLp.enorm_apply_le _ _
      _ = ∑ β ∈ Finset.univ.image (fun α : Fin m → Fin 3 => (Fin.snoc α k : Fin (m + 1) → Fin 3)),
          ∫⁻ x, ‖iteratedFDeriv ℝ (m + 1) u x (U β)‖ₑ ^ 2 :=
          (Finset.sum_image (f := fun β => ∫⁻ x, ‖iteratedFDeriv ℝ (m + 1) u x (U β)‖ₑ ^ 2)
            hinj).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ => zero_le _
  unfold energyR R3BKM.sobolevEnergy
  calc _ ≤ ∑ m ∈ Finset.range 3, ∑ β : Fin (m + 1) → Fin 3,
        ∫⁻ x, ‖iteratedFDeriv ℝ (m + 1) u x (U β)‖ₑ ^ 2 := Finset.sum_le_sum fun m _ => step m
    _ ≤ _ := by
      rw [Finset.sum_range_succ' _ 3]
      exact le_self_add

/-- **`‖∇u‖_∞ ≤ C ‖u‖_{H³}` on ℝ³.** -/
theorem norm_fderiv_le_sobolevEnergy :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : E3 → E3, ContDiff ℝ ∞ u → ∀ x : E3,
      ENNReal.ofReal ‖fderiv ℝ u x‖ ≤ C * R3BKM.sobolevEnergy 3 u ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hCb⟩ := abs_le_energyR
  refine ⟨9 * C, ENNReal.mul_ne_top (by simp) hC, fun u hu x => ?_⟩
  have hd : ∀ k j, ContDiff ℝ ∞ (dkj u k j) := fun k j =>
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).contDiff.comp
      ((hu.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const)
  set S := R3BKM.sobolevEnergy 3 u ^ (1 / 2 : ℝ)
  have hkj : ∀ k j, ENNReal.ofReal |dkj u k j x| ≤ C * S := fun k j =>
    (hCb _ (hd k j) x).trans
      (mul_le_mul_left' (ENNReal.rpow_le_rpow (energyR_dkj_le hu k j) (by norm_num)) C)
  have hnorm : ‖fderiv ℝ u x‖ ≤ ∑ k : Fin 3, ∑ j : Fin 3, |dkj u k j x| :=
    (norm_clm_le _).trans (Finset.sum_le_sum fun k _ => norm_le_sum_coord _)
  calc ENNReal.ofReal ‖fderiv ℝ u x‖
      ≤ ENNReal.ofReal (∑ k : Fin 3, ∑ j : Fin 3, |dkj u k j x|) := ENNReal.ofReal_le_ofReal hnorm
    _ = ∑ k : Fin 3, ∑ j : Fin 3, ENNReal.ofReal |dkj u k j x| := by
        rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _]
        exact Finset.sum_congr rfl fun k _ =>
          ENNReal.ofReal_sum_of_nonneg fun _ _ => abs_nonneg _
    _ ≤ ∑ k : Fin 3, ∑ j : Fin 3, C * S :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun j _ => hkj k j
    _ = 9 * C * S := by simp [Finset.sum_const]; ring

/-- **BKMLogInequality, item 1**: finite `H³` energy gives a bounded gradient. -/
theorem bddAbove_norm_fderiv {u : E3 → E3} (hu : ContDiff ℝ ∞ u)
    (hE : R3BKM.sobolevEnergy 3 u < ⊤) : BddAbove (Set.range fun x => ‖fderiv ℝ u x‖) := by
  obtain ⟨C, hC, hb⟩ := norm_fderiv_le_sobolevEnergy
  set M := C * R3BKM.sobolevEnergy 3 u ^ (1 / 2 : ℝ)
  have hM : M ≠ ⊤ := ENNReal.mul_ne_top hC (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hE.ne)
  refine ⟨M.toReal, ?_⟩
  rintro _ ⟨x, rfl⟩
  have := hb u hu x
  exact (ENNReal.ofReal_le_iff_le_toReal hM).1 this

end GradBound

#print axioms GradBound.norm_fderiv_le_sobolevEnergy
#print axioms GradBound.bddAbove_norm_fderiv
