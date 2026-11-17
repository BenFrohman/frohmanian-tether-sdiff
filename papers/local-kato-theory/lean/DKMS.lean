def KatoMaximalSolution (ν : ℝ) (u₀ : VelocityField) : Prop :=
  ∃ (S : Set ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure) (Ck : ℝ), 0 ≤ Ck ∧
    (∀ T : ℝ, Ico (0 : ℝ) T ⊆ S → IsFeffermanSolutionOn ν T u₀ u p) ∧
    (∀ t ∈ S, sobolevEnergy 3 (u t) < ⊤) ∧
    ContinuousOn (fun t => hsSq 3 (u t)) S ∧
    (∀ s ∈ S, ∃ d : ℝ, HasDerivWithinAt (fun t => hsSq 3 (u t)) d (Ici s) s ∧
      d ≤ Ck * gradSup (u s) * hsSq 3 (u s)) ∧
    (S = Ici 0 ∨ ∃ Tstar : ℝ, 0 < Tstar ∧ S = Ico 0 Tstar ∧
      ∀ B : ℝ, ∃ t ∈ S, B < hsSq 3 (u t))
