theorem hsSq_blowup_alternative {k : ℕ} (hk : 2 ≤ k) :
    Smax hf hdec hν hk = Ici (0 : ℝ) ∨
      ∃ Tstar : ℝ, 0 < Tstar ∧
        Smax hf hdec hν hk = Ico 0 Tstar ∧
        ∀ B : ℝ, ∃ t, t ∈ Ico (0 : ℝ) Tstar ∧
          B < hsSq 3 (physicalMaximal hf hdec hν t)
