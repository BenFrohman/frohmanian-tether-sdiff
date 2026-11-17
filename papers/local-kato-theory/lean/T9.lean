theorem Smax_eq_Ici_or_Ico {k : ℕ} (hk : 2 ≤ k) :
    Smax hf hdec hν hk = Ici 0 ∨
      ∃ Tstar : ℝ, 0 < Tstar ∧ Smax hf hdec hν hk = Ico 0 Tstar
