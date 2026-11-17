theorem clay_A_fefferman_of_rate
    (hrate : ∀ ν > (0 : ℝ), ∀ u₀ : VelocityField, ContDiff ℝ ∞ u₀ →
      (∀ x, div u₀ x = 0) → FeffermanDecay u₀ → FrohmanianTetherRateSmooth u₀ ν) :
    Clay_A_Fefferman
