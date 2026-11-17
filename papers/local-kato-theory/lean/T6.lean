theorem energyInequality_physicalMaximal (hdiv : ∀ x, div u₀ x = 0) {T : ℝ}
    (hS : Ico (0 : ℝ) T ⊆ Smax hf hdec hν (by norm_num : 2 ≤ 2)) :
    ∀ t ∈ Ico (0 : ℝ) T,
      ∫⁻ x, ‖physicalMaximal hf hdec hν t x‖ₑ ^ 2 ≤ ∫⁻ x, ‖u₀ x‖ₑ ^ 2
