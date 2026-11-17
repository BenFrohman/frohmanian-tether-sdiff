theorem isFeffermanSolutionOn_physicalMaximal (hdiv : ∀ x, div u₀ x = 0)
    {T : ℝ} (hS : Ico (0 : ℝ) T ⊆ Smax hf hdec hν (by norm_num : 2 ≤ 2)) :
    IsFeffermanSolutionOn ν T u₀
      (physicalMaximal hf hdec hν) (presMaximal hf hdec hν)
