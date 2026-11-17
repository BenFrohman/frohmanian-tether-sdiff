theorem h3IBPVanishingFlux_physicalMaximal (hdiv : ∀ x, div u₀ x = 0)
    {t : ℝ} (ht : inMaximal hf hdec hν (by norm_num : 2 ≤ 2) t) :
    H3IBPVanishingFlux (physicalMaximal hf hdec hν t)
      (presMaximal hf hdec hν t)
