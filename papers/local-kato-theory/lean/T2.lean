theorem katoPonce_h3_energy_physicalMaximal (hdiv : ∀ x, div u₀ x = 0) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧
      ∀ s ∈ Smax hf hdec hν (by norm_num : 2 ≤ 2),
        ∃ d : ℝ,
          HasDerivWithinAt (fun t => hsSq 3 (physicalMaximal hf hdec hν t)) d
            (Ici s) s ∧
          d ≤ Ck * gradSup (physicalMaximal hf hdec hν s) *
            hsSq 3 (physicalMaximal hf hdec hν s)
