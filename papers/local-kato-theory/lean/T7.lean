theorem continuousOn_hsSq_physicalMaximal {k : ℕ} (hk : 2 ≤ k) :
    ContinuousOn (fun t => hsSq 3 (physicalMaximal hf hdec hν t))
      (Smax hf hdec hν hk)
