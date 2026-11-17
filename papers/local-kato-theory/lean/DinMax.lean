def inMaximal {k : ℕ} (hk : 2 ≤ k) (t : ℝ) : Prop :=
  0 ≤ t ∧ ∃ n : ℕ, t ≤ (iteratePath hf hdec hν hk n).t
