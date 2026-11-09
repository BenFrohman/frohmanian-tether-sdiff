-- FrohmanianTether/ConditionalRegularity.lean, line 93
public theorem frohmanian_tether_theorem
    (hKato : ∀ u₀ ν, ContDiff ℝ (⊤ : ℕ∞) u₀ → (∀ x, div u₀ x = 0) →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) → 0 < ν →
      KatoLocalWitness u₀ ν)
    (hDI : ∀ u₀ ν, FrohmanianTetherRate u₀ ν)
    (hcrit : ∀ u₀ ν, TetheredLyapunov.PhysicalBKMContinuationCriterionFor u₀ ν)
    (huniq : ∀ u₀ ν (w : KatoLocalWitness u₀ ν),
      TetheredLyapunov.KatoUniquenessOnExistenceTimes u₀ ν w) :
  ∃ (𝔗_F : CoadjointOrbit → Functional → Functional → ℝ),
    (∀ (B : CoadjointOrbit → Functional → Functional → ℝ)
      (α : CoadjointOrbit → T3 → ℝ),
      HasTetherKernelDensity B α →
      (∀ ω x, α ω x = canonicalTetherDensity ω x) →
      ∀ ω F G, B ω F G = 𝔗_F ω F G) ∧
    (∀ (u₀ : VelocityField) (ν : ℝ),
      0 < ν →
      (∀ x, div u₀ x = 0) →
      ContDiff ℝ (⊤ : ℕ∞) u₀ →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) →
      ∃ (u : ℝ → VelocityField) (p : ℝ → PressureField),
        NS_PDE u p ν ∧
        u 0 = u₀ ∧
        (∀ t ≥ (0 : ℝ), ContDiff ℝ (⊤ : ℕ∞) (u t)) ∧
        (∀ t ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u t)) ≥ 0) ∧
        (∀ t ≥ (0 : ℝ), ∀ x, div (u t) x = 0)) := ...
