/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
-- NS_Millennium_Proof/Modules/ConditionalRegularity.lean
public theorem frohmanian_tether_theorem
    (hKato : ∀ u₀ ν, ContDiff ℝ (⊤ : ℕ∞) u₀ → (∀ x, div u₀ x = 0) →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) → 0 < ν →
      KatoLocalWitness u₀ ν)
    (hDI : ∀ u₀ ν, FrohmanianTetherRate u₀ ν)
    (τ : ℝ) (hτ : 0 < τ)
    (hTlb : ∀ u₁ ν (hsm : ContDiff ℝ (⊤ : ℕ∞) u₁)
      (hdiv : ∀ x, div u₁ x = 0)
      (hE : Integrable (fun x : T3 => ‖u₁ x‖ ^ 2))
      (hν : 0 < ν),
      τ ≤ (hKato u₁ ν hsm hdiv hE hν).T)
    (hInt : ∀ u₀ ν (_hν : 0 < ν) (T : ℝ) (v : TimeDependentVelocity)
      (q : TimeDependentPressure),
      T ∈ existenceTimes u₀ ν →
      v 0 = u₀ →
      NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      IsPhysicalNSSolution v →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun x : T3 => ‖v t x‖ ^ 2))
    (huniq_shift : ∀ u₀ ν (_hν : 0 < ν) (T : ℝ) (v : TimeDependentVelocity)
      (q : TimeDependentPressure),
      T ∈ existenceTimes u₀ ν →
      v 0 = u₀ →
      NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      IsPhysicalNSSolution v →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        ∀ (w' : KatoLocalWitness (v t) ν),
          ∀ s ∈ Set.Icc (0 : ℝ) w'.T, v (t + s) = w'.u s)
    (huniq : ∀ u₀ ν (w : KatoLocalWitness u₀ ν),
      ∀ (T' : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
        T' ∈ existenceTimes u₀ ν →
        v 0 = u₀ →
        NS_PDE v q ν →
        (∀ t ∈ Set.Icc (0 : ℝ) T', ContDiff ℝ (⊤ : ℕ∞) (v t)) →
        IsPhysicalNSSolution v →
        ∀ t ∈ Set.Icc (0 : ℝ) T', w.u t = v t) :
  ∃ (𝔗_F : CoadjointOrbit → Functional → Functional → ℝ),
    (∀ F ω,
      FunctionalDerivative KineticEnergyHamiltonian ω =
          velocity_from_vorticity ω →
      (∀ x, div (velocity_from_vorticity ω) x = 0) →
      Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2) →
      TetheredBracket F KineticEnergyHamiltonian ω =
        ClassicalBracket F KineticEnergyHamiltonian ω) ∧
    (∀ (SDiff : Type) [Group SDiff] [MulAction SDiff CoadjointOrbit] (B : CoadjointOrbit → Functional → Functional → ℝ),
      (∀ ω F G, B ω F G = -B ω G F) →
      InvariantUnderCoadjointAction SDiff B →
      DegenerateWRTKineticEnergy B →
      ProducesControllableNegativeFeedback B →
      SaturatesTetherQuadratic B →
      Polarizes B →
      Polarizes TetherKernel →
      ∀ ω F G, B ω F G = 𝔗_F ω F G) ∧
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
