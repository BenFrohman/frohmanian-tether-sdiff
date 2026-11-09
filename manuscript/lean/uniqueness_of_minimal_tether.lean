/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
-- NS_Millennium_Proof/Modules/Uniqueness.lean
public theorem step2_quadratic_and_locality
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h_sym : ∀ ω F G, B ω F G = B ω G F)
    (h_proj : ∀ ω (F F' G : Functional),
      Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) =
        Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F' ω) → B ω F G = B ω F' G) :
    FactorsThroughProjection B ∧
    ∀ ω (F G F' G' : Functional), FunctionalDerivative F ω = FunctionalDerivative F' ω →
      FunctionalDerivative G ω = FunctionalDerivative G' ω → B ω F G = B ω F' G' :=
  have h2 := step2_quadratic B h_sym h_proj
  ⟨h2, step1_of_factorization B h2⟩

public theorem uniqueness_of_minimal_tether_core
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h_sym : ∀ ω F G, B ω F G = B ω G F)
    (h_proj : ∀ ω (F F' G : Functional),
      Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) =
        Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F' ω) → B ω F G = B ω F' G)
    (h_density : FactorsThroughProjection B → ∃ α, HasTetherKernelDensity B α)
    (h_weight : ∀ α, HasTetherKernelDensity B α → ∃ c : ℝ, ∀ ω x, α ω x = -c * Enstrophy ω)
    (h_sat : SaturatesTetherQuadratic B)
    (h_nondeg : ∃ (ω : CoadjointOrbit) (F : Functional), Enstrophy ω * (∫ x,
        inner ℝ (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x)
          (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x) ∂NavierStokes3D.volume) ≠ 0) :
    ∀ ω F G, B ω F G = TetherKernel ω F G :=
  have h2 := (step2_quadratic_and_locality B h_sym h_proj).1
  have h3 := step3_scalar B h2 h_density h_weight
  have h4 := step4_scalar_eq_kappa B h3 h_sat h_nondeg
  step5_eq_tether B h4

public theorem uniqueness_of_minimal_tether
    (SDiff : Type*) [Group SDiff] [MulAction SDiff CoadjointOrbit]
    (_hyp : SDiffActionHyp SDiff)
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h_sym : ∀ ω F G, B ω F G = B ω G F)
    (hC1 : InvariantUnderCoadjointAction SDiff B)
    (hC2 : DegenerateWRTKineticEnergy B)
    (hC3 : ProducesControllableNegativeFeedback B)
    (h_sat : SaturatesTetherQuadratic B)
    (h_polarB : Polarizes B)
    (h_polarT : Polarizes TetherKernel) :
    ∀ (ω : CoadjointOrbit) (F G : Functional), B ω F G = TetherKernel ω F G :=
  uniqueness_of_minimal_symmetric_tether SDiff B h_sym hC1 hC2 hC3 h_sat h_polarB h_polarT
