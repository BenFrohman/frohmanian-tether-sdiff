-- FrohmanianTether/Combined.lean, line 87
theorem combined_conditional_capstone
    (SDiff : Type*) [Group SDiff] [MulAction SDiff CoadjointOrbit]
    (hyp : SDiffActionHyp SDiff)
    (h_density : TetherIntegralPreserved SDiff)
    (hδ : PlanSteps.KineticEnergyDerivIsVelocity)
    (hdivω : ∀ ω x, div (velocity_from_vorticity ω) x = 0)
    (hIntω : ∀ ω, Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2))
    (ωt : ℝ → CoadjointOrbit) (hω : PlanSteps.IsCoadjointMotion SDiff ωt)
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h_sym : ∀ ω F G, B ω F G = B ω G F)
    (h_proj : ∀ ω (F F' G : Functional),
      Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) =
        Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F' ω) → B ω F G = B ω F' G)
    (h_dens : FactorsThroughProjection B → ∃ α, HasTetherKernelDensity B α)
    (h_weight : ∀ α, HasTetherKernelDensity B α → ∃ c : ℝ, ∀ ω x, α ω x = -c * Enstrophy ω)
    (h_sat : SaturatesTetherQuadratic B)
    (h_nondeg : ∃ (ω : CoadjointOrbit) (F : Functional), Enstrophy ω * (∫ x,
        inner ℝ (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x)
          (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x) ∂NavierStokes3D.volume) ≠ 0)
    (u₀ : VelocityField) (ν : ℝ)
    (h_divfree : ∀ x, div u₀ x = 0)
    (h_smooth : ContDiff ℝ (⊤ : ℕ∞) u₀)
    (h_finite_energy : Integrable (fun x : T3 => ‖u₀ x‖ ^ 2))
    (h_pos_ν : ν > 0)
    (w : KatoLocalWitness u₀ ν)
    (hRate : FrohmanianTetherRate u₀ ν)
    (hClose : ClayStatements.FrohmanianTetherClosingBound ν)
    (hcrit : TetheredLyapunov.PhysicalBKMContinuationCriterionFor u₀ ν)
    (huniq : TetheredLyapunov.KatoUniquenessOnExistenceTimes u₀ ν w) :
    -- (1) C1, C2, C3 for the tether
    (InvariantUnderCoadjointAction SDiff TetherKernel ∧
      DegenerateWRTKineticEnergy TetherKernel ∧
      ProducesControllableNegativeFeedback TetherKernel) ∧
    -- (2) canonicity: B is the tether
    (∀ ω F G, B ω F G = TetherKernel ω F G) ∧
    -- (3) Casimirs conserved along the coadjoint motion
    (∀ f t, Casimir f (ωt t) = Casimir f (ωt 0)) ∧
    -- (4) no damping: T(M,H) = 0
    (∀ ω M, TetherKernel ω KineticEnergyHamiltonian M = 0) ∧
    -- (5) analytic layer, conditional on hRate / hClose
    TetheredLyapunov.PhysicalVorticityCubicRate u₀ ν ∧
    (∃ (u : ℝ → VelocityField) (p : ℝ → PressureField),
      NS_PDE u p ν ∧ u 0 = u₀ ∧
      (∀ t ≥ (0 : ℝ), ContDiff ℝ (⊤ : ℕ∞) (u t)) ∧
      (∀ t ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u t)) ≥ 0) ∧
      (∀ t ≥ (0 : ℝ), ∀ x, div (u t) x = 0)) := ...
