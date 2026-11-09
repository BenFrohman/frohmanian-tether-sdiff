/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
module

public import FrohmanianTether.SymplecticTether
public import FrohmanianTether.SymplecticConstraint
public import FrohmanianTether.Uniqueness
public import FrohmanianTether.PlanSteps
public import FrohmanianTether.ClosureBlueprint
public import FrohmanianTether.ClayStatements
public import FrohmanianTether.TetheredLyapunov

/-!
# Combined geometric + analytic layer (one target)

C1–C3 status for `TetherKernel` (checked 2026-11-04):
* C1 `InvariantUnderCoadjointAction` — CONDITIONAL on `SDiffActionHyp.casimir_invariant`
  (only that field: it gives enstrophy invariance) and `TetherIntegralPreserved` (open).
  `TetherIntegralPreserved` is supplied by any `VolumePreservingCoadjointAction`.
* C2 `DegenerateWRTKineticEnergy` — NOT PROVED. The former route assumed `δH/δω = u`
  (`KineticEnergyDerivIsVelocity`), which is false with these definitions
  (`KineticEnergyDerivative.not_forall_functionalDerivative_kineticEnergy_eq_velocity`);
  that hypothesis and every theorem using it were removed.
* C3 `ProducesControllableNegativeFeedback` — UNCONDITIONAL (`tetherKernel_C3`, equality).
* IF C2 held, symmetry would force `T(M,H) = 0` for every `M` (`tetherKernel_left_H_zero`,
  which takes C2 as a hypothesis): no damping.
-/

@[expose] public section

namespace Combined

open FrohmanianTether ArnoldGeometric NavierStokes3D MeasureTheory ForMathlib

/-- C1 from the single field `casimir_invariant` plus the open integral hypothesis. -/
theorem tetherKernel_C1_of_casimir
    (SDiff : Type*) [Group SDiff] [MulAction SDiff CoadjointOrbit]
    (hyp : SDiffActionHyp SDiff) (h_density : TetherIntegralPreserved SDiff) :
    InvariantUnderCoadjointAction SDiff TetherKernel :=
  tether_coadjoint_invariance SDiff hyp h_density

/-- C1 for any volume-preserving coadjoint action (its pullback field gives the integral). -/
theorem tetherKernel_C1_of_volumePreserving
    (SDiff : Type*) [Group SDiff] [MulAction SDiff CoadjointOrbit]
    (hyp : SDiffActionHyp SDiff) (A : Symplectori.SymplecticConstraint.VolumePreservingCoadjointAction SDiff) :
    InvariantUnderCoadjointAction SDiff TetherKernel :=
  tether_coadjoint_invariance SDiff hyp
    (Symplectori.SymplecticConstraint.volumePreservingCoadjointAction_preserves_TetherKernel A)

/-- C3, unconditional. -/
theorem tetherKernel_C3' : ProducesControllableNegativeFeedback TetherKernel :=
  tetherKernel_C3

/-- C2 + symmetry ⇒ `T(M,H) = 0` for every functional `M` (any symmetric `B`). -/
theorem left_H_zero_of_C2_symm
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h_sym : ∀ ω F G, B ω F G = B ω G F) (hC2 : DegenerateWRTKineticEnergy B)
    (ω : CoadjointOrbit) (M : Functional) :
    B ω KineticEnergyHamiltonian M = 0 := by
  rw [h_sym]; exact hC2 M ω

/-- For the tether: C2 ⇒ `T(M,H) = T(H,M) = 0`; the tether contributes no damping to `M`. -/
theorem tetherKernel_left_H_zero (hC2 : DegenerateWRTKineticEnergy TetherKernel)
    (ω : CoadjointOrbit) (M : Functional) :
    TetherKernel ω KineticEnergyHamiltonian M = 0 ∧ TetherKernel ω M KineticEnergyHamiltonian = 0 :=
  ⟨left_H_zero_of_C2_symm TetherKernel tetherKernel_comm hC2 ω M, hC2 M ω⟩

/-- **Combined conditional capstone (geometric + analytic layers).** An IMPLICATION only:
every open assumption is an explicit hypothesis. This is NOT a proof of Navier–Stokes
regularity. Nothing in the geometric layer supplies the rate hypothesis `hRate` or `hClose`
(and if C2 held, `tetherKernel_left_H_zero` would make the tether's damping coefficient 0).
C2 is not a conclusion: the former hypothesis `KineticEnergyDerivIsVelocity` is refuted
(`KineticEnergyDerivative.not_forall_functionalDerivative_kineticEnergy_eq_velocity`) and removed.

Open hypotheses: `hyp : SDiffActionHyp`, `h_density : TetherIntegralPreserved`,
`hω : IsCoadjointMotion`, `h_proj`, `h_dens`
(projection-factorization ⇒ density), `h_weight`, `h_sat`, `h_nondeg`,
`hRate : FrohmanianTetherRate`, `hClose : FrohmanianTetherClosingBound`, `hcrit` (BKM),
`huniq` (Kato uniqueness), `w` (Kato local witness). -/
theorem combined_conditional_capstone
    (SDiff : Type*) [Group SDiff] [MulAction SDiff CoadjointOrbit]
    (hyp : SDiffActionHyp SDiff)
    (h_density : TetherIntegralPreserved SDiff)
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
    -- (1) C1 and C3 for the tether (C2 is not proved)
    (InvariantUnderCoadjointAction SDiff TetherKernel ∧
      ProducesControllableNegativeFeedback TetherKernel) ∧
    -- (2) canonicity: B is the tether
    (∀ ω F G, B ω F G = TetherKernel ω F G) ∧
    -- (3) Casimirs conserved along the coadjoint motion
    (∀ f t, Casimir f (ωt t) = Casimir f (ωt 0)) ∧
    -- (4) analytic layer, conditional on hRate / hClose
    TetheredLyapunov.PhysicalVorticityCubicRate u₀ ν ∧
    (∃ (u : ℝ → VelocityField) (p : ℝ → PressureField),
      NS_PDE u p ν ∧ u 0 = u₀ ∧
      (∀ t ≥ (0 : ℝ), ContDiff ℝ (⊤ : ℕ∞) (u t)) ∧
      (∀ t ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u t)) ≥ 0) ∧
      (∀ t ≥ (0 : ℝ), ∀ x, div (u t) x = 0)) := by
  refine ⟨⟨tetherKernel_C1_of_casimir SDiff hyp h_density, tetherKernel_C3'⟩,
    uniqueness_of_minimal_tether_core B h_sym h_proj h_dens h_weight h_sat h_nondeg,
    fun f t => PlanSteps.casimir_conserved hyp ωt hω f t,
    TetheredLyapunov.physicalVorticityCubicRate_of_tetherRate h_pos_ν hRate, ?_⟩
  exact ClosureBlueprint.conditional_regularity_of_open_hyps u₀ ν h_divfree h_smooth h_finite_energy h_pos_ν
    w (hClose u₀ h_divfree h_smooth h_finite_energy) hcrit huniq

end Combined

end

#print axioms Combined.tetherKernel_C1_of_casimir
#print axioms Combined.tetherKernel_C1_of_volumePreserving
#print axioms Combined.tetherKernel_C3'
#print axioms Combined.left_H_zero_of_C2_symm
#print axioms Combined.tetherKernel_left_H_zero
#print axioms Combined.combined_conditional_capstone
