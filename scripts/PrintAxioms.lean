import FrohmanianTether

/-! `#print axioms` for the headline statements (run by `scripts/verify.sh`). The strict
repository-wide audit of every declaration is `scripts/AxiomAudit.lean`. -/

-- conditional regularity (analytic layer and periodic Clay statement)
#print axioms ConditionalRegularity.frohmanian_tether_theorem
#print axioms TetheredLyapunov.conditional_regularity
#print axioms FrohmanianTether.ClayStatements.frohmanian_conditional_regularity_of_closing_bound
#print axioms FrohmanianTether.ClayStatements.conditional_regularity_nonvacuous_at_zero
-- tether, (C1)-(C3), obstruction, canonicity
#print axioms FrohmanianTether.tetherKernel_C3
#print axioms FrohmanianTether.pairsToZero_of_C2
#print axioms FrohmanianTether.uniqueness_of_minimal_tether
#print axioms FrohmanianTether.uniqueness_of_minimal_symmetric_tether
#print axioms FrohmanianTether.uniqueness_of_minimal_tether_core
#print axioms TetherNondegeneracy.tetherKernel_nondegenerate
-- weight hypothesis
#print axioms TetherWeight.not_aeEnstrophyWeightUnrestricted_tetherKernel
#print axioms TetherWeightProof.tetherKernel_aeEnstrophyWeight
#print axioms TetherWeightProof.tetherKernel_core_inputs
-- C1: fixed-functional (refuted) and transported (proved for translations)
#print axioms FrohmanianTether.not_tetherKernel_invariant_concrete
#print axioms FrohmanianTether.not_tetherKernel_invariant_transSubgroup
#print axioms FrohmanianTether.tetherKernel_transported_invariant
#print axioms FrohmanianTether.not_transported_invariant_pointEval
-- explicit exact NS solutions (shear, ABC) and the periodic/finite-energy obstruction
#print axioms ExplicitFlows.shearFlow_navier_stokes
#print axioms ExplicitFlows.abcFlow_navier_stokes
#print axioms ExplicitFlows.shearFlow_isPeriodicSmoothSolution
#print axioms ExplicitFlows.abcFlow_isPeriodicSmoothSolution
#print axioms ExplicitFlows.curl_abcProfile
#print axioms ExplicitFlows.not_integrable_sq_of_periodic
#print axioms ExplicitFlows.isEmpty_katoLocalWitness_of_periodic
-- 0.1.5: main theorem, tether ⇒ BKM integrability, definition audit (0.1.4 defects)
#print axioms FrohmanianTether.ClayStatements.clay_B_exact_of_periodic_tether_bound
#print axioms FrohmanianTether.TetherDefinitionAudit.localTetherBoundV014_constraint_free_of_unbounded
#print axioms FrohmanianTether.TetherDefinitionAudit.exists_isLocalPhysicalSolution_zero_time
#print axioms FrohmanianTether.TetherDefinitionAudit.isLocalPhysicalSolution_escapePath
#print axioms FrohmanianTether.TetherDefinitionAudit.not_localTetherRateV014_zero
#print axioms FrohmanianTether.TetherDefinitionAudit.not_forall_localTetherRateV014
#print axioms TetheredLyapunov.comparison_ode_stability_Icc_right
#print axioms TetheredLyapunov.localTetherBound_of_localTetherRate
#print axioms FrohmanianTether.ClayStatements.localTetherRate_zero
#print axioms FrohmanianTether.ClayStatements.localTetherBound_zero
#print axioms FrohmanianTether.TetherImpliesBKM.periodicBKMIntegrability_of_periodicTetherBound
#print axioms FrohmanianTether.TetherImpliesBKM.periodicBKMIntegrability_of_periodicTetherClosingBound
