#!/usr/bin/env python3
"""Copy the exact Lean statements quoted in the paper into manuscript/lean/<key>.lean.

Statements are copied verbatim from the Lean sources (proof bodies replaced by `...`), so the
paper's appendix cannot drift from the checked code. Run from the repository root."""
import os, re
KW = r'^(?:@\[[^\]]*\]\s*)?(?:public\s+|private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|structure|abbrev)\s+(\S+)'
ITEMS = [  # key, file (under FrohmanianTether/), declaration name as written in the source
 ("IsPhysicalNSSolution","NS_Equations","IsPhysicalNSSolution"),
 ("navier_stokes_eq","NS_Equations","navier_stokes_eq"),
 ("KatoLocalWitness","NS_Equations","KatoLocalWitness"),
 ("CoadjointOrbit","ArnoldGeometric","CoadjointOrbit"),
 ("FunctionalDerivative","ArnoldGeometric","FunctionalDerivative"),
 ("KineticEnergyHamiltonian","ArnoldGeometric","KineticEnergyHamiltonian"),
 ("SDiffActionHyp","ArnoldGeometric","SDiffActionHyp"),
 ("Pi_u","ForMathlib/Projection","Pi_u"),
 ("TetherKernel","SymplecticTether","TetherKernel"),
 ("TetheredBracket","SymplecticTether","TetheredBracket"),
 ("C1","SymplecticTether","InvariantUnderCoadjointAction"),
 ("C2","SymplecticTether","DegenerateWRTKineticEnergy"),
 ("C3","SymplecticTether","ProducesControllableNegativeFeedback"),
 ("tetherKernel_C2_of_no_gateaux","SymplecticTether","tetherKernel_C2_of_no_gateaux"),
 ("not_forall_functionalDerivative_kineticEnergy_eq_velocity","KineticEnergyDerivative","not_forall_functionalDerivative_kineticEnergy_eq_velocity"),
 ("not_unique_isGateauxRepresentative","KineticEnergyDerivative","not_unique_isGateauxRepresentative"),
 ("not_unique_velocity_representative","KineticEnergyDerivative","not_unique_velocity_representative"),
 ("isVelocityGateauxRepresentative_kineticEnergy_at","ArnoldGeometric","isVelocityGateauxRepresentative_kineticEnergy_at"),
 ("tetherKernel_C3","SymplecticTether","tetherKernel_C3"),
 ("tetherKernel_comm","SymplecticTether","tetherKernel_comm"),
 ("left_H_zero_of_C2_symm","Combined","left_H_zero_of_C2_symm"),
 ("tetherKernel_left_H_zero","Combined","tetherKernel_left_H_zero"),
 ("classicalBracket_antisymm","ArnoldGeometric","classicalBracket_antisymm"),
 ("SaturatesTetherQuadratic","Uniqueness","SaturatesTetherQuadratic"),
 ("Polarizes","Uniqueness","Polarizes"),
 ("HasTetherKernelDensity","Uniqueness","HasTetherKernelDensity"),
 ("FactorsThroughProjection","Uniqueness","FactorsThroughProjection"),
 ("uniqueness_of_minimal_tether","Uniqueness","uniqueness_of_minimal_tether"),
 ("uniqueness_of_minimal_tether_core","Uniqueness","uniqueness_of_minimal_tether_core"),
 ("casimir_invariant_concrete","ConcreteSDiff","casimir_invariant"),
 ("IsCoadjointMotion","PlanSteps","IsCoadjointMotion"),
 ("casimir_conserved","PlanSteps","casimir_conserved"),
 ("comparison_ode_stability","AnalyticPipeline","comparison_ode_stability"),
 ("riccati_ceiling_of_vorticity_di","TetheredLyapunov","riccati_ceiling_of_vorticity_di"),
 ("FrohmanianTetherBound","SymplecticTether","FrohmanianTetherBound"),
 ("FrohmanianTetherRate","SymplecticTether","FrohmanianTetherRate"),
 ("FrohmanianTetherClosingBound","ClayStatements","FrohmanianTetherClosingBound"),
 ("PhysicalBKMContinuationCriterionFor","TetheredLyapunov","PhysicalBKMContinuationCriterionFor"),
 ("BKMContinuationCriterion","NS_Equations","BKMContinuationCriterion"),
 ("KatoUniquenessOnExistenceTimes","TetheredLyapunov","KatoUniquenessOnExistenceTimes"),
 ("conditional_regularity_of_open_hyps_blueprint","ClosureBlueprint","conditional_regularity_of_open_hyps"),
 ("conditional_regularity_of_open_hyps_main","ConditionalRegularity","conditional_regularity_of_open_hyps"),
 ("frohmanian_tether_theorem","ConditionalRegularity","frohmanian_tether_theorem"),
 ("conditional_regularity_nonvacuous_at_zero","ClayStatements","conditional_regularity_nonvacuous_at_zero"),
 ("stepField_not_physical","ClayStatements","stepField_not_physical"),
 ("Clay_B_exact","ClayStatements","Clay_B_exact"),
 ("PeriodicTetherClosingBound","ClayStatements","PeriodicTetherClosingBound"),
 ("PeriodicBKMContinuation","ClayStatements","PeriodicBKMContinuation"),
 ("clay_B_exact_of_periodic_tether_bound","ClayStatements","clay_B_exact_of_periodic_tether_bound"),
 ("tether_bound_not_scale_invariant","PlanSteps","tether_bound_not_scale_invariant"),
 ("IsPhysicalNSSolution","NS_Equations","IsPhysicalNSSolution"),
 ("exists_physical_time_deriv_ne_zero","PhysicalSolutionSanity","exists_physical_time_deriv_ne_zero"),
 ("not_forall_physical_time_deriv_zero","PhysicalSolutionSanity","not_forall_physical_time_deriv_zero"),
 ("SDiffActionHyp","ArnoldGeometric","SDiffActionHyp"),
 ("sdiffActionHyp","ConcreteSDiff","sdiffActionHyp"),
 ("not_transitive_on_casimir_levels","ConcreteSDiff","not_transitive_on_casimir_levels"),
 ("not_forall_strain_le_sup_vorticity","StrainBoundRefutation","not_forall_strain_le_sup_vorticity"),
 ("antisymmetric_clause_forces_zero","Uniqueness","antisymmetric_clause_forces_zero"),
 ("polarizes_tetherKernel_zero_of_not_differentiable","Uniqueness","polarizes_tetherKernel_zero_of_not_differentiable"),
 ("functionalDerivative_indep_of_not_differentiable","ArnoldGeometric","functionalDerivative_indep_of_not_differentiable"),
 ("IsFunctionalGradient","ArnoldGeometric","IsFunctionalGradient"),
 ("IsTestDirection","ArnoldGeometric","IsTestDirection"),
 ("DivFreeL2","ArnoldGeometric","DivFreeL2"),
 ("isFunctionalGradient_unique","ArnoldGeometric","isFunctionalGradient_unique"),
 ("tetherKernel_nondegenerate","TetherNondegeneracy","tetherKernel_nondegenerate"),
 ("not_tetherKernel_polarizes","TetherNondegeneracy","not_tetherKernel_polarizes"),
 ("not_forall_functionalDerivative_sub","TetherNondegeneracy","not_forall_functionalDerivative_sub"),
 ("PolarizesOnDifferentiable","Uniqueness","PolarizesOnDifferentiable"),
 ("tetherKernel_polarizesOnDifferentiable","Uniqueness","tetherKernel_polarizesOnDifferentiable"),
 ("not_step1Hyp","Uniqueness","not_step1Hyp"),
 ("not_pointwiseEnstrophyWeight_of_density","Uniqueness","not_pointwiseEnstrophyWeight_of_density"),
 ("AEEnstrophyWeightUnrestricted","Uniqueness","AEEnstrophyWeightUnrestricted"),
 ("AEEnstrophyWeight","Uniqueness","AEEnstrophyWeight"),
 ("not_aeEnstrophyWeightUnrestricted_tetherKernel","TetherWeight","not_aeEnstrophyWeightUnrestricted_tetherKernel"),
 ("not_aeEnstrophyWeightUnrestricted_of_eq_tether","TetherWeight","not_aeEnstrophyWeightUnrestricted_of_eq_tether"),
 ("integral_indicator_vitaliSet_mul","TetherWeight","integral_indicator_vitaliSet_mul"),
 ("tetherKernel_has_locallyIntegrable_density","TetherWeight","tetherKernel_has_locallyIntegrable_density"),
 ("translate","TetherC1","translate"),
 ("not_tetherKernel_invariant_concrete","TetherC1","not_tetherKernel_invariant_concrete"),
 ("tetherKernel_kernel_conditions","Uniqueness","tetherKernel_kernel_conditions"),
 ("NS_PDE_On","NS_Equations","NS_PDE_On"),
 ("IsPhysicalNSSolutionOn","NS_Equations","IsPhysicalNSSolutionOn"),
 ("IsLocalPhysicalSolution","NS_Equations","IsLocalPhysicalSolution"),
 ("LocalTetherBound","TetheredLyapunov","LocalTetherBound"),
 ("LocalFiniteTimeVorticityBound","TetheredLyapunov","LocalFiniteTimeVorticityBound"),
 ("BKMGlobalContinuation","TetheredLyapunov","BKMGlobalContinuation"),
 ("SmoothPhysicalUniqueness","TetheredLyapunov","SmoothPhysicalUniqueness"),
 ("conditional_regularity","TetheredLyapunov","conditional_regularity"),
 ("LocalTetherClosingBound","ClayStatements","LocalTetherClosingBound"),
 ("LocalTetherRate","TetheredLyapunov","LocalTetherRate"),
 ("comparison_ode_stability_Icc","TetheredLyapunov","comparison_ode_stability_Icc"),
 ("curlVal","TestFieldFamily","curlVal"),
 ("div_curlVal","TestFieldFamily","div_curlVal"),
 ("curlOrbit_test","TestFieldFamily","curlOrbit_test"),
 ("concField","TestFieldFamily","concField"),
 ("concField_test","TestFieldFamily","concField_test"),
 ("tsupport_concField_subset","TestFieldFamily","tsupport_concField_subset"),
 ("concField_ne_zero","TestFieldFamily","concField_ne_zero"),
 ("projCoef","TetherWeightProof","projCoef"),
 ("integral_beta_eq_zero","TetherWeightProof","integral_beta_eq_zero"),
 ("good_of_two_correctors","TetherWeightProof","good_of_two_correctors"),
 ("bad_finite","TetherWeightProof","bad_finite"),
 ("pointwise_identity","TetherWeightProof","pointwise_identity"),
 ("ae_zero_on_good_ball","TetherWeightProof","ae_zero_on_good_ball"),
 ("tetherKernel_aeEnstrophyWeight","TetherWeightProof","tetherKernel_aeEnstrophyWeight"),
 ("aeEnstrophyWeight_nontrivial","TetherWeightProof","aeEnstrophyWeight_nontrivial"),
 ("tetherKernel_core_inputs","TetherWeightProof","tetherKernel_core_inputs"),
 ("C1transported","TetherEquivariantC1","InvariantUnderTransportedCoadjointAction"),
 ("transSubgroup","TetherEquivariantC1","transSubgroup"),
 ("translate_smul_val","TetherEquivariantC1","translate_smul_val"),
 ("l2Translate","TetherEquivariantC1","l2Translate"),
 ("l2Translate_mem_divFreeL2","TetherEquivariantC1","l2Translate_mem_divFreeL2"),
 ("isFunctionalGradient_translate","TetherEquivariantC1","isFunctionalGradient_translate"),
 ("functionalDerivative_translate","TetherEquivariantC1","functionalDerivative_translate"),
 ("biotSavart_translate","TetherEquivariantC1","biotSavart_translate"),
 ("tI_translate","TetherEquivariantC1","tI_translate"),
 ("tetherKernel_translate","TetherEquivariantC1","tetherKernel_translate"),
 ("tetherKernel_transported_invariant","TetherEquivariantC1","tetherKernel_transported_invariant"),
 ("not_tetherKernel_invariant_transSubgroup","TetherEquivariantC1","not_tetherKernel_invariant_transSubgroup"),
 ("not_transported_invariant_pointEval","TetherEquivariantC1","not_transported_invariant_pointEval"),
]
def grab(L, i, k):
    out = []; j = i
    while j < len(L):
        l = L[j]; out.append(l)
        if k in ('theorem', 'lemma'):
            if ':=' in l:
                out[-1] = l[:l.index(':=')].rstrip() + ' := ...'; break
        elif j + 1 >= len(L) or L[j+1].strip() == '' or re.match(KW, L[j+1]) or L[j+1].lstrip().startswith(('/--', '/-!', 'theorem', 'lemma', '#')):
            break
        j += 1
    return '\n'.join(out)
os.makedirs('manuscript/lean', exist_ok=True)
for _f in os.listdir('manuscript/lean'):
    if _f.endswith('.lean'):
        os.remove(os.path.join('manuscript/lean', _f))
for key, f, name in ITEMS:
    path = f'FrohmanianTether/{f}.lean'
    L = open(path).read().split('\n')
    hits = [(i, m.group(1)) for i, l in enumerate(L) for m in [re.match(KW, l)] if m and m.group(2) == name]
    assert len(hits) == 1, (key, path, hits)
    i, k = hits[0]
    with open(f'manuscript/lean/{key}.lean', 'w') as o:
        o.write(f'-- {path}, line {i+1}\n' + grab(L, i, k) + '\n')
print(f'wrote {len(ITEMS)} statements to manuscript/lean/')
