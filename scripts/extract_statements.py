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
 ("KineticEnergyDerivIsVelocity","PlanSteps","KineticEnergyDerivIsVelocity"),
 ("tetherKernel_degenerates_on_kinetic_energy","SymplecticTether","tetherKernel_degenerates_on_kinetic_energy"),
 ("tetherKernel_C2_of_KEDeriv","Combined","tetherKernel_C2_of_KEDeriv"),
 ("tetherKernel_C3","SymplecticTether","tetherKernel_C3"),
 ("tetherKernel_comm","SymplecticTether","tetherKernel_comm"),
 ("TetherIntegralPreserved","SymplecticTether","TetherIntegralPreserved"),
 ("tether_coadjoint_invariance","SymplecticTether","tether_coadjoint_invariance"),
 ("left_H_zero_of_C2_symm","Combined","left_H_zero_of_C2_symm"),
 ("tetherKernel_left_H_zero","Combined","tetherKernel_left_H_zero"),
 ("classicalBracket_antisymm","ArnoldGeometric","classicalBracket_antisymm"),
 ("SaturatesTetherQuadratic","Uniqueness","SaturatesTetherQuadratic"),
 ("Polarizes","Uniqueness","Polarizes"),
 ("HasTetherKernelDensity","Uniqueness","HasTetherKernelDensity"),
 ("FactorsThroughProjection","Uniqueness","FactorsThroughProjection"),
 ("uniqueness_of_minimal_tether","Uniqueness","uniqueness_of_minimal_tether"),
 ("uniqueness_of_minimal_tether_core","Uniqueness","uniqueness_of_minimal_tether_core"),
 ("tethered_jacobi_identity","SymplecticTether","tethered_jacobi_identity"),
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
 ("combined_conditional_capstone","Combined","combined_conditional_capstone"),
 ("conditional_regularity_nonvacuous_at_zero","ClayStatements","conditional_regularity_nonvacuous_at_zero"),
 ("stepField_not_physical","ClayStatements","stepField_not_physical"),
 ("Clay_B_exact","ClayStatements","Clay_B_exact"),
 ("PeriodicTetherClosingBound","ClayStatements","PeriodicTetherClosingBound"),
 ("PeriodicBKMContinuation","ClayStatements","PeriodicBKMContinuation"),
 ("clay_B_exact_of_periodic_tether_bound","ClayStatements","clay_B_exact_of_periodic_tether_bound"),
 ("tethered_stretching_of_weight","SymplecticTether","tethered_stretching_of_weight"),
 ("reduced_pairing_of_unmodified_and_tether","SymplecticTether","reduced_pairing_of_unmodified_and_tether"),
 ("tether_bound_not_scale_invariant","PlanSteps","tether_bound_not_scale_invariant"),
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
for key, f, name in ITEMS:
    path = f'FrohmanianTether/{f}.lean'
    L = open(path).read().split('\n')
    hits = [(i, m.group(1)) for i, l in enumerate(L) for m in [re.match(KW, l)] if m and m.group(2) == name]
    assert len(hits) == 1, (key, path, hits)
    i, k = hits[0]
    with open(f'manuscript/lean/{key}.lean', 'w') as o:
        o.write(f'-- {path}, line {i+1}\n' + grab(L, i, k) + '\n')
print(f'wrote {len(ITEMS)} statements to manuscript/lean/')
