/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import FrohmanianTether
import FrohmanianTether.Pillars

/-!
# scripts.PrintGapsLedgerAxioms

`#print axioms` for every `frohmanian-tether-sdiff` declaration cited in the gaps-ledger note
(new version of Zenodo 10.5281/zenodo.22835069). Run by `scripts/verify.sh`; the output is
kept in `certificates/gaps-ledger-axioms.txt`.

The named open hypotheses (`PeriodicTetherClosingBound`, `FrohmanianTetherRateSmooth`,
`R3BKMContinuation`, ...) are `Prop`-valued definitions passed as explicit binders. They are
printed here only to show that defining them uses no axiom; printing them proves nothing about
Navier–Stokes solutions. They remain open.
-/

-- named open hypotheses (definitions, not theorems)
#print axioms FrohmanianTether.ClayStatements.PeriodicTetherClosingBound
#print axioms FrohmanianTether.TetherImpliesBKM.PeriodicTetherBound
#print axioms FrohmanianTether.FrohmanianTetherBound
#print axioms FrohmanianTether.FrohmanianTetherRate
#print axioms FrohmanianTether.ClayStatements.FrohmanianTetherClosingBound
#print axioms FeffermanClayA.FrohmanianTetherRateSmooth
#print axioms FeffermanClayA.R3BKMContinuationAt
#print axioms FeffermanClayA.R3BKMContinuation
#print axioms FeffermanClayA.Clay_A_Fefferman
-- proved: periodic BKM continuation, uniqueness, and the conditional implications
#print axioms FrohmanianTether.Pillars.periodicBKMContinuation_of_classical
#print axioms FrohmanianTether.Pillars.clay_B_exact_of_periodic_tether_closing_bound
#print axioms FrohmanianTether.Pillars.clay_B_exact_unique_of_periodic_tether_closing_bound
#print axioms FrohmanianTether.Pillars.periodicSmoothSolution_unique
#print axioms FrohmanianTether.Pillars.clay_B_exact_unique_iff
#print axioms FrohmanianTether.ClayStatements.clay_B_exact_of_periodic_tether_bound
#print axioms FrohmanianTether.ClayStatements.frohmanian_conditional_regularity_of_closing_bound
#print axioms ConditionalRegularity.conditional_regularity_of_open_hyps
#print axioms FeffermanClayA.ceiling_of_rate
#print axioms FeffermanClayA.clay_A_fefferman_of_frohmanianTetherRateSmooth
-- zero-datum instances and the set-aside global form
#print axioms FeffermanClayA.frohmanianTetherRateSmooth_zero
#print axioms FeffermanClayA.r3BKMContinuationAt_zero
#print axioms FeffermanClayA.frohmanianTetherRateSmoothGlobal_of_no_global_solution
-- refutations
#print axioms TetherRateCounterexample.not_forall_frohmanianTetherRate
#print axioms TetherRateCounterexample.not_frohmanianTetherRate_U
#print axioms TetherRateCounterexample.not_frohmanianTetherBound_U
#print axioms FrohmanianTether.TetherDefinitionAudit.not_forall_localTetherRateV014
-- classical sub-pieces of the gaps that are formalized (the open estimates are not)
-- T3: sup-norm bound for a transported scalar along characteristics (repository `T3` is ℝ³)
#print axioms NavierStokes3D.transported_scalar_maximum_principle
-- T5: scalar ODE comparison for the clipped cubic majorant
#print axioms TetheredLyapunov.comparison_ode_exists
#print axioms TetheredLyapunov.uniform_majorant_bound
-- T7: pointwise cyclic Jacobi identity of the KKS pairing
#print axioms Symplectori.SymplecticConstraint.kksPointwise_cyclic_jacobi_identity
-- T8: an antisymmetric (Poisson) correction vanishes on the diagonal
#print axioms FrohmanianTether.antisymmetric_correction_diagonal_zero
