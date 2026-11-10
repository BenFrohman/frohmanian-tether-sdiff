# Verification certificate

**Paper:** *The Frohmanian Tether on SDiff(𝕋³): A Metriplectic Correction, Its Canonicity, and an Obstruction to Damping — Conditional statements verified in Lean 4*, version 0.1.2 (preprint, work in progress; not yet archived on Zenodo)
**Author:** Benjamin Stanley Frohman (Independent Researcher, Texas, United States; frohmanbenjamin@gmail.com, ORCID 0009-0006-7068-3718)
**PDF:** `manuscript/main.pdf` (source `manuscript/main.tex`)

**The results are conditional.** Every theorem about Navier–Stokes solutions and the canonicity
theorems are implications from hypotheses that are not proved; the complete list by Lean name is in
"Conditional content" below. Nothing here proves global regularity of the 3D Navier–Stokes equations.

| Item | Value |
|---|---|
| Verified commit | `09d14b6a0c2ca7ff673a52ed2716c675d7268379` (Lean sources; later commits change only documentation, manuscript and metadata) |
| Lean toolchain | `leanprover/lean4:v4.30.0-rc1` (pinned in `lean-toolchain`) |
| Mathlib | `v4.30.0-rc1`, rev `0c154d67103f74be3a0f2c509f72ccbf5be9f2a7` (pinned in `lake-manifest.json`) |
| One-command verification | `bash scripts/verify.sh` (or `make verify`) from a fresh clone |
| Build | `lake build`: 2794 jobs, success |
| CI run, Lean certificate (build + source scan + strict axiom audit + `scripts/verify.sh`) | passed: https://github.com/BenFrohman/frohmanian-tether-sdiff/actions/runs/42783533141 |
| CI run, Lean 4 (lean-action build) | passed (workflow_dispatch on the branch, verified commit): https://github.com/BenFrohman/frohmanian-tether-sdiff/actions/runs/42784032747 |
| CI runs on the documentation tip `12d731e` | Lean certificate https://github.com/BenFrohman/frohmanian-tether-sdiff/actions/runs/42784258241, Lean 4 https://github.com/BenFrohman/frohmanian-tether-sdiff/actions/runs/42784309658 (both passed) |
| Zenodo archive | none for 0.1.2 yet (`.zenodo.json` prepared). The v0.1.1 archive [`10.5281/zenodo.24082000`](https://doi.org/10.5281/zenodo.24082000) still contains the removed hypothesis. |
| Modules | 32 (`FrohmanianTether` and 31 submodules) |
| Declarations audited | 968 |
| Theorem constants audited | 673 (600 stated in the sources, 73 auto-generated equation/congruence/injectivity lemmas) |
| Axioms used | only `propext`, `Classical.choice`, `Quot.sound` (some declarations use a subset) |
| `sorry` / `admit` / `native_decide` | none (`python3 scripts/check_no_sorry.py`: `OK: no sorry/admit/native_decide, no axiom declarations`) |
| `axiom` declarations | none |

## Reproduction

```
git clone https://github.com/BenFrohman/frohmanian-tether-sdiff
cd frohmanian-tether-sdiff
bash scripts/verify.sh        # or: make verify
```

`scripts/verify.sh` installs `elan` if missing (toolchain from `lean-toolchain`), runs
`lake exe cache get` (Mathlib cache for the rev in `lake-manifest.json`), `lake build`,
`python3 scripts/check_no_sorry.py`, `lake env lean scripts/AxiomAudit.lean` (strict audit) and
`lake env lean scripts/PrintAxioms.lean` (`#print axioms` for the headline theorems), and prints
`VERIFY OK`. It exits non-zero on any failure. The Lean certificate workflow runs it in CI.

### `#print axioms` for the headline theorems (`scripts/PrintAxioms.lean`)

```
'ConditionalRegularity.frohmanian_tether_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.conditional_regularity' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.ClayStatements.frohmanian_conditional_regularity_of_closing_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.ClayStatements.conditional_regularity_nonvacuous_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.tetherKernel_C3' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.pairsToZero_of_C2' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.uniqueness_of_minimal_tether' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.uniqueness_of_minimal_symmetric_tether' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.uniqueness_of_minimal_tether_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.tetherKernel_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeight.not_aeEnstrophyWeightUnrestricted_tetherKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.tetherKernel_aeEnstrophyWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.tetherKernel_core_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.not_tetherKernel_invariant_concrete' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.not_tetherKernel_invariant_transSubgroup' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.tetherKernel_transported_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.not_transported_invariant_pointEval' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Changes in 0.1.2, fifth pass (weight condition proved; transported C1; reproducibility)

- **Concentrated divergence-free test fields** (new module `TestFieldFamily`). `curlVal H =
  curl(H e₂) = (∂₁H, -∂₀H, 0)`, with `∂ᵢH(y) = fderiv ℝ H y (EuclideanSpace.single i 1)` (`pd`).
  For smooth compactly supported `H` it is smooth, compactly supported in `tsupport H`, and
  divergence-free (`div_curlVal`, symmetry of second derivatives via Mathlib
  `ContDiffAt.isSymmSndFDerivAt`), so it is a test direction (`curlOrbit_test`). `concField x hr`
  uses a Mathlib `ContDiffBump` at `x`: a test field with support in `B(x, r)`
  (`tsupport_concField_subset`), not identically zero (`concField_ne_zero`), for every `x` and `r > 0`.
- **`AEEnstrophyWeight TetherKernel` proved** (new module `TetherWeightProof`,
  `tetherKernel_aeEnstrophyWeight`, with `c = κ`).
  - `projCoef ω v` is the Gram–Schmidt coefficient of `Π_u`; it is additive on test fields
    (`projCoef_add_smul`).
  - For test fields with zero coefficient, `∫ (α ω + κ‖ω‖²) ⟨a, b⟩ = 0` (`integral_beta_eq_zero`);
    products are integrable (Mathlib `LocallyIntegrable.integrable_smul_right_of_hasCompactSupport`).
  - Orthogonality to `u` is obtained with correctors, not by building orthogonal fields:
    subtracting multiples of two test fields with nonzero coefficient, supported away from `a, b`,
    makes `a, b` orthogonal to `u` without changing `⟨a, b⟩` (`good_of_two_correctors`); at most
    two points are bad (`bad_finite`).
  - On a good ball, `g = ⟨curl(x₀g e₂), curl(x₀χ e₂)⟩ − ⟨curl(g e₂), curl(x₀²χ/2 e₂)⟩`
    (`pointwise_identity`), so `β` integrates to `0` against every smooth compactly supported `g`,
    and Mathlib's `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` gives `β = 0` a.e.
    (`ae_zero_on_good_ball`); a countable subcover (`TopologicalSpace.isOpen_iUnion_countable`)
    finishes.
  - Sanity: `aeEnstrophyWeight_nontrivial` (hypotheses satisfiable, weight nonzero at `rotOrbit 0`).
  - Discharge: `tetherKernel_core_inputs` (density, weight and saturation inputs of
    `uniqueness_of_minimal_tether_core` hold for `B = TetherKernel`). The weight hypothesis
    remains a hypothesis for a general competitor `B`, where it defines the kernel class.
- **Transported (equivariant) C1** (new module `TetherEquivariantC1`).
  - `InvariantUnderTransportedCoadjointAction S B : ∀ g F G ω, B (g • ω) (F ∘ (g⁻¹ • ·)) (G ∘ (g⁻¹ • ·)) = B ω F G`.
  - `ConcreteSDiff.transSubgroup`: the translations, a subgroup of the concrete group;
    `translate_smul_val`: `(τ_h • ω)(x) = ω(x − h)`.
  - **Proved:** `tetherKernel_transported_invariant` (all translations). Ingredients:
    `l2Translate` (Mathlib `Lp.compMeasurePreservingₗᵢ`) preserves `DivFreeL2`
    (`l2Translate_mem_divFreeL2`); gradient transport (`isFunctionalGradient_translate`,
    `functionalDerivative_translate`); Biot–Savart commutes with translations
    (`biotSavart_translate`); the projected pairing is transported (`tI_translate`); enstrophy is
    invariant.
  - Sanity: `not_transported_invariant_pointEval` (the predicate is not vacuous);
    `not_tetherKernel_invariant_transSubgroup` (the fixed-functional C1 fails on the same subgroup,
    via the generic `not_tetherKernel_invariant_of_shift`).
  - Open: rotations and general volume-preserving diffeomorphisms (the concrete group acts by scalar
    composition, the correct transport only for translations; the geometric push-forward
    `(Dφ ω) ∘ φ⁻¹` is not formalized).
- **Mathlib agreement** (new module `MathlibAgreement`): `rfl` lemmas identifying
  `NavierStokes3D.volume`, `pairing`, `eb`, `pd`, `NavierStokes3D.div`, `cross`, `translate`,
  `l2Translate`, `Enstrophy` with the Mathlib declarations they abbreviate. Remaining duplicates
  (not refactored): `NavierStokes3D.div` (trace of `fderiv`), `Pi_u` (vs
  `Submodule.orthogonalProjection`), `IsZ3Periodic` (vs `Function.Periodic`).
- **Reproducibility:** `scripts/verify.sh`, `Makefile` (`make verify`), `scripts/PrintAxioms.lean`;
  CI runs `scripts/verify.sh`.

## Changes in 0.1.2, fourth pass (weight hypothesis and C1 for the tether)

- **Unrestricted a.e. weight hypothesis refuted** (new module `TetherWeight`). The former
  `AEEnstrophyWeight` (now `AEEnstrophyWeightUnrestricted`) quantified over every density `α`,
  measurable or not. `TetherWeight.not_aeEnstrophyWeightUnrestricted_tetherKernel` proves it false
  for `TetherKernel`:
  - `vitaliSet`: one representative in the unit ball of each class of `ℝ³ / ℚ e₀` meeting the
    ball. Every null-measurable subset of it is null (`vitaliSet_null_of_subset`; disjoint
    rational translates inside `ball 0 2`), and it is not null itself
    (`vitaliSet_measure_ne_zero`; its rational translates cover `ball 0 1`).
  - `integral_indicator_vitaliSet_mul`: `∫ 1_V · f = 0` for every `f` (either the integrand is not
    integrable, so the Bochner integral is `0`, or its support is a null-measurable subset of `V`).
  - At the regular vorticity `ω = 0`, `Enstrophy 0 = 0`, so `TetherKernel 0 F G = 0`; the density
    equal to `1_V` at `ω = 0` and canonical elsewhere is a density of the tether
    (`vitaliDensity_is_density`), but `1_V` is not `0` a.e.
  - `not_aeEnstrophyWeightUnrestricted_of_eq_tether`: every `B` equal to the tether fails it. So
    `uniqueness_of_minimal_tether_core` as previously stated (hypothesis
    `AEEnstrophyWeightUnrestricted B`, conclusion `B = TetherKernel`) had jointly unsatisfiable
    hypotheses.
- **Corrected statement.** `AEEnstrophyWeight B` now quantifies only over densities `α` with
  `α ω` locally integrable at every regular `ω`. The input `h_density` of `step3_scalar` and
  `uniqueness_of_minimal_tether_core` now asks for such a density; the tether has one (the
  constant canonical density, `canonicalTetherDensity_locallyIntegrable`,
  `TetherWeight.tetherKernel_has_locallyIntegrable_density`).
- **`AEEnstrophyWeight TetherKernel` (corrected form): open.** It would need, at each regular `ω`,
  that a locally integrable `β` with `∫ β ⟨Π_u a, Π_u b⟩ = 0` for all gradients `a, b` vanishes
  a.e. Missing in Lean: divergence-free test fields that are `L²`-orthogonal to the Biot–Savart
  velocity `u` and localize at every point (the projection adds the non-compactly supported term
  `λ(a) u`; the library has only the fixed-profile rotation fields `rotField`), a family of such
  fields rich enough for Lebesgue differentiation (Mathlib has `ae_tendsto_average`), and control
  of the Bochner convention when `β ⟨Π_u a, Π_u b⟩` is not integrable.
- **C1 for `TetherKernel` under the concrete action refuted** (new module `TetherC1`).
  `ConcreteSDiff.translate h` (`x ↦ x + h`) is an element of `ConcreteSDiff.G`
  (`good_addRight`). `not_tetherKernel_invariant_concrete` proves
  `¬ InvariantUnderCoadjointAction ConcreteSDiff.G TetherKernel`: for `g` the translation by `3e₀`,
  `g • rotOrbit 0 = rotOrbit (3e₀)`; for a rotation field `φ` with nonzero tether at `rotOrbit 0`
  (`tetherKernel_rot_nondegenerate`), the functional `F = |linFun φ · − linFun φ (g • ω)|` has no
  gradient at `g • ω` (tether `0`), while at `ω` it is smooth with gradient `±φ`
  (`absFun_gradient_pos`, `absFun_gradient_neg`), so its tether there equals that of `linFun φ`
  (`tetherKernel_absFun_eq`), which is nonzero. `InvariantUnderCoadjointAction` does not transport
  `F, G`; the equivariant form (`F, G` composed with the action) is not formalized and remains open.
  For translations it would reduce to translation-equivariance of Biot–Savart; for a general
  measure-preserving permutation acting by composition, Biot–Savart is not equivariant.
- **C2 for `TetherKernel`: open, unchanged** (needs `δH/δω`, the Leray part of the stream function;
  Biot–Savart is unbounded on `L²(ℝ³)`; expected to fail at regular `ω`).

## Changes in 0.1.2, third pass (genuine functional derivative; local Kato witness)

- **`FunctionalDerivative` rebuilt** (`ArnoldGeometric`). It used to be `Classical.choose` of a
  Gâteaux representative, which is never unique. Now:
  - `L2Field` is `Lp (EuclideanSpace ℝ (Fin 3)) 2 volume`.
  - Test directions (`IsTestDirection`) are `C^∞`, compactly supported and divergence-free.
  - `DivFreeL2` is the closure of the span of the test directions.
  - `IsFunctionalGradient F ω g` means: `g ∈ DivFreeL2`, `ω` is regular (every component is
    differentiable), and `d/dt|₀ F(ω + tε) = ⟪g, ε⟫_{L²}` for every test direction `ε`.
  - `isFunctionalGradient_unique` proves the gradient is unique, so
    `FunctionalDerivative F ω` is *the* gradient when one exists, and `0` otherwise
    (`functionalDerivative_eq`, `FunctionalDerivative_eq_zero_of_not`,
    `functionalDerivative_eq_zero_of_not_regular`). No arbitrary choice is involved.
  - `functionalDerivative_of_not_differentiable` now proves that the derivative is `0` at a
    non-regular vorticity. `functionalDerivative_indep_of_not_differentiable` still holds,
    because both sides are `0`.
- **Kernel conditions for `TetherKernel`** (new module `TetherNondegeneracy`; `Uniqueness`):

  | Condition | Status | Lean |
  |---|---|---|
  | `h_nondeg` (T not identically zero) | **proved** | `TetherNondegeneracy.tetherKernel_nondegenerate`, `tether_nondeg_witness` (rotation fields with disjoint supports at `0` and `3e₀`) |
  | `Polarizes TetherKernel` (all functionals) | **refuted** | `TetherNondegeneracy.not_tetherKernel_polarizes` (the kink functional `absFun` has no gradient) |
  | Polarization restricted to functionals with gradients | **proved** | `tetherKernel_polarizesOnDifferentiable` |
  | `SaturatesTetherQuadratic TetherKernel` | **proved** | `tetherKernel_kernel_conditions` |
  | `h_proj` for `TetherKernel` | **proved** | `tetherKernel_kernel_conditions` |
  | `h_density` for `TetherKernel` | **proved** (canonical density, locally integrable) | `tetherKernel_kernel_conditions`, `TetherWeight.tetherKernel_has_locallyIntegrable_density` |
  | `h_weight`, pointwise in `x` | **refuted** for every `B` that has a density (change the density on the null set `{0}`); so the former core theorem was vacuous | `not_pointwiseEnstrophyWeight_of_density`, `not_pointwiseEnstrophyWeight_tetherKernel` |
  | `h_weight`, a.e. form over all densities (`AEEnstrophyWeightUnrestricted`) | **refuted** for `TetherKernel` (Vitali-set density at `ω = 0`); so the core theorem stated with it was vacuous | `TetherWeight.not_aeEnstrophyWeightUnrestricted_tetherKernel`, `not_aeEnstrophyWeightUnrestricted_of_eq_tether` |
  | `h_weight`, a.e. form over locally integrable densities (`AEEnstrophyWeight`) for `TetherKernel` | **proved** (fifth pass) | `TetherWeightProof.tetherKernel_aeEnstrophyWeight` |
  | `Step1Hyp` (derivative of a difference) | **refuted** | `not_step1Hyp`, `TetherNondegeneracy.not_forall_functionalDerivative_sub` |
  | C2 for `TetherKernel` (`T(·, H) = 0`, `H` the kinetic energy) | **open** | proved only where `H` has no gradient (`tetherKernel_C2_of_no_gateaux`). The general case needs `δH/δω` (the Leray part of the stream function); Biot–Savart is unbounded on `L²(ℝ³)`. Not in Mathlib; the statement is expected to fail at regular ω. |
  | C1 for `TetherKernel` under the concrete action (`F, G` not transported) | **refuted** | `not_tetherKernel_invariant_concrete` (translation by `3e₀`) |
  | transported C1 (`F, G` transported), translations | **proved** (fifth pass) | `tetherKernel_transported_invariant` |
  | transported C1, rotations / diffeomorphisms | **open** | geometric push-forward action not formalized |
  | `Polarizes B`, `SaturatesTetherQuadratic B`, `h_proj B`, `h_density B`, `h_weight B` for a general `B` | hypotheses | they *define* the class of competitors `B`; they cannot be proved for all `B` |

  - `uniqueness_of_minimal_symmetric_tether` and `uniqueness_of_minimal_tether` now take
    `PolarizesOnDifferentiable B`, and conclude `B ω F G = TetherKernel ω F G` for functionals
    `F`, `G` that have gradients at ω.
  - `uniqueness_of_minimal_tether_core` takes `h_sym`, `h_proj`, `h_density` (a density locally
    integrable at regular `ω`), `h_weight : AEEnstrophyWeight B` (locally integrable densities,
    fourth pass) and `h_sat`. It no longer takes `h_nondeg`.
  - Deleted: `step1_locality_sym`, `step1_locality_route1`, `tetherKernel_polarizes`.
- **`KatoLocalWitness` restricted to its interval** (`NS_Equations`).
  - `pde : NS_PDE_On u p ν T` (the equations for `t ∈ [0, T]` only).
  - `phys : IsPhysicalNSSolutionOn u T`.
  - Smoothness was already required only on `[0, T]`.
  - New: `NS_PDE_On`, `IsPhysicalNSSolutionOn`, `IsLocalPhysicalSolution`, plus `.mono`/`.on` lemmas.
  - Existence times, `local_existence`, `mem_existenceTimes`,
    `Tstar_pos_of_exists_smooth_solution`, `uniqueness_of_existence_times_of_energy_gronwall` and
    `smoothness_below_Tstar_of_uniqueness` now use the local forms.
  - Deleted: `mem_existenceTimes_add_of_kato_restart`. Concatenating a restarted witness would
    need a separate gluing statement.
  - Deleted because they used the old global `w.pde`:
    `conditional_regularity_of_bkmIntegrability`, `conditional_regularity_scaffold`,
    `conditional_regularity_of_restart`, `conditional_regularity_of_bkm_uniqueness` and
    `conditional_regularity_of_kato_estimates`.
- **New explicit hypotheses forced by the local witness** (`TetheredLyapunov`):
  - `BKMGlobalContinuation u₀ ν`, category (b). It says: if a Kato witness exists and
    `LocalFiniteTimeVorticityBound u₀ ν` holds (for each `T₀` one `‖ω‖∞` ceiling for every smooth
    physical solution on `[0, T]`, `T ≤ T₀`), then a global smooth physical solution exists.
    This is the Kato local theorem combined with BKM continuation. Caveat: the classical theorem
    is stated for `H^s` data; the library uses `C^∞ ∩ L²` data on `ℝ³`.
  - `SmoothPhysicalUniqueness u₀ ν`, category (b). Two smooth local physical solutions with the
    same data agree on their common interval.
  - `LocalTetherBound u₀ ν`, category (d). One `‖ω‖∞` ceiling `Y` for every smooth physical
    solution on every finite interval.
  - `LocalTetherRate u₀ ν`, category (d). This is the cubic rate
    `M' ≤ C M² − κ'' M³`, `M = ‖ω‖∞`, with the constants fixed before the interval. It implies
    `LocalTetherBound` (`localTetherBound_of_localTetherRate`, proved through the new
    finite-interval comparison lemma `comparison_ode_stability_Icc`).
  - `ClayStatements.LocalTetherClosingBound ν`, category (d): `LocalTetherBound` for all smooth,
    divergence-free, finite-energy data.
- **New headline statements:**
  - `ConditionalRegularity.frohmanian_tether_theorem (hKato) (hcont : ∀ u₀ ν,
    BKMGlobalContinuation u₀ ν) (hDI : ∀ u₀ ν, LocalTetherRate u₀ ν)`.
  - `TetheredLyapunov.conditional_regularity u₀ ν w hcont (hRiccati : LocalTetherBound u₀ ν)`.
  - `ConditionalRegularity.conditional_regularity_of_open_hyps … w hcont hRiccati (huniq :
    SmoothPhysicalUniqueness)`.
  - `ClayStatements.frohmanian_conditional_regularity_of_closing_bound ν hν (hclose :
    LocalTetherClosingBound ν) hKato hcont huniq`.
  - `ClayStatements.repaired_huniq_at_zero` is now stated for `kato_witness_zero`.
    `conditional_regularity_nonvacuous_at_zero` is re-proved from `kato_witness_zero`,
    `smoothPhysicalUniqueness_zero`, `localTetherBound_zero` and `bkmGlobalContinuation_zero`.
- **Auxiliary predicates restricted to physical solutions.** `UniformVorticityCeiling`,
  `FiniteTimeVorticityBound`, `BKMIntegrability`, `BKMContinuationCriterionFor`,
  `SmoothBelowTstarFor` and `ClosureBlueprint.RiccatiMajorantExists` now carry an
  `IsPhysicalNSSolution u →` premise. `ClosureBlueprint.type_composition_sequence` now takes a
  given global physical solution.

## Changes in 0.1.2, second pass (false or vacuous hypotheses removed)

- **`IsPhysicalNSSolution` repaired.** The clause `∀ t ≤ 0, u t = u 0` forced `∂ₜu(0) = 0`, because
  `deriv` is two-sided. It was replaced by `∃ v₀, ∀ t ≤ 0, u t = u 0 + t • v₀`.
  - Sanity lemmas (new module `PhysicalSolutionSanity`): `exists_physical_time_deriv_ne_zero` and
    `not_forall_physical_time_deriv_zero`. The witness path is not a Navier–Stokes solution.
  - `isPhysicalNSSolution_zero` and `eq_zero_of_isPhysicalNSSolution_zero_all` were re-proved.
- **Removed `SDiffActionHyp.transitive_on_casimir_levels`** (false).
  - Refutation: `ConcreteSDiff.not_transitive_on_casimir_levels`.
  - Deleted with it: `orbit_eq_casimir_level`.
  - The remaining structure is proved for the concrete action: `ConcreteSDiff.sdiffActionHyp`, which
    replaces `sdiffActionHyp_of_transitive`.
- **Removed `TetherIntegralPreserved`** and the field `VolumePreservingCoadjointAction.tether_integrand_pullback`.
  - They cannot be proved or refuted, because they concern an unspecified `Classical.choose`.
  - Deleted with them: `tether_coadjoint_invariance`, `tether_satisfies_C1`, `tetherKernel_C1`,
    `tether_coadjoint_invariance_of_integral_eq`, `volumePreservingCoadjointAction_preserves_TetherKernel`,
    `Combined.tetherKernel_C1_of_casimir`, `Combined.tetherKernel_C1_of_volumePreserving` and
    `Combined.combined_conditional_capstone`.
  - C1 for `TetherKernel` is no longer proved under any hypothesis.
- **Removed `PointwiseStrainSupBound`** (`‖Du(x)‖ ≤ C‖ω‖∞`, false).
  - Refutation: `StrainBoundRefutation.not_forall_strain_le_sup_vorticity`, in a new module.
  - Deleted with it:
    - `strain_sup_le_of_CZ`, `convective_norm_le_of_CZ`, `stretching_inner_le`, `stretching_inner_le_at_max`,
      `stretching_quartic_le`, `stretching_pairing_le_at_spatial_max`,
      `stretching_enstrophy_di_at_spatial_max` and `restart_of_kato_quantitative`.
    - `PointwiseCZGradientBoundAtMax` and `unmodified_envelope_yields_classical_quadratic_rate`.
    - `ConjecturedSDiffPushforwardInvariance`, `ConjecturedUnmodifiedTetherPairing`,
      `reduced_pairing_of_unmodified_and_tether`, `tethered_h_slot_stretching_remains_cubic`,
      `tethered_stretching_of_weight` and `unmodified_pairing_and_c3_diagonal`.
    - `AssemblyGap.unmodified_max_pairing_is_classical_source`, `AssemblyGap.unmodified_max_rate_of_cubic_source`
      and `ClosureBlueprint.calderon_zygmund_stretching_bound`.
    - `enstrophy_di_of_spatial_max`, `lyapunov_density_unweighted_di_at_spatial_max` and
      `conditional_regularity_of_constructions`.
- **Removed the circular Jacobi lemma.** `tethered_jacobi_identity` took `hident`/`hvanish`, which
  together are its conclusion.
  - Also deleted: `ClosureBlueprint.tether_kernel_jacobi` and `jacobi_cyclic_sum_skeleton`.
  - No Jacobi identity is claimed.
- **Removed the antisymmetric uniqueness clause.** It is vacuous unless `T ≡ 0`, as proved by
  `antisymmetric_clause_forces_zero`.
  - Deleted: `uniqueness_of_minimal_tether_antisymmetric`, `step1_locality`, `step3_projection`,
    `step4_coefficient`, `ClosureBlueprint.IsAdmissibleCorrection` and `tether_kernel_uniqueness`.
  - Clause (1) of `frohmanian_tether_theorem` was dropped.
- **Removed `hTlb`** (uniform lower bound on Kato existence times), together with `hInt` and `huniq_shift`.
  - `hTlb` is not refuted: by scaling it has the strength of the open problem.
  - `ConditionalRegularity.frohmanian_tether_theorem` now takes `hKato`, `hDI`, `hcrit` and `huniq` and is
    proved through the comparison lemma and BKM continuation.
  - Also deleted: `ClayStatements.repaired_hInt` and `repaired_huniq_shift_at_zero`.
- **Added: degeneracy of the encoding.**
  - `ArnoldGeometric.functionalDerivative_indep_of_not_differentiable`.
  - `tetherKernel_indep_of_not_differentiable`.
  - `polarizes_tetherKernel_zero_of_not_differentiable`: `Polarizes TetherKernel` forces `T = 0` at
    every non-differentiable ω.
  - As a result, the kernel-class conditions (`Polarizes TetherKernel`, `h_proj`, `h_nondeg`: T not
    identically zero) cannot be proved from the definitions. They remain hypotheses.

## Changes from v0.1.1 (first pass)

- **Removed (false):** `PlanSteps.KineticEnergyDerivIsVelocity`
  (`∀ ω, FunctionalDerivative KineticEnergyHamiltonian ω = velocity_from_vorticity ω`). Its negation is
  proved: `KineticEnergyDerivative.not_forall_functionalDerivative_kineticEnergy_eq_velocity`
  (new module `FrohmanianTether/KineticEnergyDerivative.lean`, standard axioms only).
- **Deleted** because they assumed the hypothesis or its pointwise form:
  `Combined.tetherKernel_C2_of_KEDeriv`, `tetherKernel_degenerates_on_kinetic_energy`,
  `tetherKernel_C2_of_identifications`, `tethered_reproduces_classical_euler`,
  `degeneracy_for_mollified_sup_norm_proxy`.
- **Deleted** because their hypotheses can never hold (a Gâteaux representative is never unique,
  `KineticEnergyDerivative.not_unique_isGateauxRepresentative` and
  `not_unique_velocity_representative`): `ArnoldGeometric.functional_derivative_eq_velocity_of_unique_repr`,
  `functional_derivative_of_kinetic_energy_of_unique_repr`, `functional_derivative_of_kinetic_energy`.
- **Statements changed:** `ConditionalRegularity.frohmanian_tether_theorem` lost its first clause
  (bracket agreement on `H` under δH = u); `Combined.combined_conditional_capstone` lost the hypotheses
  `hδ`, `hdivω`, `hIntω` and the conclusions C2 and `T(H,M) = 0`.
- **Added:** unfolding lemmas `ArnoldGeometric.isGateauxRepresentative_iff`, `ArnoldGeometric.BiotSavart_apply`.
- No other Lean statement was changed.

## Checks

- `bash scripts/verify.sh` runs all of the following from a fresh clone and prints `VERIFY OK`.

- `lake build` succeeds with the pinned toolchain and Mathlib.
- `python3 scripts/check_no_sorry.py`: no `sorry`, `admit`, `native_decide` or `axiom` declaration
  in any tracked `.lean` file (comments and strings ignored).
- `lake env lean scripts/AxiomAudit.lean`: for every non-internal declaration in the
  `FrohmanianTether.*` modules, `collectAxioms` is computed; the command raises an error (non-zero
  exit) on any axiom other than `propext`, `Classical.choice`, `Quot.sound` (this includes `sorryAx`
  and `Lean.ofReduceBool`) or on any `axiom` declaration. The audit was tested to fail on a module
  containing a `sorry` theorem and an `axiom`.

## Conditional content

The repository declares no axioms. Open assumptions are explicit hypotheses (Lean arguments or
named `Prop`s), so every theorem that uses them is a conditional implication. The list below is
exactly what the headline theorems take.

- **(b) Classical results not in Mathlib:**
  - `hKato`: every smooth, divergence-free, finite-energy datum has a `KatoLocalWitness` (Kato
    local existence). The witness now asks for the equations only on `[0, T]`.
  - `TetheredLyapunov.BKMGlobalContinuation` (Kato local theorem plus Beale–Kato–Majda
    continuation, with the `H^s` versus `C^∞ ∩ L²` data-class caveat).
  - `TetheredLyapunov.SmoothPhysicalUniqueness` (uniqueness of smooth solutions on a common
    interval). Used only by the uniqueness clause of `conditional_regularity_of_open_hyps` and
    `frohmanian_conditional_regularity_of_closing_bound`.
  - `PeriodicBKMContinuation` (for `clay_B_exact_of_periodic_tether_bound` and
    `clay_B_exact_of_torus_direction_depletion`).
  - `KatoUniquenessOnExistenceTimes` (only for `smoothBelowTstar_of_katoUniqueness`).
  - `IsCoadjointMotion` for the Euler flow (`PlanSteps`).
- **(d) Equivalent in strength to the open problem:**
  - `LocalTetherRate` (`hDI` of `frohmanian_tether_theorem`). It includes time-differentiability
    of `‖ω(t)‖∞`.
  - `LocalTetherBound` (`hRiccati`) and `ClayStatements.LocalTetherClosingBound`.
  - `PeriodicTetherClosingBound` and `PeriodicDirectionDepletionBound`.
  - `FrohmanianTetherRate`, `FrohmanianTetherBound`, `FrohmanianTetherClosingBound` and
    `ClosureBlueprint.RiccatiMajorantExists`. These are the global-path forms, kept for auxiliary
    lemmas only.
- **(c) Kernel-class conditions on a competitor `B`** (hypotheses of the uniqueness theorems; they
  define the class, so they are not provable for every `B`): `h_sym`,
  `PolarizesOnDifferentiable B`, `SaturatesTetherQuadratic B`, `h_proj`, `h_density` (locally
  integrable density) and `h_weight : AEEnstrophyWeight B` (locally integrable densities), together
  with C1/C2/C3 for `B` in `uniqueness_of_minimal_tether`.
- **Open (not proved, not refuted) for `TetherKernel` itself:**
  - C2 at regular ω (`DegenerateWRTKineticEnergy TetherKernel`; expected to fail).
  - Transport-invariance under rotations and general volume-preserving diffeomorphisms (not
    formalized).
  - Any Jacobi identity.
- **Proved for `TetherKernel` in the fifth pass:** `AEEnstrophyWeight TetherKernel`
  (`tetherKernel_aeEnstrophyWeight`); transported C1 for translations
  (`tetherKernel_transported_invariant`).
- **Refuted, so no theorem assumes them:** `Polarizes TetherKernel`, pointwise `h_weight`,
  `AEEnstrophyWeightUnrestricted TetherKernel`, C1 for `TetherKernel` under the concrete action
  (`InvariantUnderCoadjointAction ConcreteSDiff.G TetherKernel`), `Step1Hyp`, and the hypotheses
  removed in the earlier passes. (C1 for a competitor `B` remains a carried, unused hypothesis of
  `uniqueness_of_minimal_tether` over an abstract action.)
- Nothing here proves global regularity of the 3D Navier–Stokes equations or any part of the Clay
  Millennium Problem.

## Dependency revisions (`lake-manifest.json`)

| Package | Input rev | Rev |
|---|---|---|
| mathlib | `v4.30.0-rc1` | `0c154d67103f74be3a0f2c509f72ccbf5be9f2a7` |
| plausible | `main` | `f449eabb8f7e3feef0366856c20e28a6d2c97ee3` |
| LeanSearchClient | `main` | `c5d5b8fe6e5158def25cd28eb94e4141ad97c843` |
| importGraph | `main` | `86503d416c875fdcf3b6b6c54c22581e96c6bda7` |
| proofwidgets | `v0.0.97` | `82d457fb3bdd9efadbae06608ff337d689efdddf` |
| aesop | `v4.30.0-rc1` | `f74c7555aaa94eadd7b7bff9170f7983f92aac21` |
| Qq | `v4.30.0-rc1` | `7aa86cb20b8458748dc24d55dab2d7ea01161057` |
| batteries | `v4.30.0-rc1` | `bf597c77bf9b8e66720d724928207f5911533113` |
| Cli | `v4.30.0-rc1` | `f7d0ca7c926cdde0562af20394dd25d028b839a5` |

## Axiom report (`lake env lean scripts/AxiomAudit.lean`, local run on the verified commit `09d14b6`; same summary as the CI artifact `axioms` of run 42783533141)

```
'AnalyticPipeline.bkm_integrableOn_of_uniform_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AnalyticPipeline.bkm_regularity_pipeline' depends on axioms: [propext, Classical.choice, Quot.sound]
'AnalyticPipeline.bkm_time_integral_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AnalyticPipeline.comparison_ode_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AnalyticPipeline.comparison_ode_stability' depends on axioms: [propext, Classical.choice, Quot.sound]
'AnalyticPipeline.holderConjugate_three_halves_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'AnalyticPipeline.holder_I4' depends on axioms: [propext, Classical.choice, Quot.sound]
'AnalyticPipeline.holder_I4_le_sobolev' depends on axioms: [propext, Classical.choice, Quot.sound]
'AnalyticPipeline.majorant_vector_field_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AnalyticPipeline.majorant_vector_field_neg_of_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'AnalyticPipeline.stretching_bound_of_holder' depends on axioms: [propext, Classical.choice, Quot.sound]
'AnalyticPipeline.vorticity_sup_norm_riccati_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AnalyticPipeline.young_inequality_eps' depends on axioms: [propext, Classical.choice, Quot.sound]
'AnalyticPipeline.youngs_absorption_elimination' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.BiotSavart_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.BiotSavart_affine' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.BiotSavart_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.BiotSavart_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.BiotSavart_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.Casimir.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.CoadjointAction_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.CoadjointAction_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.CoadjointAction_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.CoadjointAction_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.CoadjointOrbit.mk.congr_simp' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.CoadjointOrbit.mk.inj' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.CoadjointOrbit.mk.injEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.CoadjointOrbit.mk.sizeOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.CoadjointOrbit.property' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.Enstrophy.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.FunctionalDerivative.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.FunctionalDerivative_eq_zero_of_not' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.IsFunctionalGradient.add' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.IsFunctionalGradient.sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.IsRegularVorticity.continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.IsTestDirection.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.IsTestDirection.memLp' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.IsTestDirection.regular' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.SDiffActionHyp.casimir_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.SDiffActionHyp.enstrophy_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.biotSavartKernel_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.biotSavartKernel_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.casimir_const_on_orbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.classicalBracket_H_H' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.classicalBracket_antisymm' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.classicalBracket_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.classical_bracket_reproduces_Euler' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.cross.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.cross_add_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.cross_add_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.cross_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.cross_smul_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.cross_smul_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.differentiableAt_biotSavartKernel_off_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.differentiableAt_cross_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.differentiableAt_cross_offset_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.div_BiotSavart_of_interchange' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.div_biotSavart_integrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.div_biotSavart_integrand_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.div_cross_offset' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.div_cross_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.functionalDerivative_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.functionalDerivative_eq_zero_of_not_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.functionalDerivative_indep_of_not_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.gateaux_representative_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.hasDerivAt_half_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.hasDerivAt_half_norm_sq_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.hasFDerivAt_biotSavartKernel_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.hasFDerivAt_norm_sq_offset' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.inner_eq_zero_of_forall_test' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.isFunctionalGradient_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.isGateauxRepresentative_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.isVelocityGateauxRepresentative_kineticEnergy_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.kineticEnergyHamiltonian_hasDerivAt_velocity_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.kineticEnergy_hasDerivAt_velocity_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.norm_rpow_neg_three_eq_norm_sq_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.orbitLine.congr_simp' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.orbitLine.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.orbit_add_smul_div_free' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.pairing.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.pairing_cross_self_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.testToL2.congr_simp' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.testToL2.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.velocity_from_vorticity.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.velocity_from_vorticity_eq_BiotSavart' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.velocity_from_zero_orbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClosureBlueprint.beale_kato_majda_criterion' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClosureBlueprint.bkm_integrableOn_of_uniform_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClosureBlueprint.bkm_regularity_pipeline' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClosureBlueprint.comparison_ode_bound_of_equality' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClosureBlueprint.comparison_ode_solution_existence' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClosureBlueprint.comparison_ode_stability' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClosureBlueprint.conditional_regularity_of_open_hyps' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClosureBlueprint.continuation_under_global_existence' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClosureBlueprint.local_existence_kato' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClosureBlueprint.lyapunov_quartic_cancellation_skeleton' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClosureBlueprint.regularity_from_riccati_majorant' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClosureBlueprint.type_composition_sequence' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClosureBlueprint.uniqueness_of_kernel_density' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClosureBlueprint.youngs_absorption_elimination' depends on axioms: [propext, Classical.choice, Quot.sound]
'Combined.left_H_zero_of_C2_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Combined.tetherKernel_C3'' depends on axioms: [propext, Classical.choice, Quot.sound]
'Combined.tetherKernel_left_H_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConcreteSDiff.casimir_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConcreteSDiff.coe_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConcreteSDiff.constOrbit.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConcreteSDiff.divPres_add_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConcreteSDiff.divPres_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConcreteSDiff.enstrophy_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConcreteSDiff.good' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConcreteSDiff.good_addRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConcreteSDiff.not_transitive_on_casimir_levels' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConcreteSDiff.orbit_ext' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConcreteSDiff.sdiffActionHyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConcreteSDiff.smul_constOrbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConcreteSDiff.smul_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConcreteSDiff.translate.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConcreteSDiff.translate_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConcreteSDiff.translate_inv_smul_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConcreteSDiff.translate_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConcreteSDiff.translate_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConcreteSDiff.translate_smul_rotOrbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConcreteSDiff.translate_smul_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConcreteSDiff.translate_test' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConditionalRegularity.conditional_regularity_of_open_hyps' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConditionalRegularity.frohmanian_tether_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContDiffBump.mk.congr_simp' depends on axioms: [propext, Classical.choice, Quot.sound]
'ForMathlib.Pi_u.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'ForMathlib.Pi_u_is_the_L2_orthogonal_projection_onto_complement_of_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'ForMathlib.Pi_u_of_energy_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'ForMathlib.Pi_u_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'ForMathlib.pairing_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'ForMathlib.projection_orthogonal_to_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'ForMathlib.projector_orthogonality' depends on axioms: [propext, Classical.choice, Quot.sound]
'Frohmanian.AssemblyGap.classical_max_rate_of_cubic_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'Frohmanian.AssemblyGap.classical_source_not_reduced_strain' depends on axioms: [propext, Classical.choice, Quot.sound]
'Frohmanian.CubicSourceAudit.ClassicalStretchingSource.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Frohmanian.CubicSourceAudit.ReducedStrain.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Frohmanian.CubicSourceAudit.corrected_rate_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'Frohmanian.CubicSourceAudit.cubic_field_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Frohmanian.CubicSourceAudit.cubic_sink_of_corrected_rate' depends on axioms: [propext, Classical.choice, Quot.sound]
'Frohmanian.CubicSourceAudit.reduced_pairing_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Frohmanian.CubicSourceAudit.source_rate_sub_sink' depends on axioms: [propext, Classical.choice, Quot.sound]
'Frohmanian.CubicSourceAudit.weighted_source_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.CalderonZygmundConstant3D_eq_three_halves' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.CalderonZygmundConstant3D_ne_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.CalderonZygmundConstant3D_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.ClayStatements.bkmGlobalContinuation_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.ClayStatements.bkm_of_closing_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.ClayStatements.clay_B_exact_of_periodic_tether_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.ClayStatements.clay_B_exact_of_with_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.ClayStatements.closing_bound_uniqueness_family_unsatisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.ClayStatements.conditional_regularity_nonvacuous_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.ClayStatements.frohmanianTetherBound_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.ClayStatements.frohmanianTetherRate_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.ClayStatements.frohmanian_conditional_regularity_of_closing_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.ClayStatements.isZ3Periodic_iff_unit_shifts' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.ClayStatements.library_huniq_unsatisfiable_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.ClayStatements.localTetherBound_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.ClayStatements.repaired_huniq_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.ClayStatements.smoothPhysicalUniqueness_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.ClayStatements.stepField.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.ClayStatements.stepField_not_physical' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.ClayStatements.vorticity_sup_norm_zero_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.HighSetDepletionAndBKM.clay_B_exact_of_torus_direction_depletion' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.HighSetDepletionAndBKM.comparison_ode_ceiling' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.HighSetDepletionAndBKM.cubic_comparison_field_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.HighSetDepletionAndBKM.cubic_comparison_field_neg_of_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.HighSetDepletionAndBKM.periodicTetherClosingBound_of_directionDepletion' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.HighSetDepletionAndBKM.scale_invariant_cubic_rate_of_direction_coercivity' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.HighSetDepletionAndBKM.unmodified_max_rate_of_cubic_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.HighSetDepletionAndBKM.viscous_direction_dissipation_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.Pi_u_smul_of_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.SobolevConstant3D_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.Step1Hyp.deriv_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.Step1Hyp.sub_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.Step1Hyp.zero_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.TetherKernel.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.TorusStrainExclusion.aligned_vorticity_stretching_integrand_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.TorusStrainExclusion.biot_savart_det_aligned_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.TorusStrainExclusion.biot_savart_det_difference_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.TorusStrainExclusion.burgersLinearStrain_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.TorusStrainExclusion.burgersLinearStrain_div_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.TorusStrainExclusion.burgersLinearStrain_not_z3_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.TorusStrainExclusion.burgers_background_strain_not_z3_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.TorusStrainExclusion.cross3_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.TorusStrainExclusion.det3_self_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.TorusStrainExclusion.linear_strain_not_z3_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.TorusStrainExclusion.navier_stokes_scaling_homogeneity_deg6' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.TorusStrainExclusion.navier_stokes_vorticity_dt_scaling_exponent' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.TorusStrainExclusion.t3_eq_sum_stdBasisVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.TorusStrainExclusion.unnormalized_quartic_scaling_mismatch' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.TorusStrainExclusion.z3_periodic_continuousLinear_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.TorusStrainExclusion.z3_periodic_coord_diff_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.TorusStrainExclusion.z3_periodic_deriv_integral_unit_interval_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.TorusStrainExclusion.z3_periodic_linear_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.TorusStrainExclusion.z3_periodic_unit_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.antisym_sat_forces_zero_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.antisymmetric_clause_forces_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.antisymmetric_correction_diagonal_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.canonicalTetherDensity_locallyIntegrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.div_biot_savart_of_eq_curl' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.div_biot_savart_velocity_of_interchange' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.hPi_of_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.kappa'_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.kappa_eq_three_halves' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.kappa_ne_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.kappa_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.max_rate_of_reduced_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.not_pointwiseEnstrophyWeight_of_density' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.not_pointwiseEnstrophyWeight_tetherKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.not_polarizes_tetherKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.not_step1Hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.not_tetherKernel_invariant_concrete' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.not_tetherKernel_invariant_of_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.not_tetherKernel_invariant_transSubgroup' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.not_transported_invariant_pointEval' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.pairsToZero_of_C2' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.pointEvalKernel.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.polarizes_tetherKernel_zero_of_not_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.reduced_pairing_iff_cancels_kappa_M4' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.step1_of_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.step2_degree' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.step2_degree_of_canonical_density' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.step2_degree_of_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.step2_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.step2_quadratic_and_locality' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.step3_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.step4_scalar_eq_kappa' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.step5_eq_tether' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.step5_higher_order' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.tetherKernel_C2_of_no_gateaux' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.tetherKernel_C3' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.tetherKernel_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.tetherKernel_diagonal_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.tetherKernel_has_canonical_density' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.tetherKernel_indep_of_not_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.tetherKernel_kernel_conditions' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.tetherKernel_nondegenerate_on_casimir_defect' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.tetherKernel_of_right_factor_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.tetherKernel_polarizesOnDifferentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.tetherKernel_quadratic_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.tetherKernel_strict_neg_of_orthogonal_component' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.tetherKernel_symmetric' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.tetherKernel_transported_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.tetherPointwiseDensity_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.tetherPointwiseDensity_strict_neg_of_noncasimir' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.tether_kernel_density_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.tether_nondeg_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.time_pairing_le_stretching_at_max' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.uniqueness_of_kernel_density' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.uniqueness_of_kernel_density_fun' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.uniqueness_of_minimal_symmetric_tether' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.uniqueness_of_minimal_tether' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.uniqueness_of_minimal_tether_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'IndependentMajorant.comparison_majorant_global_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'IndependentMajorant.lemma_3_1_uniform_bound_and_continuation' depends on axioms: [propext, Classical.choice, Quot.sound]
'KineticEnergyDerivative.biotSavart_indField_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KineticEnergyDerivative.bsField0_coord2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KineticEnergyDerivative.continuousOn_bsInt0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KineticEnergyDerivative.ctr.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KineticEnergyDerivative.div_indField' depends on axioms: [propext, Classical.choice, Quot.sound]
'KineticEnergyDerivative.e1.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KineticEnergyDerivative.fderiv_eq_zero_of_two_valued' depends on axioms: [propext, Classical.choice, Quot.sound]
'KineticEnergyDerivative.functionalDerivative_of_not_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KineticEnergyDerivative.indField.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KineticEnergyDerivative.indField_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'KineticEnergyDerivative.indField_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KineticEnergyDerivative.indOrbit.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KineticEnergyDerivative.integrable_bsField0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KineticEnergyDerivative.isGateauxRepresentative_of_not_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KineticEnergyDerivative.ne_zero_of_mem_closedBall' depends on axioms: [propext, Classical.choice, Quot.sound]
'KineticEnergyDerivative.not_differentiableAt_indField' depends on axioms: [propext, Classical.choice, Quot.sound]
'KineticEnergyDerivative.not_forall_functionalDerivative_kineticEnergy_eq_velocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'KineticEnergyDerivative.not_unique_isGateauxRepresentative' depends on axioms: [propext, Classical.choice, Quot.sound]
'KineticEnergyDerivative.not_unique_velocity_representative' depends on axioms: [propext, Classical.choice, Quot.sound]
'KineticEnergyDerivative.one_lt_coord_of_mem_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'LinearMap.mk₂.congr_simp' depends on axioms: [propext, Quot.sound]
'MathlibAgreement.cross_eq_crossProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathlibAgreement.div_eq_sum_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathlibAgreement.eb_eq_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathlibAgreement.enstrophy_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathlibAgreement.l2Translate_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathlibAgreement.pairing_eq_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathlibAgreement.pd_eq_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathlibAgreement.translate_eq_addRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathlibAgreement.volume_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.IsPhysicalNSSolution.on' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.IsPhysicalNSSolutionOn.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.KatoLocalWitness.Tpos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.KatoLocalWitness.init' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.KatoLocalWitness.mk.inj' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.KatoLocalWitness.mk.injEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.KatoLocalWitness.mk.sizeOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.KatoLocalWitness.pde' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.KatoLocalWitness.phys' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.KatoLocalWitness.smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.NS_PDE.on' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.NS_PDE_On.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.Tstar_eq_top_iff_forall_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.Tstar_eq_top_of_bkm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.Tstar_eq_top_of_katoRestartTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.Tstar_eq_top_of_unbounded_existenceTimes' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.Tstar_eq_top_of_uniform_restart' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.Tstar_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.Tstar_pos_of_exists_smooth_solution' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.Tstar_pos_of_kato_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.Tstar_zero_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.VorticityTransportRegularity.pressureC2' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.VorticityTransportRegularity.spaceC1' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.VorticityTransportRegularity.spaceC2' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.VorticityTransportRegularity.spaceC3' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.VorticityTransportRegularity.spacetimeC2' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.beale_kato_majda' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.beale_kato_majda_scaffold' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.beale_kato_majda_scaffold_integrability_unused' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.bkm_criterion_without_integrability_not_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.contDiffAt_directionalCoord' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.convective.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.convective_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.convective_difference' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.convective_energy_pairing_vanishes' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.convective_eq_sum_directional' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.convective_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.convective_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.curl.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.curl_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.curl_add3' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.curl_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.curl_convective' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.curl_convective_div_free' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.curl_gradient' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.curl_laplacian' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.curl_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.curl_time_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.curl_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.cyclicLiePairing_expand' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.deriv_euclidean_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.deriv_prod_fst_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.differentiableAt_convective_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.differentiableAt_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.differentiableAt_coord_of_differentiableAt_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.differentiableAt_curl' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.differentiableAt_curl_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.differentiableAt_directionalCoord' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.differentiableAt_half_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.differentiableAt_of_contDiffAt_coords' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.differentiableAt_pressureGradient_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.differentiableAt_time_deriv_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.directionalCoord.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.directionalCoord_convective' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.directionalCoord_curl' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.directionalCoord_laplacian' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.directionalCoord_pressureGradient' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.directionalCoord_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.directionalCoord_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.div.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.div_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.div_add_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.div_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.div_curl' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.div_of_eq_curl' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.div_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.div_smul_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.div_zero_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.energy_zero_of_gronwall' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.energy_zero_of_gronwall_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.eq_of_l2_energy_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.eq_zero_of_isPhysicalNSSolutionOn_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.eq_zero_of_isPhysicalNSSolution_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.eq_zero_of_isPhysicalNSSolution_zero_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.ereal_eq_top_of_bkm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.exists_mem_existenceTimes_gt_of_lt_Tstar' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.fderiv_apply_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.fderiv_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.fderiv_directionalCoord' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.fderiv_field_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.fderiv_prod_snd_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.gradient_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.inner_convective_eq_inner_grad_half_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.inner_convective_le_strain' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.inner_convective_product_rule' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.inner_self_convective_eq_inner_grad_half_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.integration_by_parts_of_vanishing_flux' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.isPhysicalNSSolution_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.katoRestartTime_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.katoSobolevIndex_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.kato_Hs_bound_on_restart_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.kato_ponce_implies_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.kato_ponce_of_uniform_vorticity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.laplacian.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.laplacian_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.laplacian_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.le_Tstar_of_mem_existenceTimes' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.le_vorticity_sup_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.local_existence' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.mem_existenceTimes' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.mem_existenceTimes_of_kato_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.mem_existenceTimes_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.navier_stokes_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.ns_cauchy_eq_of_energy_gronwall' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.ns_cauchy_of_energy_gronwall' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.ns_cauchy_on_Icc_of_energy_gronwall' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.ns_momentum_difference' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.ns_pde_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.one_add_log_le_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.parabolic_regularity_from_vorticity_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.pressureGradient.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.pressureGradient_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.pressureGradient_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.pressure_energy_pairing_vanishes' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.reciprocal_of_quadratic_growth' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.smoothness_below_Tstar_of_uniqueness' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.smoothness_of_Tstar_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.smoothness_on_restart_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.smul_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.sum_univ_fin3' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.time_deriv.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.time_deriv_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.time_deriv_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.time_deriv_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.time_space_mixed_partials' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.transport_inner_vanishes_of_grad_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.transported_energy_pairing_vanishes' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.transported_scalar_along_characteristic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.transported_scalar_maximum_principle' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.uniqueness_of_existence_times_of_energy_gronwall' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.volume.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.vorticity_sup_norm_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.vorticity_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.vorticity_transport_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.vorticity_transport_equation' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.vorticity_transport_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
'PhysicalSolutionSanity.exists_physical_time_deriv_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'PhysicalSolutionSanity.not_forall_physical_time_deriv_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'PhysicalSolutionSanity.physical_time_deriv_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'PhysicalSolutionSanity.sanityPath_isPhysical' depends on axioms: [propext, Classical.choice, Quot.sound]
'PlanSteps.bsSymbol.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'PlanSteps.bsSymbol_curl' depends on axioms: [propext, Classical.choice, Quot.sound]
'PlanSteps.bsSymbol_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'PlanSteps.casimir_conserved' depends on axioms: [propext, Classical.choice, Quot.sound]
'PlanSteps.tether_bound_not_scale_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScalingIdentities.directionalCoord_rescale' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScalingIdentities.vorticity_rescale' depends on axioms: [propext, Classical.choice, Quot.sound]
'StrainBoundRefutation.not_forall_strain_le_sup_vorticity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.FrohmanianMetriplecticPairing_diag_eq_metric' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.PeriodicCellPhysicalNSSolution.cell_energy_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.PeriodicCellPhysicalNSSolution.cell_energy_le_init' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.PeriodicCellPhysicalNSSolution.init_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.PeriodicCellPhysicalNSSolution.pde_ici' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.PeriodicCellPhysicalNSSolution.periodic_p' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.PeriodicCellPhysicalNSSolution.periodic_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.PeriodicCellPhysicalNSSolution.smooth_p' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.PeriodicCellPhysicalNSSolution.smooth_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.PeriodicCellPhysicalNSSolution.viscosity_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.Pi_u_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.Pi_u_self_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.SpatialMaxVorticityEnvelope.attains_max' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.SpatialMaxVorticityEnvelope.convective_grad_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.SpatialMaxVorticityEnvelope.danskin_rate_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.SpatialMaxVorticityEnvelope.def_M' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.SpatialMaxVorticityEnvelope.differentiable_M' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.SpatialMaxVorticityEnvelope.satisfies_ns' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.SpatialMaxVorticityEnvelope.transport_reg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.SpatialMaxVorticityEnvelope.viscosity_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.SpatialMaxVorticityEnvelope.viscous_laplacian_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.TetherKernel_eq_tetherMetricForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.VolumePreservingCoadjointAction.integral_comp_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.VolumePreservingCoadjointAction.mk.inj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.VolumePreservingCoadjointAction.mk.injEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.VolumePreservingCoadjointAction.mk.sizeOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.VortexLineMonodromyCondition.casimir_transverse_damping' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.VortexLineMonodromyCondition.coadjoint_monodromy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.VortexLineMonodromyCondition.kelvin_circulation_preserved' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.VortexLineMonodromyCondition.orbit_trajectory' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.bddAbove_range_norm_of_attained_max' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.beltrami_casimir_projection_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.beltrami_lamb_vector_cross_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.beltrami_tetherPointwiseDensity_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.bochner_laplacian_3d_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.concrete_bochner_polar_viscous_damping_at_max' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.constVelocity_convective_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.constVelocity_laplacian_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.constVelocity_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.constantin_fefferman_near_far_cutoff_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.cross_anticomm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.cross_jacobi_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.cross_self_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.first_remaining_gap_bochner_polar_damping_at_max' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.kksPointwiseIntegrand_skew' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.kksPointwise_cyclic_jacobi_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.kksSymplecticForm_functional_skew' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.kksSymplecticForm_self_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.kksSymplecticForm_skew' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.navier_stokes_eq_constVelocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.near_field_stretching_absorbed_by_viscous_direction_damping' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.nonzero_smooth_ns_solution_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.periodicCellPhysical_implies_IsPeriodicSmoothSolution' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.polar_pythagoras_3d_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.polar_pythagoras_directional_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.symplectic_constraint_yields_cubic_damping_and_ceiling' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.tetherMetricForm_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Symplectori.SymplecticConstraint.vorticity_sup_norm_eq_of_isSpatialMax' depends on axioms: [propext, Classical.choice, Quot.sound]
'TestFieldFamily.concBump.congr_simp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TestFieldFamily.concBump.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TestFieldFamily.concField.congr_simp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TestFieldFamily.concField.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TestFieldFamily.concField_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TestFieldFamily.concField_test' depends on axioms: [propext, Classical.choice, Quot.sound]
'TestFieldFamily.contDiff_curlVal' depends on axioms: [propext, Classical.choice, Quot.sound]
'TestFieldFamily.contDiff_pd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TestFieldFamily.curlOrbit.congr_simp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TestFieldFamily.curlOrbit.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TestFieldFamily.curlOrbit_test' depends on axioms: [propext, Classical.choice, Quot.sound]
'TestFieldFamily.curlOrbit_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'TestFieldFamily.curlVal.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TestFieldFamily.curlVal_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TestFieldFamily.div_curlVal' depends on axioms: [propext, Classical.choice, Quot.sound]
'TestFieldFamily.hasCompactSupport_curlVal' depends on axioms: [propext, Classical.choice, Quot.sound]
'TestFieldFamily.inner_curlVal' depends on axioms: [propext, Classical.choice, Quot.sound]
'TestFieldFamily.pd.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TestFieldFamily.tsupport_concField_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'TestFieldFamily.tsupport_curlVal_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherEquivariant.biotSavartKernel_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherEquivariant.biotSavart_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherEquivariant.functionalDerivative_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherEquivariant.isFunctionalGradient_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherEquivariant.l2Translate_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherEquivariant.l2Translate_mem_divFreeL2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherEquivariant.l2Translate_testToL2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherEquivariant.mp_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherEquivariant.tI_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherEquivariant.tetherKernel_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.absFun.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.absFun_gradient_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.absFun_gradient_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.absFun_no_gradient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.biotSavartKernel_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.bump_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.continuous_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.div_rotField' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.eb.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.hasFDerivAt_rotField_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.inner_eb' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.inner_self_testToL2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.inner_testToL2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.integrable_inner_test' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.integral_rotField_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.linFun.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.linFun_gradient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.linFun_orbitLine' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.not_forall_functionalDerivative_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.not_tetherKernel_polarizes' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.pi_u_L2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.rotField.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.rotField_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.rotField_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.rotField_eq_zero_of_far' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.rotField_hasCompactSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.rotField_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.rotL.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.rotL_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.rotL_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.rotOrbit.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.rot_test' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.stronglyMeasurable_biotSavart' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.tI.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.tetherIntegral_L2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.tetherKernel_absFun_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.tetherKernel_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.tetherKernel_eq_zero_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.tetherKernel_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.tetherKernel_polarizes_of_gradient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherNondegeneracy.tetherKernel_rot_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeight.enstrophy_zeroOrbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeight.exists_vitaliSet_rep' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeight.integral_indicator_vitaliSet_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeight.measure_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeight.not_aeEnstrophyWeightUnrestricted_of_eq_tether' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeight.not_aeEnstrophyWeightUnrestricted_tetherKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeight.shift.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeight.shift_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeight.shift_subset_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeight.tetherKernel_has_locallyIntegrable_density' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeight.vitaliDensity.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeight.vitaliDensity_is_density' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeight.vitaliSet_measure_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeight.vitaliSet_null_of_measurable' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeight.vitaliSet_null_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeight.vitaliSet_subset_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeight.vitaliSet_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeight.zeroOrbit.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeight.zeroOrbit_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.aeEnstrophyWeight_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.ae_zero_of_killsOrth' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.ae_zero_on_good_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.bad_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.comb.congr_simp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.comb_test' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.comb_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.continuous_inner_test' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.good_of_not_coefPt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.good_of_two_correctors' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.hasCompactSupport_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.integrable_mul_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.integral_beta_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.pi_u_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.pi_u_testToL2_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.pointwise_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.projCoef.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.projCoef_add_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.projCoef_congr_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.tetherKernel_aeEnstrophyWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetherWeightProof.tetherKernel_core_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.ComparisonODE_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.IsComparisonODESolution.deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.IsComparisonODESolution.init' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.LyapunovSminus.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.Tstar_top_of_restart_without_vorticity_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.bkmIntegrability_of_finiteTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.comparison_ode_clipped_on_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.comparison_ode_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.comparison_ode_local_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.comparison_ode_stability_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.conditional_regularity' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.conditional_regularity_of_local_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.conditional_regularity_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.finiteTimeVorticityBound_of_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.global_solutions_eq_of_uniqueness' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.hasDerivAt_lyapunov_density' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.hasDerivAt_lyapunov_density_unweighted' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.hasDerivAt_lyapunov_minus_of_enstrophy_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.hasDerivAt_lyapunov_plus_of_enstrophy_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.hasDerivAt_majorantField' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.hasDerivAt_norm_pow_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.hasDerivAt_norm_sq_of_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.hasDerivAt_quartic_tether_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.integrableOn_Icc_zero_of_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.isLocalPhysicalSolution_of_global' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.lemma_3_1_uniform_bound_and_continuation' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.localExistenceTime_of_kato' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.localFiniteTimeVorticityBound_of_localTetherBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.localTetherBound_of_localTetherRate' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.lyapunovSminus_density_ge_of_abs_phi' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.lyapunovSminus_density_le_half_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.lyapunovSminus_density_neg_of_large_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.lyapunovSminus_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.lyapunovSminus_source_density' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.lyapunovSε_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.lyapunov_ident_of_transport_cz' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.majorantField.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.majorantFieldClip_eq_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.majorantFieldClip_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.majorantFieldClip_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.majorantFieldClip_unique_on_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.majorantField_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.majorantField_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.majorantField_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.majorantField_lipschitzOn_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.majorantField_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.majorantField_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.physicalBKMIntegrability_of_finiteTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.physicalFiniteTimeVorticityBound_of_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.physicalUniformVorticityCeiling_of_tetherBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.physicalVorticityCubicRate_of_tetherRate' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.quartic_weight_source_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.riccati_ceiling_of_vorticity_di' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.smoothBelowTstar_of_katoUniqueness' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.uniform_majorant_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'TetheredLyapunov.youngs_absorption_elimination' depends on axioms: [propext, Classical.choice, Quot.sound]
'crossProduct.eq_1' depends on axioms: [propext, Quot.sound]
'fderivInnerCLM.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'gradient.congr_simp' depends on axioms: [propext, Classical.choice, Quot.sound]
AUDIT SUMMARY: theorems audited: 673 (600 stated in the sources, 73 auto-generated equation/congruence/injectivity lemmas); declarations audited: 968; violations: 0
AUDIT PASS: only propext, Classical.choice, Quot.sound; no sorryAx; no axiom declarations
```
