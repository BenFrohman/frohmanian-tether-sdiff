# The Frohmanian Tether on SDiff(𝕋³)

[![Lean certificate](https://github.com/BenFrohman/frohmanian-tether-sdiff/actions/workflows/certify.yml/badge.svg?branch=main)](https://github.com/BenFrohman/frohmanian-tether-sdiff/actions/workflows/certify.yml)
[![Lean 4](https://github.com/BenFrohman/frohmanian-tether-sdiff/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/BenFrohman/frohmanian-tether-sdiff/actions/workflows/lean.yml)
[![Lean](https://img.shields.io/badge/Lean-v4.30.0--rc1-blue.svg)](https://github.com/leanprover/lean4)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.30.0--rc1-blue.svg)](https://github.com/leanprover-community/mathlib4)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0006--7068--3718-brightgreen.svg)](https://orcid.org/0009-0006-7068-3718)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24082000.svg)](https://doi.org/10.5281/zenodo.24082000)

Lean 4 formalization and manuscript for *The Frohmanian Tether on SDiff(𝕋³): A Metriplectic
Correction, Its Canonicity, and an Obstruction to Damping* (Benjamin Stanley Frohman).

## Scope (read this first)

**This repository does not prove global regularity of the 3D Navier–Stokes equations and makes no
claim toward the Clay Millennium Problem.** All results about the full program are *conditional
implications*: every open assumption is an explicit Lean hypothesis.

What is formalized:

* The tether kernel `TetherKernel` (a symmetric quadratic metric correction to the Arnold
  Lie–Poisson bracket) and the conditions (C1)–(C3).
* C1 (coadjoint invariance): **not proved**. The two hypotheses earlier versions used for it
  (`SDiffActionHyp.transitive_on_casimir_levels`, refuted, and `TetherIntegralPreserved`) were removed
  together with the C1 theorems (see below).
* `FunctionalDerivative` is a genuine derivative. `FunctionalDerivative F ω` is the unique
  divergence-free `L²` field `g` with `d/dt|₀ F(ω + tε) = ⟪g, ε⟫_{L²}` for every smooth, compactly
  supported, divergence-free test field `ε`, at a vorticity whose components are differentiable.
  When no such `g` exists, it is `0`. Uniqueness is proved (`ArnoldGeometric.isFunctionalGradient_unique`),
  so no arbitrary choice is made.
* C2 (degeneracy w.r.t. kinetic energy): **not proved** for `TetherKernel` at regular vorticities
  (proved only where `H` has no gradient, `tetherKernel_C2_of_no_gateaux`). The hypothesis
  `KineticEnergyDerivIsVelocity` (δH/δω = u) that earlier versions used for it is **false** with the
  repository's definitions; the refutation is proved in Lean
  (`KineticEnergyDerivative.not_forall_functionalDerivative_kineticEnergy_eq_velocity`), and the
  hypothesis and every theorem that assumed it have been removed (see below).
* C3 (controllable negative feedback): unconditional (`tetherKernel_C3`).
* Canonicity: uniqueness only within the restricted kernel class and under the explicit
  hypotheses of `uniqueness_of_minimal_tether` — not an unconditional uniqueness theorem. The proof
  uses only diagonal saturation (`B(F,F) = T(F,F)`) and polarization restricted to functionals that
  have gradients (`PolarizesOnDifferentiable`), and concludes `B = T` on such functionals; C1–C3 are
  not used. For `TetherKernel` itself:
  * proved: nondegeneracy (`TetherNondegeneracy.tetherKernel_nondegenerate`), restricted polarization,
    saturation, `h_proj` and the canonical density (`tetherKernel_kernel_conditions`);
  * refuted: unrestricted polarization (`TetherNondegeneracy.not_tetherKernel_polarizes`), the
    pointwise weight condition for any kernel with a density (`not_pointwiseEnstrophyWeight_of_density`;
    the earlier core theorem that assumed it was vacuous) and `Step1Hyp` (`not_step1Hyp`);
  * open: the a.e. weight condition `AEEnstrophyWeight TetherKernel`.
* **Obstruction to damping (proved, conditional on C2):** for every symmetric kernel, C2 forces
  `B(H,M) = B(M,H) = 0` for every functional `M` (`Combined.left_H_zero_of_C2_symm`,
  `Combined.tetherKernel_left_H_zero`). So a symmetric tether that preserved the Euler vector field
  would have damping coefficient 0, and nothing in the geometric layer supplies the rate or
  closing-bound hypotheses.
* `ConcreteSDiff`: a concrete subgroup of measurable, measure- and divergence-preserving
  permutations of ℝ³; `SDiffActionHyp` (now only Casimir invariance) is proved for it
  (`ConcreteSDiff.sdiffActionHyp`).
* Classical bracket antisymmetry and `{H,H}_cl = 0` (`ArnoldGeometric`), vorticity scaling
  (`ScalingIdentities.vorticity_rescale`). The full tethered bracket is **not** antisymmetric, and no
  Jacobi identity is claimed for it.
* `IsPhysicalNSSolution` was repaired. The old clause `u t = u 0` for `t ≤ 0` forced `∂ₜu(0) = 0`, since
  `deriv` is two-sided. It is now an affine extension: `∃ v₀, ∀ t ≤ 0, u t = u 0 + t • v₀`. Sanity lemma:
  `PhysicalSolutionSanity.exists_physical_time_deriv_ne_zero` gives a physical path with a nonzero time
  derivative at `t = 0`. That path is not a Navier–Stokes solution, and none is formalized.

## Removed: `KineticEnergyDerivIsVelocity` (δH/δω = u) is false

`PlanSteps.KineticEnergyDerivIsVelocity` stated
`∀ ω, FunctionalDerivative KineticEnergyHamiltonian ω = velocity_from_vorticity ω`.
`FrohmanianTether/KineticEnergyDerivative.lean` proves its negation: for `ω = 1_B e₁` (`B` the unit
ball at `(0,2,0)`) it is in `CoadjointOrbit` (its `fderiv`-based divergence is 0) and
not differentiable, so `FunctionalDerivative` is `0` there, while its Biot–Savart velocity is
nonzero at the origin. (Under the former choice-based encoding the counterexample compared `ω`
with `2ω`.)
It also proves that Gâteaux representatives are never unique, so the old "unique representative ⇒
δH = u" lemmas could never apply. The counterexample is non-smooth; the classical value of δH/δω in
the vorticity pairing (the stream function `ψ`, `curl ψ = u`) is not formalized.

Deleted (they assumed the hypothesis or its pointwise form, or concluded it from unsatisfiable
hypotheses): `PlanSteps.KineticEnergyDerivIsVelocity`, `Combined.tetherKernel_C2_of_KEDeriv`,
`tetherKernel_degenerates_on_kinetic_energy`, `tetherKernel_C2_of_identifications`,
`tethered_reproduces_classical_euler`, `degeneracy_for_mollified_sup_norm_proxy`,
`functional_derivative_of_kinetic_energy`, `functional_derivative_of_kinetic_energy_of_unique_repr`,
`ArnoldGeometric.functional_derivative_eq_velocity_of_unique_repr`. Changed statements: clause (1) of
`ConditionalRegularity.frohmanian_tether_theorem` (bracket agreement on `H` under δH = u) was
removed; `Combined.combined_conditional_capstone` (since deleted, see below) no longer took δH = u (nor the `div`/energy
hypotheses that only served it) and no longer concluded C2 or `T(H,M) = 0`.

## Removed in 0.1.2 (false, unprovable or vacuous)

Each was deleted together with every theorem that used it. No statement was silently weakened.

| Removed hypothesis | Status | Lean evidence |
|---|---|---|
| `SDiffActionHyp.transitive_on_casimir_levels` | false | `ConcreteSDiff.not_transitive_on_casimir_levels` |
| `TetherIntegralPreserved` (and the `tether_integrand_pullback` field) | unprovable under the former choice-based `FunctionalDerivative`; not reinstated after the rebuild | — |
| `PointwiseStrainSupBound` (`‖Du(x)‖ ≤ C‖ω‖∞`) | false | `StrainBoundRefutation.not_forall_strain_le_sup_vorticity` |
| `hident`/`hvanish` of `tethered_jacobi_identity` | circular (assumed the conclusion) | — |
| antisymmetric uniqueness clause | vacuous unless `T ≡ 0` | `antisymmetric_clause_forces_zero` |
| `hTlb` (uniform lower bound on Kato times), with `hInt`, `huniq_shift` | as strong as the open problem; not refuted | — |
| `Polarizes TetherKernel` | false | `TetherNondegeneracy.not_tetherKernel_polarizes` |
| pointwise `h_weight` | false for every kernel with a density | `not_pointwiseEnstrophyWeight_of_density` |
| `Step1Hyp` | false | `not_step1Hyp` |
| global `pde` field of `KatoLocalWitness`, `hcrit`, global-path `hDI` | stronger than Kato's theorem; replaced by the local witness and explicit continuation hypotheses | — |

The main theorems deleted were `tether_coadjoint_invariance`, `Combined.tetherKernel_C1_of_casimir`,
`Combined.tetherKernel_C1_of_volumePreserving`, `Combined.combined_conditional_capstone`,
`tethered_jacobi_identity`, `orbit_eq_casimir_level`, `uniqueness_of_minimal_tether_antisymmetric`,
the stretching estimates at a spatial maximum, and the bridges built on the strain bound. Full list:
`CERTIFICATE.md`. `ConditionalRegularity.frohmanian_tether_theorem` lost its antisymmetric clause and the
hypotheses `hTlb`, `hInt` and `huniq_shift`. `KatoLocalWitness` now asks for the equations only on
its interval `[0, T]`. `frohmanian_tether_theorem` now takes `hKato` (local existence),
`hcont : ∀ u₀ ν, BKMGlobalContinuation u₀ ν` and `hDI : ∀ u₀ ν, LocalTetherRate u₀ ν`.

## Remaining assumptions (explicit hypotheses; no axioms)

* **(b) Classical results not in Mathlib:**
  * `hKato`: a `KatoLocalWitness` (Kato local existence, equations on `[0, T]` only).
  * `BKMGlobalContinuation` (Kato plus Beale–Kato–Majda continuation; the classical theorem uses
    `H^s` data, the library `C^∞ ∩ L²` data on ℝ³).
  * `SmoothPhysicalUniqueness` (uniqueness of smooth solutions; only for uniqueness clauses).
  * `PeriodicBKMContinuation`, `KatoUniquenessOnExistenceTimes` (auxiliary lemmas) and
    `IsCoadjointMotion` for the Euler flow (Arnold).
* **(d) Equivalent in strength to the open problem:**
  * `LocalTetherRate` (cubic rate for `‖ω‖∞`, also requiring its time-differentiability).
  * `LocalTetherBound` and `LocalTetherClosingBound`.
  * `PeriodicTetherClosingBound` and `PeriodicDirectionDepletionBound`.
  * The global-path forms `FrohmanianTetherRate`, `FrohmanianTetherBound`,
    `FrohmanianTetherClosingBound` and `RiccatiMajorantExists` (auxiliary lemmas only).

  The tether does not supply any of them.
* **(c) Kernel-class conditions on a competitor `B`** (they define the class): `h_sym`,
  `PolarizesOnDifferentiable B`, `SaturatesTetherQuadratic B`, `h_proj`, `h_density` and
  `AEEnstrophyWeight B`, plus C1–C3 for `B` in `uniqueness_of_minimal_tether`.
* **Open for `TetherKernel`:** `AEEnstrophyWeight TetherKernel`, C2 at regular vorticities (assumed in
  `tetherKernel_left_H_zero`; expected to fail), and C1 under the concrete action.

## Build

```
lake exe cache get   # Mathlib v4.30.0-rc1
lake build
lake env lean scripts/AxiomAudit.lean
```

Build: 2726 jobs. `python3 scripts/check_no_sorry.py` finds no `sorry`, `admit`, `native_decide` or
`axiom` declaration in the sources. `scripts/AxiomAudit.lean` audits all 840 declarations in the 26
`FrohmanianTether.*` modules, including 569 theorem constants (514 stated in the sources, 55
auto-generated equation/congruence/injectivity lemmas), and **fails** if any depends on an axiom other
than `propext`, `Classical.choice`, `Quot.sound` (so `sorryAx` and `native_decide` are rejected). Both
checks run in CI (`.github/workflows/certify.yml`). See [`CERTIFICATE.md`](CERTIFICATE.md).

Every hypothesis named above is an explicit Lean argument or a named `Prop`; the repository declares no
axioms. No theorem takes any of the removed hypotheses above, or `KineticEnergyDerivIsVelocity`, as a
hypothesis.

## Contents

* `FrohmanianTether/` — Lean modules (originally extracted from the author's NS_Millennium_Proof
  project, branch `sdiff-abstract-action`, commit `0c9cfdb`; this repository is now standalone).
* `manuscript/main.tex`, `manuscript/main.pdf` — the paper (v0.1.2 draft, unreleased). It quotes the Lean statements
  verbatim from `manuscript/lean/`, generated by `python3 scripts/extract_statements.py`; build with
  `cd manuscript && tectonic main.tex`.
* `scripts/AxiomAudit.lean`, `scripts/check_no_sorry.py` — the strict audit and source scan.
* `CERTIFICATE.md` — verified commit, toolchain, Mathlib revision and the full axiom report.

## License

Apache 2.0 (see `LICENSE`). Cite via `CITATION.cff`. The Zenodo archive [`10.5281/zenodo.24082000`](https://doi.org/10.5281/zenodo.24082000) ([record](https://zenodo.org/records/24082000)) is version 0.1.1, which still contains the removed hypothesis `KineticEnergyDerivIsVelocity`.
