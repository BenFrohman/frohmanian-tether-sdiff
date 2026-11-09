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
* C1 (coadjoint invariance): conditional on `SDiffActionHyp` (the theorem takes the whole
  structure, including `transitive_on_casimir_levels`; the proof uses only `casimir_invariant`) and
  `TetherIntegralPreserved` (open).
* C2 (degeneracy w.r.t. kinetic energy): **not proved** for `TetherKernel`. The hypothesis
  `KineticEnergyDerivIsVelocity` (δH/δω = u) that earlier versions used for it is **false** with the
  repository's definitions; the refutation is proved in Lean
  (`KineticEnergyDerivative.not_forall_functionalDerivative_kineticEnergy_eq_velocity`), and the
  hypothesis and every theorem that assumed it have been removed (see below).
* C3 (controllable negative feedback): unconditional (`tetherKernel_C3`).
* Canonicity: uniqueness only within the restricted kernel class and under the explicit
  hypotheses of `uniqueness_of_minimal_tether` — not an unconditional uniqueness theorem. The proof
  uses only diagonal saturation (`B(F,F) = T(F,F)`) and polarization; C1–C3 are not used.
* **Obstruction to damping (proved, conditional on C2):** for every symmetric kernel, C2 forces
  `B(H,M) = B(M,H) = 0` for every functional `M` (`Combined.left_H_zero_of_C2_symm`,
  `Combined.tetherKernel_left_H_zero`). So a symmetric tether that preserved the Euler vector field
  would have damping coefficient 0, and nothing in the geometric layer supplies the rate or
  closing-bound hypotheses.
* `ConcreteSDiff`: a concrete subgroup of measurable, measure- and divergence-preserving
  permutations of 𝕋³ with Casimir invariance.
* Classical bracket antisymmetry and `{H,H}_cl = 0` (`ArnoldGeometric`), vorticity scaling
  (`ScalingIdentities.vorticity_rescale`). The full tethered bracket is **not** antisymmetric.

## Removed: `KineticEnergyDerivIsVelocity` (δH/δω = u) is false

`PlanSteps.KineticEnergyDerivIsVelocity` stated
`∀ ω, FunctionalDerivative KineticEnergyHamiltonian ω = velocity_from_vorticity ω`.
`FrohmanianTether/KineticEnergyDerivative.lean` proves its negation: for `ω = 1_B e₁` (`B` the unit
ball at `(0,2,0)`) and `2ω`, both are in `CoadjointOrbit` (their `fderiv`-based divergence is 0) and
not differentiable, so `FunctionalDerivative` returns the same choice value at both, while
`BiotSavart (2ω) = 2 BiotSavart ω ≠ BiotSavart ω` (its third component at the origin is negative).
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
removed; `Combined.combined_conditional_capstone` no longer takes δH = u (nor the `div`/energy
hypotheses that only served it) and no longer concludes C2 or `T(H,M) = 0`.

## Open assumptions (hypotheses of `Combined.combined_conditional_capstone`)

`SDiffActionHyp`, `TetherIntegralPreserved`, `IsCoadjointMotion`, projection factorization ⇒ density, weight/saturation/non-degeneracy
hypotheses, `FrohmanianTetherRate` and `FrohmanianTetherClosingBound` (not supplied by the
tether; at least as strong as global regularity), the BKM continuation criterion, Kato
uniqueness, and a Kato local-existence witness. BKM and Kato are cited, not formalized.

## Build

```
lake exe cache get   # Mathlib v4.30.0-rc1
lake build
lake env lean scripts/AxiomAudit.lean
```

Build: 2713 jobs. `python3 scripts/check_no_sorry.py` finds no `sorry`, `admit`, `native_decide` or
`axiom` declaration in the sources. `scripts/AxiomAudit.lean` audits all 783 declarations in the 23
`FrohmanianTether.*` modules, including 536 theorem constants (496 stated in the sources, 40
auto-generated equation/congruence/injectivity lemmas), and **fails** if any depends on an axiom other
than `propext`, `Classical.choice`, `Quot.sound` (so `sorryAx` and `native_decide` are rejected). Both
checks run in CI (`.github/workflows/certify.yml`). See [`CERTIFICATE.md`](CERTIFICATE.md).

Every hypothesis named above is an explicit Lean argument or a named `Prop`; the repository declares no
axioms. No theorem takes `KineticEnergyDerivIsVelocity` or its pointwise form as a hypothesis.

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
