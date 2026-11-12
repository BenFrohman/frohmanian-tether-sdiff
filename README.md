# The Frohmanian Tether Bound ⇒ Global Smoothness on 𝕋³ (kernel-checked, conditional)

[![Lean certificate](https://github.com/BenFrohman/frohmanian-tether-sdiff/actions/workflows/certify.yml/badge.svg?branch=main)](https://github.com/BenFrohman/frohmanian-tether-sdiff/actions/workflows/certify.yml)
[![Lean 4](https://github.com/BenFrohman/frohmanian-tether-sdiff/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/BenFrohman/frohmanian-tether-sdiff/actions/workflows/lean.yml)
[![Lean](https://img.shields.io/badge/Lean-v4.30.0--rc1-blue.svg)](https://github.com/leanprover/lean4)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.30.0--rc1-blue.svg)](https://github.com/leanprover-community/mathlib4)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0006--7068--3718-brightgreen.svg)](https://orcid.org/0009-0006-7068-3718)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24148268.svg)](https://doi.org/10.5281/zenodo.24148268)

Lean 4 formalization and manuscript for *The Frohmanian Tether Bound Implies Global Smoothness on 𝕋³ under Beale–Kato–Majda Continuation, and Implies BKM Integrability: Kernel-Checked Conditional Theorems in Lean 4* (Benjamin Stanley Frohman), version 0.1.6.

## Scope (read this first)

**Not peer-reviewed. Not an unconditional Navier–Stokes proof.** **This repository does not prove
global regularity of the 3D Navier–Stokes equations and makes no claim toward the Clay Millennium
Problem.** All results about the full program are *conditional
implications*: every open assumption is an explicit Lean hypothesis (full list by Lean name under
"Remaining assumptions" below).

## Fefferman Problem (A) reduction and tether-rate refutation (included in version 0.1.6)

**Conditional only. Clay (A) is not proved.** Merged in PR #4 and included on `main` at
`4aba751`. Kernel-checked at commit `4010251` (Lean `v4.30.0-rc1`, Mathlib `0c154d67`; axioms only
`propext`, `Classical.choice`, `Quot.sound`; rebuild: `bash scripts/verify.sh`). Full details and
`#print axioms` output are in `CERTIFICATE.md`.

* `TetherRateCounterexample.not_forall_frohmanianTetherRate`: `FrohmanianTetherRate` (and
  `FrohmanianTetherBound`) as written is **false**. A steady finite-energy field with a
  nowhere-differentiable Takagi component satisfies `NS_PDE` through Mathlib's zero junk
  derivative, while its vorticity is unbounded.
* `TetherRatePeriodicVacuity.frohmanianTetherRate_of_periodic`: on periodic data it holds only
  vacuously.
* `FeffermanClayA.clay_A_fefferman_of_frohmanianTetherRateSmooth`:
  `(∀ ν > 0, ∀ Fefferman data u₀, FrohmanianTetherRateSmooth u₀ ν) → (∀ ν > 0, R3BKMContinuation ν) → Clay_A_Fefferman`.
  `Clay_A_Fefferman` states Fefferman's official Problem (A) literally. Both hypotheses are
  **open** for general data and are shown satisfiable at `u₀ = 0`.

## Main results (version 0.1.6)

**Main Theorem (kernel-checked)** — `FrohmanianTether.ClayStatements.clay_B_exact_of_periodic_tether_bound`:

```lean
theorem clay_B_exact_of_periodic_tether_bound
    (hclose : ∀ ν > (0 : ℝ), PeriodicTetherClosingBound ν)
    (hBKM : ∀ ν > (0 : ℝ), PeriodicBKMContinuation ν) : Clay_B_exact
```

`PeriodicTetherClosingBound ν` is **the Frohmanian tether bound**: for every smooth divergence-free
ℤ³-periodic `u₀` there is one `Y` with `‖ω(t)‖_∞ ≤ Y` along every classical periodic solution from `u₀` on
every `[0, T)`. `PeriodicBKMContinuation ν` is the Beale–Kato–Majda continuation hypothesis (such a
ceiling yields a global smooth periodic solution). In version 0.1.5 both were hypotheses. In version
0.1.6, `PeriodicBKMContinuation` is **proved** ("Proved pillar: BKM continuation" below), so only the
tether bound remains open.

**Second theorem (kernel-checked)** — `FrohmanianTether.TetherImpliesBKM.periodicBKMIntegrability_of_periodicTetherBound`:
`PeriodicTetherBound ν u₀ → PeriodicBKMIntegrability ν u₀`, i.e. `∫⁻ t in Ico 0 T, ofReal ‖ω(t)‖_∞ ≤ ofReal (max Y 0 * max T₀ 0)`
for every classical periodic solution on `[0, T)`, `T ≤ T₀`.

**Proved pillar: uniqueness (kernel-checked, unconditional; included in version 0.1.6)** —
library `FrohmanianTetherPillars`, module `FrohmanianTether.Pillars.Uniqueness`. Uniqueness of classical
ℤ³-periodic solutions is imported from
[`BenFrohman/periodic-navier-stokes-smooth-uniqueness`](https://github.com/BenFrohman/periodic-navier-stokes-smooth-uniqueness)
at commit `de92662d45e8a0f47ce0c196f6dbcfe44ddb4b3b` (Lake dependency `NSTorusUniqueness`, same toolchain and
Mathlib rev). Its mirrored definitions are checked against the sdiff definitions by `rfl`
(`isPeriodicSmoothSolutionOn_eq_sdiff` and seven more), so it applies to the sdiff classes directly:

```lean
theorem periodicSmoothSolutionOn_unique (hν : 0 ≤ ν)
    (hu : IsPeriodicSmoothSolutionOn ν T u₀ u p) (hv : IsPeriodicSmoothSolutionOn ν T u₀ v q) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, u t = v t
theorem periodicSmoothSolution_unique (hν : 0 ≤ ν)
    (hu : IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p)
    (hv : IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) v q) : ∀ t ≥ (0 : ℝ), u t = v t
theorem clay_B_exact_unique_iff : Clay_B_exact_unique ↔ Clay_B_exact
theorem clay_B_exact_unique_of_periodic_tether_bound
    (hclose : ∀ ν > (0 : ℝ), PeriodicTetherClosingBound ν)
    (hBKM : ∀ ν > (0 : ℝ), PeriodicBKMContinuation ν) : Clay_B_exact_unique
```

`Clay_B_exact_unique` is Statement (B) plus uniqueness of the global velocity; both sides of the `iff` are
open. The uniqueness pillar adds the uniqueness conclusion; it discharges no hypothesis by itself.

**Proved pillar: BKM continuation (kernel-checked; included in version 0.1.6)** —
module `FrohmanianTether.Pillars.BKMContinuation`. The hypothesis `hBKM` of the Main Theorem is now a
theorem:

```lean
theorem periodicBKMContinuation_of_classical {ν : ℝ} (hν : 0 < ν) : PeriodicBKMContinuation ν
theorem clay_B_exact_of_periodic_tether_closing_bound
    (hclose : ∀ ν > (0 : ℝ), PeriodicTetherClosingBound ν) : Clay_B_exact
theorem clay_B_exact_unique_of_periodic_tether_closing_bound
    (hclose : ∀ ν > (0 : ℝ), PeriodicTetherClosingBound ν) : Clay_B_exact_unique
```

It is proved from the classical periodic theory of
[`BenFrohman/periodic-ns-classical-continuation`](https://github.com/BenFrohman/periodic-ns-classical-continuation)
at `502ff17`: Kato local existence (`periodicLocalExistence_of_nonneg`), the maximal solution
(`periodicMaximalSolution_of_uniqueness`), the Beale–Kato–Majda criterion (`periodicBKMCriterion`), continuity
of `t ↦ ‖ω(t)‖_∞` below the lifespan (`continuousOn_vorticity_Ico`) and `periodicGlobalOfTstarTop`.
That repository (with its dependency `fefferman-clay-navier-stokes` @ `ebcf109`) declares the same
`NavierStokes3D.*` names as this library, so it cannot be imported next to it. It is therefore vendored in
[`vendor/BKMPillar`](vendor/BKMPillar/VENDOR.md) with one mechanical rename (`NavierStokes3D` →
`FeffermanNavierStokes3D`, module prefix `BKMPillar.`), checked file by file against the upstream commits by
`bash scripts/check_vendor.sh`. The operators are equal to this library's by `rfl`
(`fef_convective_eq`, `fef_laplacian_eq`, `fef_div_eq`, `fef_pressureGradient_eq`, `fef_curl_eq`,
`fef_vorticity_eq`, `fef_vorticity_sup_norm_eq`), and the different solution classes are bridged by proved
conversions (`isPeriodicSmoothSolutionOn_of_fefferman`: a solution on `[0, T]` in the Fefferman class is an
sdiff solution on `[0, T)`; `isPeriodicSmoothSolution_of_fefferman` for global solutions). The vendored
modules are covered by the strict axiom audit.

**So the Main Theorem now has exactly one hypothesis, the open Frohmanian tether bound `hclose`.** It is the
whole difficulty: by Beale–Kato–Majda it is as hard as Statement (B). Prodi–Serrin is not used. This is still
a conditional theorem and not a proof of Statement (B) or of the Clay Millennium Problem.

**Converse (not a theorem here).** BKM integrability ⇒ tether bound is true classical mathematics
conditional on three pillars — the Beale–Kato–Majda theorem, uniqueness of classical periodic solutions
(now proved and imported, above), and long-time decay; the other two are not formalized in this library. See the paper, Section 2.1.

**Corrections in 0.1.5** (module `TetherDefinitionAudit`, all kernel-checked): the 0.1.4
`LocalTetherBound`/`LocalFiniteTimeVorticityBound` were constraint-free at times of unbounded vorticity
(junk value `vorticity_sup_norm = 0`; now guarded by `BddAbove`), and the 0.1.4 `LocalTetherRate` is
refuted (`not_forall_localTetherRateV014`: an explicit local solution from `u₀ = 0` has `‖ω(t)‖_∞ = 1/t`), so
the 0.1.4 `frohmanian_tether_theorem` held vacuously. The corrected `LocalTetherRate` uses right
derivatives and holds at zero data (`localTetherRate_zero`). Changed statements: `LocalTetherBound`,
`LocalFiniteTimeVorticityBound`, `LocalTetherRate`, `LocalTetherClosingBound`,
`frohmanian_conditional_regularity_of_closing_bound`, `frohmanian_tether_theorem`; exact diffs in the paper
(Section 3.3) and in [`CERTIFICATE.md`](CERTIFICATE.md).

## Reproduce (one command)

From a fresh clone:

```
git clone https://github.com/BenFrohman/frohmanian-tether-sdiff
cd frohmanian-tether-sdiff
bash scripts/verify.sh        # or: make verify
```

`scripts/verify.sh` installs `elan` if missing (it then installs the toolchain pinned in
`lean-toolchain`, `leanprover/lean4:v4.30.0-rc1`), fetches the Mathlib cache for the revision pinned in
`lake-manifest.json` (Mathlib `v4.30.0-rc1`, rev `0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`), runs
`lake build`, `python3 scripts/check_no_sorry.py`, the strict audit `scripts/AxiomAudit.lean`, and
`scripts/PrintAxioms.lean` (`#print axioms` for the headline theorems), and ends with `VERIFY OK`.
It exits non-zero on any failure. The *Lean certificate* CI workflow runs the same script. Verified
commit and outputs: [`CERTIFICATE.md`](CERTIFICATE.md).

What is formalized:

* The tether kernel `TetherKernel` (a symmetric quadratic metric correction to the Arnold
  Lie–Poisson bracket) and the conditions (C1)–(C3).
* C1 (coadjoint invariance) with the functionals held fixed: **refuted** for the tether under the
  concrete action (`not_tetherKernel_invariant_concrete`, see below). The transported (equivariant)
  form `InvariantUnderTransportedCoadjointAction`, `B(g•ω; F∘g⁻¹, G∘g⁻¹) = B(ω; F, G)`, is **proved**
  for the tether under all translations (`tetherKernel_transported_invariant`, module
  `TetherEquivariantC1`); for rotations and general diffeomorphisms it is open. The two
  hypotheses earlier versions used for it (`SDiffActionHyp.transitive_on_casimir_levels`, refuted,
  and `TetherIntegralPreserved`) were removed together with the C1 theorems (see below).
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
    the earlier core theorem that assumed it was vacuous), the a.e. weight condition over all
    (possibly non-measurable) densities (`TetherWeight.not_aeEnstrophyWeightUnrestricted_tetherKernel`:
    at `ω = 0` the indicator of a Vitali-type set is a density of the tether; so the core theorem
    stated with that form was also vacuous) and `Step1Hyp` (`not_step1Hyp`);
  * proved: the corrected a.e. weight condition `AEEnstrophyWeight TetherKernel` (densities locally
    integrable at regular vorticities): `TetherWeightProof.tetherKernel_aeEnstrophyWeight`. It uses
    the concentrated divergence-free test fields `curl(χ e₂)` of `TestFieldFamily` (`concField x hr`,
    support in `B(x, r)`, any point, any radius), correctors that make test pairs orthogonal to `u`
    without changing `⟨a, b⟩`, and Mathlib's
    `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`. Hence the density and weight inputs of
    `uniqueness_of_minimal_tether_core` hold for `B = T` (`tetherKernel_core_inputs`).
* **Obstruction to damping (proved, conditional on C2):** for every symmetric kernel, C2 forces
  `B(H,M) = B(M,H) = 0` for every functional `M` (`Combined.left_H_zero_of_C2_symm`,
  `Combined.tetherKernel_left_H_zero`). So a symmetric tether that preserved the Euler vector field
  would have damping coefficient 0, and nothing in the geometric layer supplies the rate or
  closing-bound hypotheses.
* `ConcreteSDiff`: a concrete subgroup of measurable, measure- and divergence-preserving
  permutations of ℝ³; `SDiffActionHyp` (now only Casimir invariance) is proved for it
  (`ConcreteSDiff.sdiffActionHyp`). It contains the translations (`ConcreteSDiff.translate`).
* C1 for `TetherKernel` under this concrete action is **refuted**
  (`not_tetherKernel_invariant_concrete`): `InvariantUnderCoadjointAction` keeps the functionals
  fixed, and for the translation by `3e₀` a functional with a kink at `g • ω` has tether `0` at
  `g • ω` but a nonzero tether at `ω`. The transported form holds for translations
  (`tetherKernel_transported_invariant`): the functional gradient is transported by the `L²`
  translation (`functionalDerivative_translate`, via Mathlib's `Lp.compMeasurePreservingₗᵢ`) and
  Biot–Savart commutes with translations (`biotSavart_translate`). Sanity: a point-evaluation kernel
  fails the transported form (`not_transported_invariant_pointEval`), and the fixed form fails on the
  same subgroup (`not_tetherKernel_invariant_transSubgroup`).
* Classical bracket antisymmetry and `{H,H}_cl = 0` (`ArnoldGeometric`), vorticity scaling
  (`ScalingIdentities.vorticity_rescale`). The full tethered bracket is **not** antisymmetric, and no
  Jacobi identity is claimed for it.
* `IsPhysicalNSSolution` was repaired. The old clause `u t = u 0` for `t ≤ 0` forced `∂ₜu(0) = 0`, since
  `deriv` is two-sided. It is now an affine extension: `∃ v₀, ∀ t ≤ 0, u t = u 0 + t • v₀`. Sanity lemma:
  `PhysicalSolutionSanity.exists_physical_time_deriv_ne_zero` gives a physical path with a nonzero time
  derivative at `t = 0`. That path is not a Navier–Stokes solution. The library's nonzero
  Navier–Stokes solutions (constant flows; the shear and ABC flows below) have infinite energy on ℝ³,
  so none of them is in this class.

## Explicit exact solutions (new in 0.1.4, module `ExplicitFlows`)

Coordinates `x = (x₀, x₁, x₂)`. Proved against the library's own `navier_stokes_eq` (all `t ≥ 0`, hence
`NS_PDE` and `NS_PDE_On` for every `T`), for all real parameters:

* Decaying shear `u = e^{-νk²t} (a sin(k x₂), 0, 0)`, pressure `0`: `shearFlow_navier_stokes`,
  `shearFlow_NS_PDE_On`; nonzero for `a ≠ 0`, `k ≠ 0`, `t ≥ 0` (`shearFlow_ne_zero`).
* Decaying ABC flow `u = e^{-νk²t} (A sin kx₂ + C cos kx₁, B sin kx₀ + A cos kx₂, C sin kx₁ + B cos kx₀)`,
  pressure `-|u|²/2` (`abcPressure₀_eq_norm`): `abcFlow_navier_stokes`, `abcFlow_NS_PDE_On`, Beltrami
  property `curl_abcProfile` (`∇ × u = k u`); equal to `e^{-νk²t}(C, A, B)` at the origin, nonzero unless
  `A = B = C = 0` (`abcFlow_ne_zero`).
* One mechanism (`flow_navier_stokes`): `ΔV = -k²V` for trig profiles (`laplacian_trigField`), `div V = 0`,
  `(V·∇)V + ∇p₀ = 0`. The time factor `decay` is continued affinely to `t < 0`, as
  `IsPhysicalNSSolutionOn` requires (`hasDerivAt_decay`, `flow_physical_clauses`).
* With `k = 2πm` both are global smooth `ℤ³`-periodic solutions in the class `IsPeriodicSmoothSolution`
  of `Clay_B_exact`, for these particular data (`shearFlow_isPeriodicSmoothSolution`,
  `abcFlow_isPeriodicSmoothSolution`, `clay_B_instance_shear`, `clay_B_instance_abc`). This is not a step
  toward `Clay_B_exact` and no Clay Millennium claim is made. `PeriodicTetherClosingBound` is not
  discharged even at these data (it quantifies over all local periodic solutions; uniqueness is not
  formalized).
* **They are not Kato witnesses, and none exists for periodic data:** a continuous nonzero
  `ℤ³`-periodic field never has `‖u‖²` integrable on ℝ³ (`not_integrable_sq_of_periodic`), so
  `KatoLocalWitness u₀ ν` is empty for every nonzero periodic `u₀`
  (`isEmpty_katoLocalWitness_of_periodic`, `isEmpty_katoLocalWitness_shear`,
  `isEmpty_katoLocalWitness_abc`). A `kato_witness_shear` cannot be built. At such data
  `LocalTetherBound`, `SmoothPhysicalUniqueness`, `BKMGlobalContinuation` hold only vacuously
  (`*_vacuous_of_periodic`); this is an audit of the encoding, not a discharge.

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
| `h_weight` over all densities (`AEEnstrophyWeightUnrestricted`) | false for the tether; replaced by `AEEnstrophyWeight` (locally integrable densities) | `TetherWeight.not_aeEnstrophyWeightUnrestricted_tetherKernel` |
| global `pde` field of `KatoLocalWitness`, `hcrit`, global-path `hDI` | stronger than Kato's theorem; replaced by the local witness and explicit continuation hypotheses | — |

The main theorems deleted were `tether_coadjoint_invariance`, `Combined.tetherKernel_C1_of_casimir`,
`Combined.tetherKernel_C1_of_volumePreserving`, `Combined.combined_conditional_capstone`,
`tethered_jacobi_identity`, `orbit_eq_casimir_level`, `uniqueness_of_minimal_tether_antisymmetric`,
the stretching estimates at a spatial maximum, and the bridges built on the strain bound. Full list:
`CERTIFICATE.md`. `ConditionalRegularity.frohmanian_tether_theorem` lost its antisymmetric clause and the
hypotheses `hTlb`, `hInt` and `huniq_shift`. `KatoLocalWitness` now asks for the equations only on
its interval `[0, T]`. `frohmanian_tether_theorem` now takes `hKato` (local existence),
`hcont : ∀ u₀ ν, 0 < ν → BKMGlobalContinuation u₀ ν` and `hDI : ∀ u₀ ν, 0 < ν → BddAbove (Set.range fun x => ‖vorticity u₀ x‖) → LocalTetherRate u₀ ν` (0.1.5; in 0.1.4 `hDI` was unsatisfiable).

## Remaining assumptions (explicit hypotheses; no axioms)

* **(b) Classical results not in Mathlib:**
  * `hKato`: a `KatoLocalWitness` (Kato local existence, equations on `[0, T]` only).
  * `BKMGlobalContinuation` (Kato plus Beale–Kato–Majda continuation; the classical theorem uses
    `H^s` data, the library `C^∞ ∩ L²` data on ℝ³).
  * `SmoothPhysicalUniqueness` (uniqueness of smooth solutions on the ℝ³ class `IsLocalPhysicalSolution`;
    only for uniqueness clauses). Not discharged by the uniqueness pillar, which is about the periodic class
    `IsPeriodicSmoothSolutionOn`; the ℝ³ class requires `L²(ℝ³)` and differs.
  * `PeriodicBKMContinuation` (hypothesis `hBKM` of the Main Theorem): **now proved** for every `ν > 0`
    (`FrohmanianTether.Pillars.periodicBKMContinuation_of_classical`, see "Proved pillar: BKM continuation"
    above); `clay_B_exact_of_periodic_tether_closing_bound` needs only `hclose`.
  * `KatoUniquenessOnExistenceTimes` (auxiliary lemmas) and
    `IsCoadjointMotion` for the Euler flow (Arnold).
* **(d) Equivalent in strength to the open problem:**
  * The Frohmanian tether bound `PeriodicTetherClosingBound` (hypothesis `hclose` of the Main Theorem) and its per-datum form `PeriodicTetherBound`.
  * `LocalTetherRate` (cubic rate for `‖ω‖∞` as a right-derivative inequality, 0.1.5).
  * `LocalTetherBound` and `LocalTetherClosingBound` (with bounded vorticity, 0.1.5).
  * `PeriodicDirectionDepletionBound`.
  * The global-path forms `FrohmanianTetherRate`, `FrohmanianTetherBound`,
    `FrohmanianTetherClosingBound` and `RiccatiMajorantExists` (auxiliary lemmas only).

  The tether does not supply any of them.
* **(c) Kernel-class conditions on a competitor `B`** (they define the class): `h_sym`,
  `PolarizesOnDifferentiable B`, `SaturatesTetherQuadratic B`, `h_proj`, `h_density` (a density
  locally integrable at regular vorticities) and `AEEnstrophyWeight B` (locally integrable
  densities), plus C1–C3 for `B` in `uniqueness_of_minimal_tether`.
* **Open for `TetherKernel`:** C2 at regular vorticities (`DegenerateWRTKineticEnergy TetherKernel`,
  assumed in `tetherKernel_left_H_zero`; expected to fail) and transport-invariance under rotations or
  general volume-preserving diffeomorphisms (the geometric push-forward action is not formalized).
  Settled: `AEEnstrophyWeight TetherKernel` proved; fixed-functional C1 refuted; transported C1 for
  translations proved.
* **Hypotheses of auxiliary lemmas only** (re-derived from every theorem binder whose type is a named
  `Prop`; not used by the paper's theorems): `BKMContinuationCriterion`, `BKMContinuationCriterionFor`,
  `LocalExistenceTime`, `SmoothBelowTstar`, `SmoothBelowTstarFor`, `PathBKMIntegrable`, `TstarIsTop`,
  `KatoUniformRestart`, `UniformVorticityCeiling`, `FiniteTimeVorticityBound`,
  `PhysicalUniformVorticityCeiling`, `PhysicalFiniteTimeVorticityBound`, `LocalFiniteTimeVorticityBound`,
  `ClassicalStretchingSource`, `CorrectedMaxRate`, `SymplecticQuarticStretchingSinkAtMax`,
  `Clay_B_exact_with_energy`, `ZeroDerivAlongEnergy`, and the regularity side conditions
  `VorticityTransportRegularity`, `SpatialMaxVorticityEnvelope`, `PeriodicCellPhysicalNSSolution`,
  `VolumePreservingCoadjointAction`.
* The explicit flows discharge none of the hypotheses above (they are vacuous at
  periodic data, see "Explicit exact solutions").

## Mathlib names

New modules use Mathlib declarations directly (`ContDiffBump`, `fderiv`, `ContDiff`, `tsupport`,
`HasCompactSupport`, `LocallyIntegrable`, `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`,
`EuclideanSpace.single`/`PiLp` API, `Lp.compMeasurePreservingₗᵢ`, `integral_add_right_eq_self`,
`Equiv.addRight`, `Subgroup`). `FrohmanianTether/MathlibAgreement.lean` proves (by `rfl`) that the
project-local names `NavierStokes3D.volume`, `pairing`, `eb`, `pd`, `NavierStokes3D.div`, `cross`,
`translate`, `l2Translate`, `Enstrophy` agree with the Mathlib declarations they abbreviate.
Project-local because Mathlib lacks them: curl (`curlVal`), divergence-free fields (`CoadjointOrbit`,
`DivFreeL2`), test directions, the functional gradient, Biot–Savart, `Pi_u`, the tether and (C1)–(C3).
Remaining duplicates, not refactored: `NavierStokes3D.div` (could use the trace of `fderiv`), `Pi_u`
(pointwise formula rather than `Submodule.orthogonalProjection` on `L²`), `IsZ3Periodic` (not stated via
`Function.Periodic`), `ExplicitFlows.kd` (the coordinate of `EuclideanSpace.single i 1`,
`single_apply_kd`). `ExplicitFlows` uses `Real.sin`/`Real.cos`/`Real.exp`, `HasFDerivAt`, `HasDerivAt`,
`contDiff_piLp`, `Real.sin_add_int_mul_two_pi`, `Integrable.measure_norm_ge_lt_top`,
`Measure.addHaar_ball_center`, `Metric.measure_ball_pos`, `measure_iUnion`; its project-local
definitions are `tp`, `tq`, `trigField`, `decay`, `flow`, `flowPressure` and the named profiles/flows.

## Build

`bash scripts/verify.sh` (above) does everything. Step by step:

```
lake exe cache get   # Mathlib v4.30.0-rc1, rev pinned in lake-manifest.json
lake build
python3 scripts/check_no_sorry.py
lake env lean scripts/AxiomAudit.lean
lake env lean scripts/PrintAxioms.lean
```

Build (version 0.1.6, verified commit `4aba751`): 8389 jobs. `python3 scripts/check_no_sorry.py` finds no `sorry`, `admit`, `native_decide` or
`axiom` declaration in the sources. `scripts/AxiomAudit.lean` audits all 2546 declarations in the 42
`FrohmanianTether.*` and 52 vendored `BKMPillar.*` modules, including 1886 theorem constants (1674
stated in the sources, 212 auto-generated equation/congruence/injectivity lemmas), and **fails** if any
depends on an axiom other than `propext`, `Classical.choice`, `Quot.sound` (so `sorryAx` and
`native_decide` are rejected). Toolchain `leanprover/lean4:v4.30.0-rc1`, Mathlib
`0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`. `bash scripts/check_vendor.sh` checks the vendored copy
against upstream. Both checks run in CI (`.github/workflows/certify.yml`; Lean certificate run
43107567565, `VERIFY OK`). Version 0.1.5 (verified commit `5d7c9d0`, before the pillars) was 2797 jobs
and 1101 declarations in 35 modules, including 782 theorem constants. See [`CERTIFICATE.md`](CERTIFICATE.md).

Every hypothesis named above is an explicit Lean argument or a named `Prop`; the repository declares no
axioms. No theorem takes any of the removed hypotheses above, or `KineticEnergyDerivIsVelocity`, as a
hypothesis.

## Contents

* `FrohmanianTether/` — Lean modules (originally extracted from the author's NS_Millennium_Proof
  project, branch `sdiff-abstract-action`, commit `0c9cfdb`; this repository is now standalone).
* `manuscript/main.tex`, `manuscript/main.pdf` — the paper (version 0.1.6 preprint; conditional results). It quotes the Lean statements
  verbatim from `manuscript/lean/`, generated by `python3 scripts/extract_statements.py`; build with
  `cd manuscript && tectonic main.tex`.
* `scripts/verify.sh` (`make verify`) — one-command verification; `scripts/AxiomAudit.lean`,
  `scripts/check_no_sorry.py`, `scripts/PrintAxioms.lean` — the strict audit, source scan and headline
  `#print axioms`.
* `vendor/BKMPillar/` — vendored, namespace-renamed copy of the proved classical-continuation pillar
  (`VENDOR.md`; checked by `bash scripts/check_vendor.sh`).
* `CERTIFICATE.md` — verified commit, toolchain, Mathlib revision and the full axiom report.

## License

Apache 2.0 (see `LICENSE`). Cite via `CITATION.cff` or the Zenodo record of version 0.1.6, [`10.5281/zenodo.24148268`](https://doi.org/10.5281/zenodo.24148268) ([record](https://zenodo.org/records/24148268)); it adds the proved BKM continuation pillar, so the Main Theorem needs only the open tether closing bound, and includes the repaired `FrohmanianTetherRateSmooth` reduction of Fefferman's Problem (A). Earlier: 0.1.5 [`10.5281/zenodo.24122596`](https://doi.org/10.5281/zenodo.24122596) (Main Theorem framing, tether ⇒ BKM integrability, definition audit and corrected local hypotheses); 0.1.4 [`10.5281/zenodo.24120781`](https://doi.org/10.5281/zenodo.24120781) (module `ExplicitFlows`), 0.1.3 [`10.5281/zenodo.24102715`](https://doi.org/10.5281/zenodo.24102715) (DOI-only update of 0.1.2), 0.1.2 [`10.5281/zenodo.24102345`](https://doi.org/10.5281/zenodo.24102345). All versions: concept DOI [`10.5281/zenodo.24081999`](https://doi.org/10.5281/zenodo.24081999). The archive [`10.5281/zenodo.24082000`](https://doi.org/10.5281/zenodo.24082000) ([record](https://zenodo.org/records/24082000)) is version 0.1.1, which still contains the removed hypothesis `KineticEnergyDerivIsVelocity`.

## Copyright

© 2026 Benjamin Stanley Frohman.
