/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.SymplecticTether
public import FrohmanianTether.TetheredLyapunov
public import FrohmanianTether.Uniqueness
public import FrohmanianTether.IndependentMajorant
public import FrohmanianTether.ArnoldGeometric
public import FrohmanianTether.NS_Equations
public import FrohmanianTether.AnalyticPipeline
public import Mathlib.Analysis.Calculus.ContDiff.Basic

-- NOTE (post-bumper-rails phase): All silencing options removed. Warnings for classical `sorry`s
-- (pin weakenings and assembly) are now visible. Full convention documented in TetheredLyapunov.lean.

-- Error Explanations (Lean Language Reference) — Assembly Layer
-- This file historically contained the last 7 hard errors (custom unicode-in-identifier notation,
-- ambiguous CoadjointOrbit export, ContDiff ∞ syntax, vorticity_L references). All were fixed
-- in the "priority 2" work (clean ASCII identifiers, open hygiene with `hiding`, granular
-- ContDiff import, alignment to the 6-arg schematic conditional_regularity signature).
-- The full Error Explanations table integration (this session) confirms that the current state
-- avoids every row:
-- • synthInstanceFailed / unknownIdentifier / invalidDottedIdent / invalidField: eliminated by
--   the notation cleanup and the explicit `open ArnoldGeometric hiding CoadjointOrbit`.
-- • inferBinderTypeFailed: the schematic theorems (frohmanian_tether_theorem,
--   conditional_regularity_of_open_hyps) now have fully explicit 6-arg signatures matching the author
--   abstract; all binders are elaborated before bodies.
-- • dependsOnNoncomputable: top-level theorems that use choice (Gâteaux representative,
--   Biot–Savart integrals, Riccati solution) are marked `noncomputable` or live in
--   a noncomputable context.
-- • projNonPropFromProp / propRecLargeElim: C1–C3 and smoothness are real `Prop`s
--   (`ContDiff`, `Integrable`, degeneracy, feedback), never `True` gates.
-- • redundantMatchAlt / inductionWithNoAlts: none present.
-- • ctor* / inductiveParam*: no new inductives declared here.
-- The assembly point deliberately stays thin (it only wires Layer 1 geometric justification
-- to Layer 2 analytic continuation). This keeps the error surface minimal and makes the
-- "unique proof confirmation" property easy to audit: any future green proof of the novel
-- geometry will be visibly the one that satisfies the author abstract's ∃! form.
-- Cross-ref: all prior reference blocks (especially §5 module hygiene and the ConditionalRegularity
-- cleanup that removed the last hard errors) are still in force.

/-! # Global Regularity: Final Integration and the Frohmanian Symplectic Tether Theorem

This module assembles everything and states the main theorem exactly as
formulated in the audited LaTeX (including the three parts of Theorem 2.1
and the corollary from the PASS 5 argument, which is **conditional**: see below).

The top-level statement below is the exact Abstract formulation supplied by the author
(Sections 1 + overall theorem), using the Frohmanian Symplectic Tether as the central device.
-/

namespace ConditionalRegularity

open FrohmanianTether TetheredLyapunov
open ArnoldGeometric hiding CoadjointOrbit
open ArnoldGeometric (CoadjointOrbit)
open NavierStokes3D MeasureTheory
-- FrohmanianTether ns (containing uniqueness_of_minimal_tether) is qualified below to avoid
-- "unknown namespace" during module elaboration (the export in root makes it available at top level).

/-! ## Main Theorem — Frohmanian Symplectic Tether Theorem -/

/-- High-level statement of the full theorem — **conditional**. NOT a proof of regularity.

Hypotheses (each explicit; none is proved here):
* `hKato` — for every admissible datum a `KatoLocalWitness`: a smooth physical solution on a
  short interval `[0, T]` (equations demanded on `[0, T]` only). Category (b), Kato 1972, with
  the same `H^s` data-class caveat.
* `hcont : ∀ u₀ ν, BKMGlobalContinuation u₀ ν` — category (b), classical (Kato local existence +
  uniqueness + Beale–Kato–Majda continuation), not formalized; CAVEAT: the library's data class
  is wider than Kato's `H^s`.
* `hDI : ∀ u₀ ν, LocalTetherRate u₀ ν` — category (d), OPEN: the cubic rate
  `M' ≤ C M² − κ'' M³` for `M(t) = ‖ω(t)‖_∞`, with constants chosen before the interval, along
  every smooth physical solution on every finite interval. It implies a time-uniform ceiling
  (`localTetherBound_of_localTetherRate`, via the finite-interval comparison
  `comparison_ode_stability_Icc`), hence by BKM it is as hard as regularity itself.

Conclusion: (1) the density-form characterization of `TetherKernel` (substitution); (2) a global
smooth physical solution for every admissible datum.

**Changes (Nov 2026).** `KatoLocalWitness` now demands the equations only on its interval, so it
no longer supplies a global path; the binders `hcrit`, `huniq` were replaced by the explicit
continuation hypothesis `hcont`, and the rate hypothesis `hDI` now ranges over local
solutions (`LocalTetherRate`). The former antisymmetric clause was removed earlier (its
hypotheses force `B = TetherKernel = 0`). -/
public theorem frohmanian_tether_theorem
    (hKato : ∀ u₀ ν, ContDiff ℝ (⊤ : ℕ∞) u₀ → (∀ x, div u₀ x = 0) →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) → 0 < ν →
      KatoLocalWitness u₀ ν)
    (hcont : ∀ u₀ ν, TetheredLyapunov.BKMGlobalContinuation u₀ ν)
    (hDI : ∀ u₀ ν, TetheredLyapunov.LocalTetherRate u₀ ν) :
  ∃ (𝔗_F : CoadjointOrbit → Functional → Functional → ℝ),
    (∀ (B : CoadjointOrbit → Functional → Functional → ℝ)
      (α : CoadjointOrbit → T3 → ℝ),
      HasTetherKernelDensity B α →
      (∀ ω x, α ω x = canonicalTetherDensity ω x) →
      ∀ ω F G, B ω F G = 𝔗_F ω F G) ∧
    (∀ (u₀ : VelocityField) (ν : ℝ),
      0 < ν →
      (∀ x, div u₀ x = 0) →
      ContDiff ℝ (⊤ : ℕ∞) u₀ →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) →
      ∃ (u : ℝ → VelocityField) (p : ℝ → PressureField),
        NS_PDE u p ν ∧
        u 0 = u₀ ∧
        (∀ t ≥ (0 : ℝ), ContDiff ℝ (⊤ : ℕ∞) (u t)) ∧
        (∀ t ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u t)) ≥ 0) ∧
        (∀ t ≥ (0 : ℝ), ∀ x, div (u t) x = 0)) := by
  refine ⟨TetherKernel, ?_, ?_⟩
  · intro B α hrepr hα ω F G
    exact uniqueness_of_kernel_density B α hrepr hα ω F G
  · intro u₀ ν hνpos hdiv hsm hE
    obtain ⟨u, p, hNS, hu0, hsm, -, hnn, hdiv⟩ :=
      TetheredLyapunov.conditional_regularity u₀ ν (hKato u₀ ν hsm hdiv hE hνpos) (hcont u₀ ν)
        (TetheredLyapunov.localTetherBound_of_localTetherRate (hDI u₀ ν))
    exact ⟨u, p, hNS, hu0, hsm, hnn, hdiv⟩

/-! ## Abstract (exact formulation supplied by the author) -/

open NavierStokes3D

/-- IsSmooth is the classical notion of infinite differentiability (black-box via ContDiff). -/
public abbrev IsSmooth (f : VelocityField) : Prop := ContDiff ℝ (⊤ : ℕ∞) f

/-- Sup-norm (L^∞) of a vorticity field (classical, black-box, using clean ASCII name to avoid
unicode identifier issues in the current Lean/mathlib pin).
Still exactly matches the abstract intent: a classical sup-norm proxy for |ω|_{L^∞} used in BKM-type criteria.

Marked noncomputable because it depends on Real.instSupSet (standard for sup-norm proxies in analysis). -/
public noncomputable def vorticity_sup_norm (ω : VorticityField) : ℝ :=
  NavierStokes3D.vorticity_sup_norm ω

-- Clean alias (no custom unicode notation) provided so that references in comments / the abstract
-- theorem can mention the L^∞ control without triggering parser/elaboration problems.
noncomputable abbrev vorticity_sup_norm_proxy (ω : VorticityField) : ℝ := vorticity_sup_norm ω

/-- The solution satisfies the unmodified 3D incompressible Navier–Stokes equations
and is physically admissible (`IsPhysicalNSSolution u`). -/
public def satisfies_NavierStokes (u : TimeDependentVelocity) (ν : ℝ) : Prop :=
  IsPhysicalNSSolution u ∧ ∃ p : TimeDependentPressure, navier_stokes_eq u p ν

/-- Main theorem (Abstract, formalized) — **conditional on `hRiccati`**.

`hRiccati : LocalTetherBound (u0 0) ν` is one `‖ω‖_∞` ceiling along every smooth physical
solution on every finite interval (category (d), OPEN; by BKM as hard as regularity itself).
the Kato witness `w`, `hcont : BKMGlobalContinuation (u0 0) ν` (BKM continuation) and
`huniq : SmoothPhysicalUniqueness (u0 0) ν` are category (b): classical, not formalized.
Given them, the datum generates a unique global smooth physical solution. Not an unconditional
Clay solution. -/
public theorem conditional_regularity_of_open_hyps
    (u0 : TimeDependentVelocity)
    (_h_div_free : ∀ t x, div (u0 t) x = 0)
    (_h_smooth : IsSmooth (u0 0))
    (_h_finite_energy : Integrable (fun x : T3 => ‖u0 0 x‖ ^ 2))
    (ν : ℝ) (_h_ν_pos : ν > 0)
    (w : KatoLocalWitness (u0 0) ν)
    (hcont : TetheredLyapunov.BKMGlobalContinuation (u0 0) ν)
    (hRiccati : TetheredLyapunov.LocalTetherBound (u0 0) ν)
    (huniq : TetheredLyapunov.SmoothPhysicalUniqueness (u0 0) ν) :
  ∃ (u : TimeDependentVelocity),
    (∀ t ≥ (0 : ℝ), IsSmooth (u t)) ∧
    (u 0 = u0 0) ∧
    (∀ t ≥ (0 : ℝ), satisfies_NavierStokes u ν) ∧
    (∀ t ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u t)) ≥ 0) ∧
    (∀ v : TimeDependentVelocity,
      (∀ t ≥ (0 : ℝ), IsSmooth (v t)) →
      v 0 = u0 0 →
      (∀ t ≥ (0 : ℝ), satisfies_NavierStokes v ν) →
      ∀ t ≥ (0 : ℝ), v t = u t) := by
  obtain ⟨u, p, hNS, hu0, hsm, hphys, hnn, _hdiv⟩ :=
    TetheredLyapunov.conditional_regularity (u0 0) ν w hcont hRiccati
  refine ⟨u, hsm, hu0, fun _ _ => ⟨hphys, p, hNS⟩, hnn, ?uniq⟩
  intro v hsmv hv0 hNSv t ht
  obtain ⟨hphys_v, q, hq⟩ := hNSv 0 le_rfl
  exact TetheredLyapunov.global_solutions_eq_of_uniqueness huniq hv0 hq hsmv hphys_v
    hu0 hNS hsm hphys t ht

-- Finite kinetic energy of the initial field. Mathlib's `Integrable f` is
-- `AEStronglyMeasurable f ∧ HasFiniteIntegral f`. An earlier encoding wrote
-- `HasFiniteIntegral (fun t => u0 t • x) vol`: that is the finite-integral
-- conjunct of the same energy hypothesis, but it mixed the time variable into
-- a spatial density and did not type as `∫ ‖u₀‖²`. The hypothesis here is the
-- classical Kato/Leray L² energy at `t = 0`, identical to `local_existence`
-- and `frohmanian_tether_theorem`. One statement, one energy condition;
-- not a second theorem. On `T³`, smooth data are automatically integrable;
-- the binder is kept because Kato's theorem is classically stated in L².
-- The L^∞ bound on vorticity is the quantity controlled by the tether + majorant.

/-!
# Validating a Lean Proof — Integration of the Lean Language Reference

This block was added during the systematic reference-integration campaign upon receipt of the
full "Validating a Lean Proof" section (escalating checks: blue double ticks → #print axioms →
lean4checker --fresh → gold-standard comparator + external checkers).

The section is of the *highest* importance for this project because:
- The central claim (global regularity via the novel Frohmanian Symplectic Tether) is a
  high-stakes mathematical result (Clay Millennium Problem territory).
- The user has repeatedly emphasized the desire for "unique proof confirmation".
- Remaining `sorry`s are untranscribed paper steps in this authorship, not
  community fill-ins. Transparent validation hygiene is therefore essential.

Current toolchain (as of this session): `leanprover/lean4:v4.28.0`
(This is exactly the version the user requested we retain, matching Terence Tao’s Analysis I
repository pin. On 4.28.0 the older `Lean.trustCompiler` mechanism is still active for any
native evaluation. See the dedicated subsection below.)

## The Four Escalating Levels of Validation (directly from the reference)

1. **Blue Double Check Marks (everyday interactive use)**
   - What it means: The theorem elaborated successfully and the kernel accepted a proof term
     constructed from the definitions, theorems, and axioms in scope.
   - Current status for this project: Once the remaining schematic `sorry`s inside the novel
     geometry (especially the six named sub-haves in `h_cyclic_integrand_zero` in SymplecticTether)
     and the classical black boxes are filled or properly cited, the blue ticks will appear on
     `conditional_regularity_of_open_hyps` and `frohmanian_tether_theorem`.
   - Protection: incomplete proofs, explicit `sorry` in the *current* theorem, honest tactic bugs.
   - Limitation: does *not* detect `sorry` or incomplete proofs in dependencies.

2. **#print axioms thmName**
   - What it means: Lists every axiom the theorem (and everything it depends on) relies upon.
   - Expected output on a finished proof of the novel geometry:
       `propext`, `Classical.choice`, `Quot.sound`
     (the three standard axioms of Lean's logic — benign).
   - Any appearance of `sorryAx` → the theorem or a dependency uses `sorry` or is incomplete.
   - Any appearance of `Lean.trustCompiler` (on 4.28.0) → native evaluation was used somewhere
     in the dependency chain (see dedicated note below).
   - Any other custom axiom → the result is only valid relative to the soundness of that axiom.
   - **Action taken in this file**: concrete `#print axioms` commands are placed immediately after
     the two top-level schematic theorems (see below).

3. **lean4checker --fresh**
   - Replays the proofs stored in the `.olean` files through the kernel.
   - Catches a small class of bugs in Lean's core handling of kernel state and simple attacks
     that bypass the elaborator.
   - Recommended as part of CI (the lean-action GitHub Action supports `lean4checker: true`).
   - Limitation: still trusts the structural integrity of the `.olean` files themselves.

4. **Gold Standard: comparator + external checkers (nanoda, etc.)**
   - For high-risk scenarios (proof marketplaces, high-reward competitions, unaligned AI,
     or when one wants protection against seriously malicious proof attempts that try to
     compromise how Lean interprets a statement).
   - Builds in a sandbox, exports the proof term to a serialized format, then validates
     *outside* the sandbox using both Lean's kernel *and* independent external checkers.
   - This is the level that would give the strongest "unique proof confirmation" for the
     novel Frohmanian geometry (the 5-step canonicity + explicit Jacobi identity on F_p).
   - Requires that the proof avoid `Lean.trustCompiler` / native evaluation on 4.28.0
     (external checkers have no access to the Lean compiler).

## On Lean.trustCompiler (relevant because we are pinned to 4.28.0)

The project is deliberately kept on `v4.28.0` (per the user's explicit request, matching the
pin used in Terence Tao’s Analysis I formalization repository).

On this version:
- Any use of `decide +native`, `bv_decide`, or direct `Lean.ofReduceBool` introduces the axiom
  `Lean.trustCompiler`.
- External checkers (lean4checker with --fresh, comparator + nanoda) *cannot* replay such proofs.
- The reference is clear: "When that level of checking is needed, proofs have to avoid using
  native evaluation."

**Project policy for validation levels (honest vs. malicious context)**

- Classical black-box infrastructure (local existence, BKM, parabolic regularity, CZ estimates,
  transport/Young/Hölder algebra, ODE comparison, etc.) may freely use any convenient tactics,
  including native evaluation, during development. These are documented with citations and
  will eventually be replaced by citations to mathlib or small ForMathlib lemmas.
- The *novel geometric core* (everything in SymplecticTether.lean: TetherKernel definition,
  the atomic canonicity lemmas, degeneracy proofs,
  invariance, etc.) **must eventually be free of native evaluation** if we ever wish to subject
  the final artifact to comparator + external checkers for the strongest possible assurance.
- The analytic layer in TetheredLyapunov (majorant ODE, differential inequality, Lemma 3.1
  continuation) sits in the middle: the independent-majorant construction itself is pure
  mathematics and should be kernel-checkable; heavy numerical or decision-procedure work
  inside classical inequalities can stay native if clearly marked.

This distinction directly supports the four living audit checklists (especially Non-Circularity
and Canonicality) and the two-layer architecture.

## Current Honest Development State (rails off)

As long as classical black-box `sorry`s remain inside `conditional_regularity_of_open_hyps`,
`frohmanian_tether_theorem`, or any lemma they depend on, `#print axioms` will
report `sorryAx`. This is *expected and visible*.

The presence of `sorryAx` is not a bug in the formalization strategy; it is the
honest signal that remaining paper steps are still being transcribed in this
authorship. There is no open task list for anyone else to fill.

When those steps are transcribed, the only axioms that should remain for the
novel claims are `propext`, `Classical.choice`, and `Quot.sound`.

## Concrete Commands (live in this file)

After the two main theorems you will find:

    #print axioms frohmanian_tether_theorem
    #print axioms conditional_regularity_of_open_hyps

Run these (or `lake build` followed by inspecting the output) to see the current axiom
surface. As the proof matures, these commands become part of the permanent validation
ritual.

See the new "Validation and Trust Strategy" section in Blueprint.md for the full mapping of
these four levels onto the project's novel geometry and the goal of unique proof confirmation.
-/

#print axioms frohmanian_tether_theorem
#print axioms conditional_regularity_of_open_hyps

end ConditionalRegularity
