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
* `hKato` — for every smooth, divergence-free, finite-energy datum a `KatoLocalWitness`.
  CAUTION: as encoded, a `KatoLocalWitness` carries a path solving the equations pointwise for
  ALL `t ≥ 0` (smooth only on `[0, T]`), so `hKato` is stronger than Kato's local theorem; it
  assumes existence of a (possibly non-smooth after `T`) physical solution for all time.
* `hDI : ∀ u₀ ν, FrohmanianTetherRate u₀ ν` — the cubic rate `M' ≤ C M² − κ'' M³` for
  `M(t) = ‖ω(t)‖_∞` along every physical solution. OPEN; at least as strong as a time-uniform
  vorticity bound, hence (by BKM) as hard as the regularity problem itself.
* `hcrit` — the Beale–Kato–Majda continuation criterion (classical, not formalized).
* `huniq` — uniqueness of smooth physical solutions on existence intervals (classical, not
  formalized).

Conclusion: (1) the density-form characterization of `TetherKernel` (substitution); (2) global
smoothness of the witness path.

**Changes (Nov 2026).** The former clause "every ANTISYMMETRIC `B` satisfying C1–C3,
saturation and polarization equals `TetherKernel`" was removed: its hypotheses force
`B = TetherKernel = 0` (`FrohmanianTether.antisymmetric_clause_forces_zero`). The former
binders `τ`, `hTlb` (one Kato existence time `τ` for ALL data), `hInt`, `huniq_shift` (the
quantitative-restart route) were removed; continuation now goes through `hcrit` (BKM) as in
`conditional_regularity_of_open_hyps`. The former first clause ("the tethered bracket
reproduces the classical one on `H`") was removed earlier: its hypothesis `δH/δω = u` is false
(`KineticEnergyDerivative.not_forall_functionalDerivative_kineticEnergy_eq_velocity`). -/
public theorem frohmanian_tether_theorem
    (hKato : ∀ u₀ ν, ContDiff ℝ (⊤ : ℕ∞) u₀ → (∀ x, div u₀ x = 0) →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) → 0 < ν →
      KatoLocalWitness u₀ ν)
    (hDI : ∀ u₀ ν, FrohmanianTetherRate u₀ ν)
    (hcrit : ∀ u₀ ν, TetheredLyapunov.PhysicalBKMContinuationCriterionFor u₀ ν)
    (huniq : ∀ u₀ ν (w : KatoLocalWitness u₀ ν),
      TetheredLyapunov.KatoUniquenessOnExistenceTimes u₀ ν w) :
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
    let w := hKato u₀ ν hsm hdiv hE hνpos
    have hceil : PhysicalUniformVorticityCeiling u₀ ν := by
      intro u p hNS hu0 hphys
      obtain ⟨C, κ'', hC, hκ, hd, hdd, hc, _⟩ := hDI u₀ ν u p hνpos hNS hu0 hphys
      exact riccati_ceiling_of_vorticity_di u C κ'' hC hκ hd hdd hc
    exact ⟨w.u, w.p, conditional_regularity_of_bkm_uniqueness u₀ ν hνpos w
      (physicalFiniteTimeVorticityBound_of_uniform hceil) (hcrit u₀ ν) (huniq u₀ ν w)⟩

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

`hRiccati : FrohmanianTetherBound (u0 0) ν` is a time-uniform bound on `‖ω‖_∞`.
It is open; by BKM it is equivalent in difficulty to regularity itself
(see `ClayStatements.lean`, `FrohmanianTetherClosingBound`). Given it, plus the
classical local-theory binders `w`, `hcrit` (BKM continuation criterion), `huniq`, every smooth, divergence-free
initial field generates a unique global smooth solution. Not an unconditional Clay solution.

This is the top-level statement whose proof proceeds via the Frohmanian Symplectic Tether
(the 5-step uniqueness + tethered Lyapunov + independent majorant + BKM upgrade).
-/
public theorem conditional_regularity_of_open_hyps
    (u0 : TimeDependentVelocity)
    (h_div_free : ∀ t x, div (u0 t) x = 0)
    (h_smooth : IsSmooth (u0 0))
    (h_finite_energy : Integrable (fun x : T3 => ‖u0 0 x‖ ^ 2))
    (ν : ℝ) (h_ν_pos : ν > 0)
    (w : KatoLocalWitness (u0 0) ν)
    (hRiccati : FrohmanianTetherBound (u0 0) ν)
    (hcrit : TetheredLyapunov.PhysicalBKMContinuationCriterionFor (u0 0) ν)
    (huniq : TetheredLyapunov.KatoUniquenessOnExistenceTimes (u0 0) ν w) :
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
  obtain ⟨hNS, hu0, hsm, hnn, _hdiv⟩ :=
    TetheredLyapunov.conditional_regularity_of_bkm_uniqueness (u0 0) ν h_ν_pos
      w (TetheredLyapunov.physicalFiniteTimeVorticityBound_of_uniform
          (TetheredLyapunov.physicalUniformVorticityCeiling_of_tetherBound hRiccati))
      hcrit huniq
  refine ⟨w.u, hsm, hu0, ?ns, hnn, ?uniq⟩
  · intro _t _ht
    exact ⟨w.phys, w.p, hNS⟩
  · intro v hsmv hv0 hNSv t ht
    obtain ⟨hphys_v, q, hq⟩ := hNSv 0 le_rfl
    have ht1 : 0 < t + 1 := by linarith
    have hmem : t + 1 ∈ existenceTimes (u0 0) ν :=
      mem_existenceTimes (u0 0) ν ht1 v q hv0 hq (fun s hs => hsmv s hs.1) hphys_v
    exact (huniq (t + 1) v q hmem hv0 hq (fun s hs => hsmv s hs.1) hphys_v
      t ⟨ht, le_of_lt (lt_add_one t)⟩).symm

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
