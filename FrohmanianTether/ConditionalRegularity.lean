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

/-! # Conditional statements: assembly of the tether layer and the analytic layer

This module states `frohmanian_tether_theorem` and `conditional_regularity_of_open_hyps`. Both are
**conditional implications**: every analytic input (Kato local existence, Kato–BKM continuation,
uniqueness, and a local-solution rate or bound as strong as the open problem) is an explicit
hypothesis. Nothing here proves global regularity of the 3D Navier–Stokes equations.
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
-- The L^∞ bound on vorticity is supplied only by the explicit hypothesis `hRiccati`
-- (the tether does not supply it).

#print axioms frohmanian_tether_theorem
#print axioms conditional_regularity_of_open_hyps

end ConditionalRegularity
