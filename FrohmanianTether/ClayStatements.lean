/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.ConditionalRegularity
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Clay Millennium Problem: Official Statements and the Closing Bound (OPEN TARGETS)

Official statement: Charles L. Fefferman, "Existence and Smoothness of the Navier–Stokes
Equation", Clay Mathematics Institute, 2000.

**Everything in the "open targets" sections below is a `def … : Prop`.** None is an axiom,
none is a `sorry`'d theorem, and none is assumed by any theorem in the default build except
as an explicit, visible hypothesis. They record what is *not* proved.

Domain note. The model space `T3` of this development is `EuclideanSpace ℝ (Fin 3)` (that
is, ℝ³ at the type level). Clay (A) is stated on it directly. Clay (B) is stated on it with
the unit-period condition in each coordinate direction, which is Fefferman's formulation (8)
of the periodic problem. Smoothness here is `ContDiff ℝ (⊤ : ℕ∞)` (C^∞), jointly in `(t, x)` on
`[0, ∞) × ℝ³`, as in Fefferman (6)/(11). The rest of the library also writes
`ContDiff ℝ (⊤ : ℕ∞)`, i.e. C^∞ (the coercion of `⊤ : ℕ∞`; the bare `⊤ : WithTop ℕ∞`
would mean real-analytic C^ω, which an earlier version used by mistake).
-/

open NavierStokes3D MeasureTheory FrohmanianTether
open scoped ContDiff

namespace FrohmanianTether.ClayStatements

/-! ## Open target: the closing bound (Task: what would make the result unconditional) -/

/-- **Frohmanian tether closing bound** (OPEN). For every viscosity-`ν` datum in the class
consumed by `conditional_regularity_of_open_hyps`, the Frohmanian tether bound holds: every solution
from it has `‖ω(τ)‖_∞` bounded uniformly in `τ ≥ 0`.

Scaling: `‖ω‖_∞ ↦ λ² ‖ω‖_∞` under `u_λ(x,t) = λ u(λx, λ²t)`, and `sup_t` is
scale-neutral, so the bound is *supercritical*; its time-integrated form
`∫₀^T ‖ω‖_∞ dt < ∞` (Beale–Kato–Majda) is the critical one. By BKM and the decay of
Leray solutions, this bound for all data is equivalent to global regularity, so proving it
is the Millennium Problem itself, not a reduction of it. -/
@[expose] public def FrohmanianTetherClosingBound (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField,
    (∀ x, div u₀ x = 0) → ContDiff ℝ (⊤ : ℕ∞) u₀ →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) →
        FrohmanianTetherBound u₀ ν

/-- **BKM closing criterion** (OPEN). Along every solution from admissible data, the
vorticity supremum is integrable on every `[0, T]`: `∫₀ᵀ ‖ω(t)‖_∞ dt < ∞`.

Mathematical statement of the minimal closing fact: for smooth divergence-free finite-energy
`u₀` and the solution `u`, `∫₀ᵀ ‖ω(t)‖_{L^∞} dt < ∞` for every `T`. By Beale–Kato–Majda this
is equivalent to no blow-up on `[0, T]`. Relation to the classical criteria (each sufficient
for regularity, each open for general data):
* BKM: `ω ∈ L¹_t L^∞_x` — scale-invariant (critical).
* Prodi–Serrin–Ladyzhenskaya: `u ∈ L^p_t L^q_x`, `2/p + 3/q ≤ 1`, `3 < q ≤ ∞` — critical.
* Escauriaza–Seregin–Šverák: `u ∈ L^∞_t L³_x` — critical endpoint.
* Constantin–Fefferman: Lipschitz control of `ξ = ω/|ω|` where `|ω|` is large — scale-invariant
  geometric condition.
All are a-priori bounds on a critical quantity, while the energy gives only supercritical
control; that gap is the Millennium Problem, so this Prop is as hard as Clay (A).
`vorticity_sup_norm` is a real `iSup` (`0` on unbounded ranges), so the criterion also
requires `BddAbove` of `x ↦ ‖ω(t,x)‖` at each `t ≥ 0`; it cannot be met by unbounded fields. -/
public def BKMClosingCriterion (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField,
    (∀ x, div u₀ x = 0) → ContDiff ℝ (⊤ : ℕ∞) u₀ →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) →
        ∀ u : ℝ → VelocityField, ∀ p : ℝ → PressureField,
          NS_PDE u p ν → u 0 = u₀ → IsPhysicalNSSolution u → ∀ T : ℝ,
            IntervalIntegrable (fun t => vorticity_sup_norm (vorticity (u t))) volume 0 T ∧
              ∀ t ≥ (0 : ℝ), BddAbove (Set.range fun x => ‖vorticity (u t) x‖)

/-- **Proved.** The (open) Frohmanian closing bound implies the (open) BKM criterion. -/
public theorem bkm_of_closing_bound {ν : ℝ} (h : FrohmanianTetherClosingBound ν) :
    BKMClosingCriterion ν := by
  intro u₀ hdiv hsm hE u p hNS h0 hphys T
  obtain ⟨_, _, hcont, hbdd⟩ := h u₀ hdiv hsm hE u p hNS h0 hphys
  exact ⟨hcont.intervalIntegrable 0 T, hbdd⟩

/-! ## Open targets: Clay (A) and (B), Fefferman's statements -/

/-- **Clay (A)** (OPEN): existence and smoothness on ℝ³, force `f = 0`.
For `ν > 0` and any smooth divergence-free `u⁰` with
`|∂_x^α u⁰(x)| ≤ C_{αK} (1 + |x|)^{-K}` (Fefferman (4)), there are smooth `u, p` on
`[0,∞) × ℝ³` solving (1)–(3) with bounded energy `∫ |u(x,t)|² dx < C` (Fefferman (7)).
The decay condition is stated for every derivative order `k` via `iteratedFDeriv`. -/
public def Clay_A : Prop :=
  ∀ (ν : ℝ) (u₀ : VelocityField),
    0 < ν →
    ContDiff ℝ (⊤ : ℕ∞) u₀ →
    (∀ x, div u₀ x = 0) →
    (∀ k K : ℕ, ∃ C : ℝ, ∀ x : T3,
      ‖iteratedFDeriv ℝ k u₀ x‖ ≤ C / (1 + ‖x‖) ^ K) →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × T3 => p q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
      navier_stokes_eq u p ν ∧
      u 0 = u₀ ∧
      ∃ E : ℝ, ∀ t ≥ (0 : ℝ),
        Integrable (fun x : T3 => ‖u t x‖ ^ 2) ∧ ∫ x, ‖u t x‖ ^ 2 ≤ E

/-- **Clay (B)** (OPEN): existence and smoothness on ℝ³/ℤ³, force `f = 0`.
For `ν > 0` and any smooth divergence-free `u⁰` of period 1 in each coordinate
(Fefferman (8)), there are smooth `u, p` on `[0,∞) × ℝ³`, of period 1 in `x`
(Fefferman (10)), solving (1)–(3) (Fefferman (11)).

**Deprecated in favour of `Clay_B_exact`.** Differences: (a) here `∂ₜ` is the two-sided
`deriv` inside `navier_stokes_eq`, so the equation at `t = 0` depends on `u` for `t < 0`;
`Clay_B_exact` uses the one-sided `derivWithin … (Set.Ici 0)`; (b) periodicity here is the
unit-shift form, there the `ℤ³` form (equivalent: `isZ3Periodic_iff_unit_shifts`);
(c) `u₀`'s pressure erratum and the force slot `f` are explicit there. Kept for reference. -/
public def Clay_B : Prop :=
  ∀ (ν : ℝ) (u₀ : VelocityField),
    0 < ν →
    ContDiff ℝ (⊤ : ℕ∞) u₀ →
    (∀ x, div u₀ x = 0) →
    (∀ (j : Fin 3) (x : T3), u₀ (x + EuclideanSpace.single j 1) = u₀ x) →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × T3 => p q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
      navier_stokes_eq u p ν ∧
      u 0 = u₀ ∧
      ∀ t ≥ (0 : ℝ), ∀ (j : Fin 3) (x : T3),
        u t (x + EuclideanSpace.single j 1) = u t x ∧
        p t (x + EuclideanSpace.single j 1) = p t x

/-! ## Proved: the closing bound feeds the Frohmanian assembly -/

/-- **Proved (no `sorry`, standard axioms only).** If the open closing bound held, then,
together with the classical local-theory binders already used by
`conditional_regularity_of_open_hyps` (Kato witness `hKato`, BKM continuation criterion `hcrit`,
uniqueness `huniq`), *every* datum in the library's class would have a unique global
solution, smooth (`ContDiff ℝ (⊤ : ℕ∞)`) at every `t ≥ 0`.

This is the exact sense in which `conditional_regularity_of_open_hyps` plus the closing bound
"yields" global regularity. It does **not** yet yield `Clay_A` or `Clay_B`: the library
treats C^∞ data (`ContDiff ℝ (⊤ : ℕ∞)`) on `T3` but has no periodicity or decay hypotheses, gives
smoothness in `x` at each time rather than jointly in `(t, x)`, and gives no uniform
energy bound. Those bridges are not formalized. -/
public theorem frohmanian_conditional_regularity_of_closing_bound
    (ν : ℝ) (hν : 0 < ν)
    (hclose : FrohmanianTetherClosingBound ν)
    (hKato : ∀ u₀ : VelocityField, ContDiff ℝ (⊤ : ℕ∞) u₀ → (∀ x, div u₀ x = 0) →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) → KatoLocalWitness u₀ ν)
    (hcrit : ∀ u₀ : VelocityField, TetheredLyapunov.PhysicalBKMContinuationCriterionFor u₀ ν)
    (huniq : ∀ (u₀ : VelocityField) (w : KatoLocalWitness u₀ ν),
      TetheredLyapunov.KatoUniquenessOnExistenceTimes u₀ ν w)
    (u₀ : VelocityField) (hdiv : ∀ x, div u₀ x = 0) (hsm : ContDiff ℝ (⊤ : ℕ∞) u₀)
    (hE : Integrable (fun x : T3 => ‖u₀ x‖ ^ 2)) :
    ∃ (u : TimeDependentVelocity),
      (∀ t ≥ (0 : ℝ), ConditionalRegularity.IsSmooth (u t)) ∧
      (u 0 = u₀) ∧
      (∀ t ≥ (0 : ℝ), ConditionalRegularity.satisfies_NavierStokes u ν) ∧
      (∀ t ≥ (0 : ℝ), ConditionalRegularity.vorticity_sup_norm (vorticity (u t)) ≥ 0) ∧
      (∀ v : TimeDependentVelocity,
        (∀ t ≥ (0 : ℝ), ConditionalRegularity.IsSmooth (v t)) →
        v 0 = u₀ →
        (∀ t ≥ (0 : ℝ), ConditionalRegularity.satisfies_NavierStokes v ν) →
        ∀ t ≥ (0 : ℝ), v t = u t) :=
  ConditionalRegularity.conditional_regularity_of_open_hyps (fun _ => u₀) (fun _ x => hdiv x) hsm hE ν hν
    (hKato u₀ hsm hdiv hE) (hclose u₀ hdiv hsm hE) (hcrit u₀)
    (huniq u₀ (hKato u₀ hsm hdiv hE))


/-! ## Clay (B) and (D) on `ℝ³/ℤ³`, exactly as in Fefferman's official description

Fefferman (Clay, 2000), quoted verbatim (ASCII transcription):

* (8)  `u°(x + e_j) = u°(x)`, `f(x + e_j, t) = f(x, t)` for `1 ≤ j ≤ n` (`e_j` = j-th unit vector);
  erratum: "The further condition `p(x + e_j, t) = p(x, t)` should be made explicit in Eqn (8)."
* (9)  `|∂_x^α ∂_t^m f(x,t)| ≤ C_{αmK} (1 + |t|)^{-K}` on `ℝ³ × [0, ∞)`, for any `α, m, K`.
* (10) `u(x, t) = u(x + e_j, t)` on `ℝ³ × [0, ∞)` for `1 ≤ j ≤ n`.
* (11) `p, u ∈ C^∞(ℝⁿ × [0, ∞))`.
* (B) "Take `ν > 0` and `n = 3`. Let `u°(x)` be any smooth, divergence-free vector field
  satisfying (8); we take `f(x,t)` to be identically zero. Then there exist smooth functions
  `p(x,t)`, `u_i(x,t)` on `ℝ³ × [0, ∞)` that satisfy (1), (2), (3), (10), (11)."
* (D) "Take `ν > 0` and `n = 3`. Then there exist a smooth, divergence-free vector field `u°(x)`
  on `ℝ³` and a smooth `f(x,t)` on `ℝ³ × [0, ∞)`, satisfying (8), (9), for which there exist no
  solutions `(p, u)` of (1), (2), (3), (10), (11) on `ℝ³ × [0, ∞)`."

Note: official (B) does **not** list the energy bound (7). On `ℝ³/ℤ³` a smooth periodic
solution satisfies the energy equality, so the cell energy is automatically bounded by its
initial value (classical, not formalized here). `Clay_B_exact_with_energy` adds it anyway.

Encoding choices. Periodicity is invariance under the whole lattice `ℤ³`
(`IsZ3Periodic`), proved equivalent to the unit-shift form (8)/(10) in
`isZ3Periodic_iff_unit_shifts`. The time derivative is `derivWithin … (Set.Ici 0)`, the
one-sided derivative on `[0, ∞)`, so the statement never looks at `t < 0`.
Smoothness is `ContDiffOn ℝ ∞` jointly in `(t, x)` on `[0, ∞) × ℝ³` (C^∞, not analytic). -/

/-- The lattice vector `∑ⱼ kⱼ eⱼ` for `k ∈ ℤ³`. -/
@[expose] public noncomputable def latticeVec (k : Fin 3 → ℤ) : T3 :=
  ∑ j : Fin 3, ((k j : ℤ) : ℝ) • EuclideanSpace.single j (1 : ℝ)

/-- `f` is `ℤ³`-periodic, i.e. descends to `ℝ³/ℤ³`. -/
@[expose] public def IsZ3Periodic {α : Type*} (f : T3 → α) : Prop :=
  ∀ (k : Fin 3 → ℤ) (x : T3), f (x + latticeVec k) = f x

/-- **Proved.** `ℤ³`-periodicity is exactly Fefferman's unit-shift condition (8)/(10). -/
public theorem isZ3Periodic_iff_unit_shifts {α : Type*} (f : T3 → α) :
    IsZ3Periodic f ↔ ∀ (j : Fin 3) (x : T3), f (x + EuclideanSpace.single j 1) = f x := by
  constructor
  · intro h j x
    have := h (Pi.single j 1) x
    have hv : latticeVec (Pi.single j 1) = EuclideanSpace.single j (1 : ℝ) := by
      unfold latticeVec
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    rwa [hv] at this
  · intro h k x
    have hper : ∀ j : Fin 3, Function.Periodic f (EuclideanSpace.single j (1 : ℝ)) :=
      fun j y => h j y
    have hz : ∀ (j : Fin 3) (n : ℤ) (y : T3),
        f (y + ((n : ℤ) : ℝ) • EuclideanSpace.single j (1 : ℝ)) = f y := by
      intro j n y
      have := (hper j).zsmul n y
      rwa [← Int.cast_smul_eq_zsmul ℝ] at this
    unfold latticeVec
    rw [Fin.sum_univ_three, ← add_assoc, ← add_assoc, hz, hz, hz]

/-- Unit cell `[0,1]³` (integration domain for the cell energy). -/
@[expose] public def unitCube : Set T3 := {x | ∀ i : Fin 3, x i ∈ Set.Icc (0 : ℝ) 1}

/-- Fefferman (1)+(2) on `ℝ³ × [0, ∞)` with force `f`, one-sided time derivative. -/
@[expose] public def navier_stokes_eq_Ici (u : TimeDependentVelocity) (p : TimeDependentPressure)
    (ν : ℝ) (f : ℝ → T3 → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∀ t ≥ (0 : ℝ), ∀ x : T3,
    derivWithin (fun s => u s x) (Set.Ici 0) t + convective (u t) (u t) x +
        pressureGradient (p t) x = ν • laplacian (u t) x + f t x ∧
      div (u t) x = 0

/-- The admissible-solution clause shared by (B) and (D): (1),(2),(3),(10) [+ erratum for `p`],(11). -/
@[expose] public def IsPeriodicSmoothSolution (ν : ℝ) (u₀ : VelocityField)
    (f : ℝ → T3 → EuclideanSpace ℝ (Fin 3))
    (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
  ContDiffOn ℝ ∞ (fun q : ℝ × T3 => p q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
  navier_stokes_eq_Ici u p ν f ∧
  u 0 = u₀ ∧
  ∀ t ≥ (0 : ℝ), IsZ3Periodic (u t) ∧ IsZ3Periodic (p t)

/-- **Clay (B), exact** (OPEN — a `Prop`, not a theorem). -/
@[expose] public def Clay_B_exact : Prop :=
  ∀ (ν : ℝ) (u₀ : VelocityField),
    0 < ν →
    ContDiff ℝ (⊤ : ℕ∞) u₀ →
    (∀ x, div u₀ x = 0) →
    IsZ3Periodic u₀ →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p

/-- Clay (B) with the cell energy bound `∫_{[0,1]³} |u(x,t)|² dx < C` added (OPEN).
Strictly stronger as written; classically equivalent (energy equality on `𝕋³`). -/
@[expose] public def Clay_B_exact_with_energy : Prop :=
  ∀ (ν : ℝ) (u₀ : VelocityField),
    0 < ν →
    ContDiff ℝ (⊤ : ℕ∞) u₀ →
    (∀ x, div u₀ x = 0) →
    IsZ3Periodic u₀ →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p ∧
      ∃ C : ℝ, ∀ t ≥ (0 : ℝ), ∫ x in unitCube, ‖u t x‖ ^ 2 < C

/-- **Proved.** The energy form implies the exact form. -/
public theorem clay_B_exact_of_with_energy (h : Clay_B_exact_with_energy) : Clay_B_exact :=
  fun ν u₀ hν hs hd hp => (h ν u₀ hν hs hd hp).imp fun _ => .imp fun _ hh => hh.1

/-- **Clay (D), periodic breakdown** (OPEN — a `Prop`). (9) is imposed on every mixed
`(t, x)` derivative of order `k` via `iteratedFDerivWithin` on `[0,∞) × ℝ³`. -/
@[expose] public def Clay_D_periodic : Prop :=
  ∃ (ν : ℝ) (u₀ : VelocityField) (f : ℝ → T3 → EuclideanSpace ℝ (Fin 3)),
    0 < ν ∧
    ContDiff ℝ (⊤ : ℕ∞) u₀ ∧
    (∀ x, div u₀ x = 0) ∧
    IsZ3Periodic u₀ ∧
    ContDiffOn ℝ ∞ (fun q : ℝ × T3 => f q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
    (∀ t ≥ (0 : ℝ), IsZ3Periodic (f t)) ∧
    (∀ k K : ℕ, ∃ C : ℝ, ∀ t ≥ (0 : ℝ), ∀ x : T3,
      ‖iteratedFDerivWithin ℝ k (fun q : ℝ × T3 => f q.1 q.2)
          (Set.Ici (0 : ℝ) ×ˢ Set.univ) (t, x)‖ ≤ C / (1 + |t|) ^ K) ∧
    ¬ ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
        IsPeriodicSmoothSolution ν u₀ f u p

/-! ## Audit finding: the library's uniqueness binder is unsatisfiable

`huniq` in `conditional_regularity_of_open_hyps` / `conditional_regularity_of_restart` quantifies over every
`v` with `NS_PDE v q ν` that is smooth **in `x`** on `[0, T']`. `NS_PDE` uses
`deriv (fun s => v s x)`, which is `0` where `v` is not differentiable in `t`. Hence the
step field `v t = 𝟙[t > 1] e₀` (with `q = 0`) "solves" NS from `u₀ = 0`, as does `v ≡ 0`, and
the binder would force them equal. So no witness satisfies it at `u₀ = 0`, and the closing
theorem `frohmanian_conditional_regularity_of_closing_bound` (which demands it for *all* data) has
an unsatisfiable hypothesis set. Classical uniqueness needs time regularity in the class. -/

/-- Step-in-time constant field: `0` for `t ≤ 1`, `e₀` for `t > 1`. -/
@[expose] public noncomputable def stepField : TimeDependentVelocity :=
  fun t _ => if 1 < t then EuclideanSpace.single 0 (1 : ℝ) else 0

private theorem deriv_step (x : T3) (t : ℝ) : deriv (fun s => stepField s x) t = 0 := by
  rcases lt_trichotomy t 1 with h | rfl | h
  · have : (fun s => stepField s x) =ᶠ[nhds t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with s hs
      simp [stepField, not_lt.mpr (le_of_lt (Set.mem_Iio.mp hs))]
    rw [this.deriv_eq]; simp
  · apply deriv_zero_of_not_differentiableAt
    intro hd
    have hc := hd.continuousAt
    have hlim : Filter.Tendsto (fun s => stepField s x) (nhdsWithin 1 (Set.Ioi 1))
        (nhds (EuclideanSpace.single 0 (1 : ℝ))) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp [stepField, Set.mem_Ioi.mp hs]
    have h2 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1:ℝ)))
    have heq := tendsto_nhds_unique h2 hlim
    simp [stepField] at heq
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) heq
    simp at this
  · have : (fun s => stepField s x) =ᶠ[nhds t] fun _ => EuclideanSpace.single 0 (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h] with s hs
      simp [stepField, Set.mem_Ioi.mp hs]
    rw [this.deriv_eq]; simp

private theorem ns_of_spatially_const (v : TimeDependentVelocity) (ν : ℝ)
    (hconst : ∀ t, ∃ c, v t = fun _ => c)
    (hdt : ∀ t x, deriv (fun s => v s x) t = 0) :
    NS_PDE v (fun _ _ => 0) ν := by
  intro t _ x
  obtain ⟨c, hc⟩ := hconst t
  have hlap : laplacian (v t) x = 0 := by
    simp [laplacian, hc]
  have hconv : convective (v t) (v t) x = 0 := by simp [convective, hc]
  have hpg : pressureGradient (fun _ : T3 => (0 : ℝ)) x = 0 := by
    simp [pressureGradient, gradient]
  have hdiv : div (v t) x = 0 := by simp [div, hc]
  refine ⟨?_, hdiv⟩
  simp only [time_deriv, hdt, hlap, hconv, hpg, smul_zero, add_zero]

/-- **Proved (standard axioms).** The library's uniqueness binder fails at `u₀ = 0`:
no Kato witness for zero data satisfies it, for any `ν`. -/
public theorem library_huniq_unsatisfiable_at_zero (ν : ℝ) (w : KatoLocalWitness 0 ν) :
    ¬ (∀ (T' : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
      T' ∈ existenceTimes 0 ν → v 0 = 0 → NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T', ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      ∀ t ∈ Set.Icc (0 : ℝ) T', w.u t = v t) := by
  intro h
  have hS : NS_PDE stepField (fun _ _ => 0) ν :=
    ns_of_spatially_const _ ν (fun t => ⟨_, rfl⟩) (fun t x => deriv_step x t)
  have hZ : NS_PDE (fun (_ : ℝ) (_ : T3) => (0 : EuclideanSpace ℝ (Fin 3))) (fun _ _ => 0) ν :=
    ns_of_spatially_const _ ν (fun t => ⟨0, rfl⟩) (fun _ _ => by simp)
  have hS0 : stepField 0 = 0 := by funext x; simp [stepField]
  have hSsm : ∀ t ∈ Set.Icc (0 : ℝ) 2, ContDiff ℝ (⊤ : ℕ∞) (stepField t) :=
    fun t _ => contDiff_const
  have hZsm : ∀ t ∈ Set.Icc (0 : ℝ) 2,
      ContDiff ℝ (⊤ : ℕ∞) ((fun (_ : ℝ) (_ : T3) => (0 : EuclideanSpace ℝ (Fin 3))) t) :=
    fun t _ => contDiff_const
  have hmem : (2 : ℝ) ∈ existenceTimes 0 ν :=
    mem_existenceTimes_zero ν (by norm_num)
  have h1 := h 2 stepField _ hmem hS0 hS hSsm 2 ⟨by norm_num, le_rfl⟩
  have h2 := h 2 _ _ hmem rfl hZ hZsm 2 ⟨by norm_num, le_rfl⟩
  have := congrFun (h1.symm.trans h2) 0
  have := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) this
  simp [stepField] at this

/-- **Proved.** The *unpatched* uniqueness binder (omitting `IsPhysicalNSSolution v`)
is unsatisfiable. -/
public theorem closing_bound_uniqueness_family_unsatisfiable (ν : ℝ)
    (hKato : ∀ u₀ : VelocityField, ContDiff ℝ (⊤ : ℕ∞) u₀ → (∀ x, div u₀ x = 0) →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) → KatoLocalWitness u₀ ν) :
    ¬ (∀ (u₀ : VelocityField) (w : KatoLocalWitness u₀ ν)
      (T' : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
      T' ∈ existenceTimes u₀ ν → v 0 = u₀ → NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T', ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      ∀ t ∈ Set.Icc (0 : ℝ) T', w.u t = v t) := by
  intro h
  have hd : ∀ x : T3, div (0 : VelocityField) x = 0 := fun x => by simp [div]
  exact library_huniq_unsatisfiable_at_zero ν
    (hKato 0 contDiff_const hd (by simp)) (h 0 _)

/-! ## Non-vacuity and joint satisfiability after the `IsPhysicalNSSolution` repair

Adding `IsPhysicalNSSolution` (pointwise time-differentiability `DifferentiableAt ℝ (fun s => u s x) t`,
spatial continuity, and the Leray L² energy inequality `∫ ‖u t x‖² ≤ ∫ ‖u 0 x‖²`) rules out
`stepField` and unbounded non-L² parasitic waves. With this repair:
1. `stepField` is proved not physically admissible (`stepField_not_physical`);
2. the repaired uniqueness hypothesis `huniq` is proved satisfiable at `u₀ = 0` (`repaired_huniq_at_zero`);
3. `FrohmanianTetherBound 0 ν` and `FrohmanianTetherRate 0 ν` are proved unconditionally (`frohmanianTetherBound_zero`, `frohmanianTetherRate_zero`);
4. `ConditionalRegularity.conditional_regularity_of_open_hyps` is instantiated unconditionally at `u₀ = 0` (`conditional_regularity_nonvacuous_at_zero`), proving that all of its hypotheses are jointly satisfiable. -/

/-- `stepField` violates `IsPhysicalNSSolution` (it jumps from `0` to `e₀ ≠ 0` at `t = 1`). -/
public theorem stepField_not_physical : ¬ IsPhysicalNSSolution stepField := by
  intro hphys
  have hS0 : stepField 0 = 0 := by funext x; simp [stepField]
  have h20 : stepField 2 = 0 :=
    eq_zero_of_isPhysicalNSSolution_zero stepField hS0 hphys 2 (by norm_num)
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) (congrFun h20 0)
  simp [stepField] at h2

/-- With `IsPhysicalNSSolution v`, the uniqueness binder `huniq` of `conditional_regularity_of_open_hyps`
is unconditionally satisfied at `u₀ = 0` for *every* `w : KatoLocalWitness 0 ν`. -/
public theorem repaired_huniq_at_zero (ν : ℝ) (w : KatoLocalWitness 0 ν) :
    ∀ (T' : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
      T' ∈ existenceTimes 0 ν →
      v 0 = 0 →
      NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T', ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      IsPhysicalNSSolution v →
      ∀ t ∈ Set.Icc (0 : ℝ) T', w.u t = v t := by
  intro T' v _q _hmem hv0 _hpde _hsm hphys t ht
  have hw_zero : w.u t = 0 := eq_zero_of_isPhysicalNSSolution_zero w.u w.init w.phys t ht.1
  have hv_zero : v t = 0 := eq_zero_of_isPhysicalNSSolution_zero v hv0 hphys t ht.1
  exact hw_zero.trans hv_zero.symm

/-- Vorticity and its sup-norm vanish on the zero velocity field. -/
public theorem vorticity_sup_norm_zero_field :
    vorticity_sup_norm (vorticity (0 : VelocityField)) = 0 := by
  unfold vorticity_sup_norm vorticity
  have hcurl : (fun x : T3 => ‖curl (0 : VelocityField) x‖) = fun _ => (0 : ℝ) := by
    funext x
    rw [curl_zero x, norm_zero]
  rw [hcurl, ciSup_const]

/-- `FrohmanianTetherBound 0 ν` holds unconditionally after the `IsPhysicalNSSolution` repair. -/
public theorem frohmanianTetherBound_zero (ν : ℝ) : FrohmanianTetherBound 0 ν := by
  intro u p _hNS hu0 hphys
  have hu_all : ∀ τ : ℝ, u τ = 0 :=
    eq_zero_of_isPhysicalNSSolution_zero_all u hu0 hphys
  have hfun : (fun τ : ℝ => vorticity_sup_norm (vorticity (u τ))) = fun _ => (0 : ℝ) := by
    funext τ
    rw [hu_all τ, vorticity_sup_norm_zero_field]
  refine ⟨0, ?_, ?_, ?_⟩
  · intro τ _hτ
    rw [hu_all τ, vorticity_sup_norm_zero_field]
  · rw [hfun]
    exact continuous_const
  · intro τ _hτ
    refine ⟨0, ?_⟩
    rintro y ⟨x, rfl⟩
    dsimp [vorticity]
    rw [hu_all τ, curl_zero x, norm_zero]

/-- `FrohmanianTetherRate 0 ν` holds unconditionally after the `IsPhysicalNSSolution` repair. -/
public theorem frohmanianTetherRate_zero (ν : ℝ) : FrohmanianTetherRate 0 ν := by
  intro u p _hν _hNS hu0 hphys
  have hu_all : ∀ τ : ℝ, u τ = 0 :=
    eq_zero_of_isPhysicalNSSolution_zero_all u hu0 hphys
  have hfun : (fun τ : ℝ => vorticity_sup_norm (vorticity (u τ))) = fun _ => (0 : ℝ) := by
    funext τ
    rw [hu_all τ, vorticity_sup_norm_zero_field]
  refine ⟨1, 1, one_pos, one_pos, ?_, ?_, ?_, ?_⟩
  · intro s _hs
    rw [hfun]
    exact differentiableAt_const 0
  · intro s _hs
    have hds : deriv (fun τ => vorticity_sup_norm (vorticity (u τ))) s = 0 := by
      rw [hfun]; simp
    rw [hds, hu_all s, vorticity_sup_norm_zero_field]
    norm_num
  · rw [hfun]
    exact continuous_const
  · intro τ _hτ
    refine ⟨0, ?_⟩
    rintro y ⟨x, rfl⟩
    dsimp [vorticity]
    rw [hu_all τ, curl_zero x, norm_zero]

/-- **Kernel-verified non-vacuity of `ConditionalRegularity.conditional_regularity_of_open_hyps`:**
at quiescent initial data `u0 = 0`, every hypothesis of `conditional_regularity_of_open_hyps`
(`h_div_free`, `h_smooth`, `h_finite_energy`, `w = kato_witness_zero ν`,
`hRiccati = frohmanianTetherBound_zero ν`, `hcrit`, and `huniq = repaired_huniq_at_zero ν`)
is unconditionally discharged, producing a global smooth solution without any unproved assumptions. -/
public theorem conditional_regularity_nonvacuous_at_zero (ν : ℝ) (hν : 0 < ν) :
    ∃ (u : TimeDependentVelocity),
      (∀ t ≥ (0 : ℝ), ConditionalRegularity.IsSmooth (u t)) ∧
      (u 0 = 0) ∧
      (∀ t ≥ (0 : ℝ), ConditionalRegularity.satisfies_NavierStokes u ν) ∧
      (∀ t ≥ (0 : ℝ), ConditionalRegularity.vorticity_sup_norm (vorticity (u t)) ≥ 0) ∧
      (∀ v : TimeDependentVelocity,
        (∀ t ≥ (0 : ℝ), ConditionalRegularity.IsSmooth (v t)) →
        v 0 = 0 →
        (∀ t ≥ (0 : ℝ), ConditionalRegularity.satisfies_NavierStokes v ν) →
        ∀ t ≥ (0 : ℝ), v t = u t) :=
  ConditionalRegularity.conditional_regularity_of_open_hyps
    (fun _ => 0)
    (fun _ x => div_zero_field x)
    contDiff_const
    (by simp)
    ν hν
    (kato_witness_zero ν)
    (frohmanianTetherBound_zero ν)
    (by
      intro u p _ hu0 _ T hT
      rw [hu0, Tstar_zero_eq_top] at hT
      exact absurd hT.symm (EReal.coe_ne_top T))
    (repaired_huniq_at_zero ν (kato_witness_zero ν))

/-! ## Honest periodic chain: what the tether bound buys on `𝕋³`

The library chain cannot be instantiated on `𝕋³` as is, for two independent reasons:
1. its energy binder `Integrable (‖u₀‖²)` on ℝ³ forces a continuous `ℤ³`-periodic `u₀` to vanish;
2. its uniqueness binder is unsatisfiable (`library_huniq_unsatisfiable_at_zero`).
So the periodic implication is stated against the *classical* BKM continuation theorem on
`𝕋³` (Beale–Kato–Majda 1984, with Kato/Temam local theory and parabolic smoothing), as an
explicit named hypothesis. -/

/-- Local smooth periodic solution on `[0, T)` (classical class: jointly C^∞, one-sided `∂ₜ`). -/
@[expose] public def IsPeriodicSmoothSolutionOn (ν T : ℝ) (u₀ : VelocityField)
    (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (Set.Ico (0 : ℝ) T ×ˢ Set.univ) ∧
  ContDiffOn ℝ ∞ (fun q : ℝ × T3 => p q.1 q.2) (Set.Ico (0 : ℝ) T ×ˢ Set.univ) ∧
  (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : T3,
    derivWithin (fun s => u s x) (Set.Ici 0) t + convective (u t) (u t) x +
        pressureGradient (p t) x = ν • laplacian (u t) x ∧ div (u t) x = 0) ∧
  u 0 = u₀ ∧
  ∀ t ∈ Set.Ico (0 : ℝ) T, IsZ3Periodic (u t) ∧ IsZ3Periodic (p t)

/-- **Periodic Frohmanian tether closing bound** (OPEN; by BKM as hard as Clay (B)).
A time-uniform `‖ω‖_∞` ceiling `Y` along every *classical* smooth periodic solution.
(Whereas `FrohmanianTetherBound` in `SymplecticTether.lean` restricts to `IsPhysicalNSSolution`
on `ℝ³`—ruling out non-differentiable jumps and non-`L²` waves so `frohmanianTetherBound_zero`
holds at `u₀ = 0`—this periodic version states the corresponding closing bound directly for
`ℤ³`-periodic smooth solutions on `𝕋³`.) -/
@[expose] public def PeriodicTetherClosingBound (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField,
    (∀ x, div u₀ x = 0) → ContDiff ℝ (⊤ : ℕ∞) u₀ → IsZ3Periodic u₀ →
      ∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
        IsPeriodicSmoothSolutionOn ν T u₀ u p →
          ∀ t ∈ Set.Ico (0 : ℝ) T, vorticity_sup_norm (vorticity (u t)) ≤ Y

/-- **Classical periodic BKM continuation** (class (i): known, not formalized here).
Local existence (Kato 1984; Temam 1995), uniqueness of smooth periodic solutions, and the
Beale–Kato–Majda criterion (1984) with parabolic smoothing give: if every local smooth
periodic solution from `u₀` obeys one uniform `‖ω‖_∞ ≤ Y`, the solution is global.
References also: Constantin–Foias, *Navier–Stokes Equations* (1988). -/
@[expose] public def PeriodicBKMContinuation (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField,
    (∀ x, div u₀ x = 0) → ContDiff ℝ (⊤ : ℕ∞) u₀ → IsZ3Periodic u₀ →
      (∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
        IsPeriodicSmoothSolutionOn ν T u₀ u p →
          ∀ t ∈ Set.Ico (0 : ℝ) T, vorticity_sup_norm (vorticity (u t)) ≤ Y) →
        ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
          IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p

/-- **Proved (standard axioms).** Periodic tether closing bound + classical periodic BKM
continuation, for every `ν > 0`, gives `Clay_B_exact`. Conditional: the bound is OPEN and is
the whole difficulty; the Frohmanian assembly contributes no step that BKM does not. -/
public theorem clay_B_exact_of_periodic_tether_bound
    (hclose : ∀ ν > (0 : ℝ), PeriodicTetherClosingBound ν)
    (hBKM : ∀ ν > (0 : ℝ), PeriodicBKMContinuation ν) : Clay_B_exact :=
  fun ν u₀ hν hs hd hp => hBKM ν hν u₀ hd hs hp (hclose ν hν u₀ hd hs hp)

#print axioms conditional_regularity_nonvacuous_at_zero
#print axioms frohmanianTetherRate_zero
#print axioms frohmanianTetherBound_zero
#print axioms repaired_huniq_at_zero
#print axioms stepField_not_physical
#print axioms clay_B_exact_of_periodic_tether_bound

end FrohmanianTether.ClayStatements
