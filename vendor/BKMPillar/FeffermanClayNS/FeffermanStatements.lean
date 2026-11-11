/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import BKMPillar.FeffermanClayNS.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

open scoped BigOperators Gradient Topology ContDiff
open ENNReal InnerProductSpace MeasureTheory Finset Filter
open FeffermanNavierStokes3D

/-!
# Charles L. Fefferman (2000): Official Clay Millennium Navier–Stokes Statements in Lean 4

This module encodes the verbatim mathematical definitions of the Clay Mathematics Institute
Millennium Problem for 3D incompressible Navier–Stokes, following Charles L. Fefferman,
*"Existence and Smoothness of the Navier–Stokes Equation"* (2000), Equations (1)–(11):

* **Statement (A):** Existence and smoothness of Navier–Stokes solutions on `ℝ³`.
* **Statement (B):** Existence and smoothness of Navier–Stokes solutions on `ℝ³ / ℤ³` (`𝕋³`),
  both in the exact printed text of page 2 (`Clay_B_exact`, Equations (1), (2), (3), (8),
  (10), (11) with zero force `f ≡ 0`) and in the strengthened variant adding bounded energy (7)
  (`Clay_B_exact_with_energy`).
* **Statement (D):** Breakdown of Navier–Stokes solutions on `ℝ³ / ℤ³`.

All statements `Clay_A`, `Clay_B_exact`, `Clay_B_exact_with_energy`, and `Clay_D_periodic` are
defined as `Prop`s (open mathematical propositions, never asserted as axioms).
-/

namespace FeffermanClayNS

/-- The `j`-th standard unit basis vector `eⱼ ∈ ℝ³`. -/
@[expose] public noncomputable def stdBasisVec (j : Fin 3) : T3 :=
  EuclideanSpace.single j (1 : ℝ)

/-- Embedding of an integer lattice vector `k ∈ ℤ³` into `T3 = ℝ³`. -/
@[expose] public noncomputable def intVecToT3 (k : Fin 3 → ℤ) : T3 :=
  ∑ j : Fin 3, (k j : ℝ) • stdBasisVec j

/-- **Fefferman Equation (8) (`ℤ³`-periodicity on `ℝ³ / ℤ³`):**
A function `g : T3 → α` is periodic of period `1` in each coordinate direction (`e₁, e₂, e₃`),
equivalently invariant under all integer lattice shifts `k ∈ ℤ³`:
`g (x + k₁ e₁ + k₂ e₂ + k₃ e₃) = g x`. -/
@[expose] public def IsZ3Periodic {α : Type*} (g : T3 → α) : Prop :=
  ∀ (x : T3) (k : Fin 3 → ℤ), g (x + intVecToT3 k) = g x

/-- Unit-shift periodicity (`g (x + eⱼ) = g x` for `j = 1, 2, 3`, Fefferman Eq. (8) literally)
is equivalent to full `ℤ³`-lattice periodicity `IsZ3Periodic g`. -/
public theorem isZ3Periodic_iff_unit_shifts {α : Type*} (g : T3 → α) :
    IsZ3Periodic g ↔ ∀ (x : T3) (j : Fin 3), g (x + stdBasisVec j) = g x := by
  constructor
  · intro h x j
    have := h x (Pi.single j 1)
    have hv : intVecToT3 (Pi.single j 1) = stdBasisVec j := by
      unfold intVecToT3
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    rwa [hv] at this
  · intro hunit x k
    have hper : ∀ j : Fin 3, Function.Periodic g (stdBasisVec j) :=
      fun j y => hunit y j
    have hz : ∀ (j : Fin 3) (n : ℤ) (y : T3),
        g (y + ((n : ℤ) : ℝ) • stdBasisVec j) = g y := by
      intro j n y
      have := (hper j).zsmul n y
      rwa [← Int.cast_smul_eq_zsmul ℝ] at this
    unfold intVecToT3
    rw [Fin.sum_univ_three, ← add_assoc, ← add_assoc, hz, hz, hz]

/-- **Fefferman Equation (1) on `[0, ∞) × ℝ³`:**
Incompressible Navier–Stokes momentum equation with external force `f`, using the right-hand
time derivative `derivWithin · (Set.Ici 0) t` so that `t = 0` is the one-sided derivative on
`[0, ∞)` as specified in Fefferman's footnote on page 2. -/
@[expose] public def navier_stokes_eq_Ici
    (ν : ℝ) (f : ℝ → T3 → EuclideanSpace ℝ (Fin 3))
    (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  ∀ t ≥ (0 : ℝ), ∀ x : T3,
    derivWithin (fun s => u s x) (Set.Ici (0 : ℝ)) t + convective (u t) (u t) x =
      ν • laplacian (u t) x - pressureGradient (p t) x + f t x

/-- **Fefferman Periodic Initial Data (Equations (2), (8) with `f ≡ 0`):**
Smooth (`C^∞(ℝ³)`), divergence-free, `ℤ³`-periodic initial velocity field `u⁰(x)`. -/
@[expose] public def IsPeriodicSmoothInitialData (u₀ : VelocityField) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) u₀ ∧
  (∀ x : T3, div u₀ x = 0) ∧
  IsZ3Periodic u₀

/-- **Fefferman Periodic Smooth Solution on `ℝ³ / ℤ³` (Equations (1), (2), (3), (8), (10), (11)):**
A pair `(u, p)` solving the Navier–Stokes system on `[0, ∞) × ℝ³` such that:
1. Eq. (10): `u(t, x)` is `ℤ³`-periodic in `x` (`IsZ3Periodic (u t)` for all `t ≥ 0`), and
   `p(t, x)` is `ℤ³`-periodic in `x` (`IsZ3Periodic (p t)` for all `t ≥ 0`), ensuring `(u, p)`
   is a single-valued smooth solution on the compact torus `𝕋³ = ℝ³ / ℤ³`;
2. Eq. (11): `u, p ∈ C^∞([0, ∞) × ℝ³)` jointly in `(t, x)` (`ContDiffOn ℝ ∞` on `[0, ∞) × ℝ³`);
3. Eq. (1): Momentum balance `∂_t u + (u · ∇) u = ν Δu - ∇p + f` on `[0, ∞) × ℝ³`;
4. Eq. (2): Incompressibility `div u = 0` on `[0, ∞) × ℝ³`;
5. Eq. (3): Initial condition `u(0, x) = u⁰(x)` on `ℝ³`. -/
@[expose] public def IsPeriodicSmoothSolution
    (ν : ℝ) (u₀ : VelocityField) (f : ℝ → T3 → EuclideanSpace ℝ (Fin 3))
    (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  (∀ t ≥ (0 : ℝ), IsZ3Periodic (u t)) ∧
  (∀ t ≥ (0 : ℝ), IsZ3Periodic (p t)) ∧
  ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
  ContDiffOn ℝ ∞ (fun q : ℝ × T3 => p q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
  navier_stokes_eq_Ici ν f u p ∧
  (∀ t ≥ (0 : ℝ), ∀ x : T3, div (u t) x = 0) ∧
  (∀ x : T3, u 0 x = u₀ x)

/-- **Local-in-time periodic smooth solution on `[0, T] × (ℝ³ / ℤ³)`:**
Restriction of Fefferman's periodic smooth solution conditions to a finite time horizon `[0, T]`.
There is no L²(ℝ³) clause: a nonzero periodic field is never square-integrable on ℝ³. The energy
over one period cell is finite automatically, since `u` is continuous and periodic.
The earlier version with the L²(ℝ³) clause is `IsPeriodicSmoothSolutionOnOriginal`. -/
@[expose] public def IsPeriodicSmoothSolutionOn
    (ν : ℝ) (u₀ : VelocityField) (f : ℝ → T3 → EuclideanSpace ℝ (Fin 3))
    (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  0 < T ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T, IsZ3Periodic (u t)) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T, IsZ3Periodic (p t)) ∧
  ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (Set.Icc (0 : ℝ) T ×ˢ Set.univ) ∧
  ContDiffOn ℝ ∞ (fun q : ℝ × T3 => p q.1 q.2) (Set.Icc (0 : ℝ) T ×ˢ Set.univ) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : T3,
    derivWithin (fun s => u s x) (Set.Icc (0 : ℝ) T) t + convective (u t) (u t) x =
      ν • laplacian (u t) x - pressureGradient (p t) x + f t x) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : T3, div (u t) x = 0) ∧
  (∀ x : T3, u 0 x = u₀ x)

/-- **Scaffolding (unsatisfiable for nonzero data):** the earlier local solution predicate, which
also required `IsPhysicalNSSolution u` (L² over all of ℝ³). See
`not_periodicLocalExistenceOriginal` in `HighSetDepletionAndBKM.lean`. -/
@[expose] public def IsPeriodicSmoothSolutionOnOriginal
    (ν : ℝ) (u₀ : VelocityField) (f : ℝ → T3 → EuclideanSpace ℝ (Fin 3))
    (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  IsPeriodicSmoothSolutionOn ν u₀ f T u p ∧ IsPhysicalNSSolution u

/-- **Fefferman Equation (7) (Bounded kinetic energy):**
`∫ ‖u(x, t)‖² dx < C` for all `t ≥ 0` (with explicit `Integrable` guard so Bochner
integration does not silently return `0` on non-integrable fields). -/
@[expose] public def HasBoundedEnergy (u : TimeDependentVelocity) : Prop :=
  (∀ t ≥ (0 : ℝ), Integrable (fun x : T3 => ‖u t x‖ ^ 2)) ∧
  ∃ C : ℝ, ∀ t ≥ (0 : ℝ), (∫ x : T3, ‖u t x‖ ^ 2) < C

/-- **Exact Fefferman Clay Statement (B) on `ℝ³ / ℤ³` (`Clay_B_exact`, OPEN — a `Prop`):**
Verbatim statement from Charles L. Fefferman (2000), page 2:
Take `ν > 0` and `n = 3`. Let `u⁰(x)` be any smooth, divergence-free, `ℤ³`-periodic vector
field on `ℝ³` satisfying (8), and take `f(x, t)` to be identically zero. Then there exist
smooth functions `p(x, t), uᵢ(x, t)` on `ℝ³ × [0, ∞)` that satisfy (1), (2), (3), (10), (11). -/
@[expose] public def Clay_B_exact (ν : ℝ) : Prop :=
  0 < ν →
  ∀ u₀ : VelocityField,
    IsPeriodicSmoothInitialData u₀ →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p

/-- **Strengthened Fefferman Clay Statement (B) with Bounded Energy (`Clay_B_exact_with_energy`):**
Same as `Clay_B_exact`, additionally asserting the uniform kinetic energy bound (7). -/
@[expose] public def Clay_B_exact_with_energy (ν : ℝ) : Prop :=
  0 < ν →
  ∀ u₀ : VelocityField,
    IsPeriodicSmoothInitialData u₀ →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p ∧
      HasBoundedEnergy u

/-- `Clay_B_exact_with_energy` immediately implies the verbatim `Clay_B_exact`. -/
public theorem clay_B_exact_of_with_energy (ν : ℝ)
    (h : Clay_B_exact_with_energy ν) : Clay_B_exact ν := by
  intro hν u₀ hu₀
  obtain ⟨u, p, hsol, _⟩ := h hν u₀ hu₀
  exact ⟨u, p, hsol⟩

/-- **Fefferman Equation (4) (`ℝ³` Schwartz-type spatial decay of all derivatives):**
`|∂_x^α u₀(x)| ≤ C_{α K} (1 + |x|)^{-K}` on `ℝ³` for all `α, K`. -/
@[expose] public def HasRapidDecay (u₀ : VelocityField) : Prop :=
  ∀ (k K : ℕ), ∃ C : ℝ, ∀ x : T3,
    ‖iteratedFDeriv ℝ k u₀ x‖ ≤ C / (1 + ‖x‖) ^ K

/-- **Fefferman `ℝ³` Initial Data (Equations (2), (4) with `f ≡ 0`):**
Smooth (`C^∞(ℝ³)`), divergence-free initial velocity field `u⁰(x)` satisfying (4). -/
@[expose] public def IsR3SmoothInitialData (u₀ : VelocityField) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) u₀ ∧
  (∀ x : T3, div u₀ x = 0) ∧
  HasRapidDecay u₀

/-- **Fefferman `ℝ³` Smooth Solution (Equations (1), (2), (3), (6), (7) with `f ≡ 0`):**
Jointly smooth `(u, p) ∈ C^∞([0, ∞) × ℝ³)` satisfying (1), (2), (3) and bounded energy (7). -/
@[expose] public def IsR3SmoothSolution
    (ν : ℝ) (u₀ : VelocityField)
    (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
  ContDiffOn ℝ ∞ (fun q : ℝ × T3 => p q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
  navier_stokes_eq_Ici ν (fun _ _ => 0) u p ∧
  (∀ t ≥ (0 : ℝ), ∀ x : T3, div (u t) x = 0) ∧
  (∀ x : T3, u 0 x = u₀ x) ∧
  HasBoundedEnergy u

/-- **Exact Fefferman Clay Statement (A) on `ℝ³` (`Clay_A`, OPEN — a `Prop`):**
Verbatim statement from Charles L. Fefferman (2000), page 2:
Take `ν > 0` and `n = 3`. Let `u⁰(x)` be any smooth, divergence-free vector field
satisfying (4). Take `f(x, t)` to be identically zero. Then there exist smooth functions
`p(x, t), uᵢ(x, t)` on `ℝ³ × [0, ∞)` that satisfy (1), (2), (3), (6), (7). -/
@[expose] public def Clay_A (ν : ℝ) : Prop :=
  0 < ν →
  ∀ u₀ : VelocityField,
    IsR3SmoothInitialData u₀ →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsR3SmoothSolution ν u₀ u p

/-- **Clay Statement (D), periodic breakdown (`Clay_D_periodic`, OPEN — a `Prop`):**
Existence of smooth, divergence-free, `ℤ³`-periodic data `u⁰` and smooth `ℤ³`-periodic force `f`
satisfying (9) for which no global periodic smooth solution `(u, p)` exists. -/
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

/-! ## Physical Admissibility (`IsPhysicalNSSolution`) & Exclusion of Discontinuous Step-Fields

Because `NS_PDE` evaluates `deriv (fun s => v s x) t`, which in Mathlib defaults to `0` at points
where `s ↦ v s x` is not differentiable, a spatially constant step-in-time field `stepField`
(`0` for `t ≤ 1`, `e₀` for `t > 1`) would satisfy raw `NS_PDE` with `q = 0` unless physical time
differentiability and the Leray `L²` energy inequality (`IsPhysicalNSSolution`) are imposed. -/

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
  have hlap : laplacian (v t) x = 0 := by simp [laplacian, hc]
  have hconv : convective (v t) (v t) x = 0 := by simp [convective, hc]
  have hpg : pressureGradient (fun _ : T3 => (0 : ℝ)) x = 0 := by
    simp [pressureGradient, gradient]
  have hdiv : div (v t) x = 0 := by simp [div, hc]
  refine ⟨?_, hdiv⟩
  simp only [time_deriv, hdt, hlap, hconv, hpg, smul_zero, add_zero]

/-- **Proved:** Without `IsPhysicalNSSolution`, a uniqueness binder quantifying over raw `NS_PDE`
solutions is unsatisfiable at `u₀ = 0` because `stepField` and `0` both satisfy raw `NS_PDE`. -/
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

/-- **Proved:** `stepField` violates `IsPhysicalNSSolution` (it jumps from `0` to `e₀ ≠ 0` at `t = 1`). -/
public theorem stepField_not_physical : ¬ IsPhysicalNSSolution stepField := by
  intro hphys
  have hS0 : stepField 0 = 0 := by funext x; simp [stepField]
  have h20 : stepField 2 = 0 :=
    eq_zero_of_isPhysicalNSSolution_zero stepField hS0 hphys 2 (by norm_num)
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) (congrFun h20 0)
  simp [stepField] at h2

/-- **Proved:** With `IsPhysicalNSSolution v`, the `L²` integrability hypothesis `hInt` holds
unconditionally for every initial datum `u₀` and viscosity `ν`. -/
public theorem repaired_hInt (u₀ : VelocityField) (ν : ℝ) :
    ∀ (T : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
      T ∈ existenceTimes u₀ ν →
      v 0 = u₀ →
      NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      IsPhysicalNSSolution v →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun x : T3 => ‖v t x‖ ^ 2) := by
  intro _T v _q _hmem _hv0 _hpde _hsm hphys t ht
  exact hphys.2.2.1 t ht.1

/-- **Proved:** With `IsPhysicalNSSolution v`, shifted-restart uniqueness is unconditionally
satisfied at quiescent initial data `u₀ = 0`. -/
public theorem repaired_huniq_shift_at_zero (ν : ℝ) :
    ∀ (T : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
      T ∈ existenceTimes (0 : VelocityField) ν →
      v 0 = (0 : VelocityField) →
      NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      IsPhysicalNSSolution v →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        ∀ (w' : KatoLocalWitness (v t) ν),
          ∀ s ∈ Set.Icc (0 : ℝ) w'.T, v (t + s) = w'.u s := by
  intro _T v _q _hmem hv0 _hpde _hsm hphys t ht w' s hs
  have hvt : v t = 0 := eq_zero_of_isPhysicalNSSolution_zero v hv0 hphys t ht.1
  have hvts : v (t + s) = 0 :=
    eq_zero_of_isPhysicalNSSolution_zero v hv0 hphys (t + s) (add_nonneg ht.1 hs.1)
  have hw0 : w'.u 0 = 0 := w'.init.trans hvt
  have hws : w'.u s = 0 :=
    eq_zero_of_isPhysicalNSSolution_zero w'.u hw0 w'.phys s hs.1
  rw [hvts, hws]

/-- **Proved:** With `IsPhysicalNSSolution v`, uniqueness on `[0, T']` is unconditionally
satisfied at `u₀ = 0` for every `w : KatoLocalWitness 0 ν`. -/
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

end FeffermanClayNS
