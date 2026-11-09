/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
module
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import FrohmanianTether.ArnoldGeometric
/-!
# Plan steps 2–4 (user's ordered plan)

* Step 2: Fourier-SYMBOL identities for Biot–Savart. On a mode `k ≠ 0` with divergence-free
  amplitude `w` (`k ⬝ᵥ w = 0`), the BS symbol is `û = |k|⁻² (k × w)` (the factor `i` of
  `i k × ·` is absorbed: `curl` acts as `−k × ·` on the real form). We prove
  `div` symbol `k ⬝ᵥ û = 0` and `curl ∘ BS = id` symbol `−k × û = w`.
  SCOPE: these are mode-wise algebraic identities. They are NOT yet connected to the
  real-space integral `BiotSavart` (that needs a Fourier-series representation of the
  kernel on T³, not formalized).
* Step 3: Euler as coadjoint motion, stated as a named Prop (`IsCoadjointMotion`);
  Casimir conservation is proved CONDITIONAL on `SDiffActionHyp` (open).
  The identification of the Euler flow with the kinetic-energy Hamiltonian motion is NOT
  proved; it is the hypothesis `IsCoadjointMotion`.
* Step 4: scaling counterexample. Under NS scaling the stretching term scales like `λ⁶`
  and `C M³ − κ M⁴` with `M_λ = λ² M` contains a `λ⁸` term, so the pointwise tether bound
  cannot hold at all scales for any nonzero `M` (checked lemma below).
-/

@[expose] public section

namespace PlanSteps

open Matrix ArnoldGeometric

/-- Real form of the Biot–Savart Fourier symbol on mode `k`. -/
noncomputable def bsSymbol (k w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (k ⬝ᵥ k)⁻¹ • crossProduct k w

/-- Step 2 (proved): divergence-free symbol, `k · û = 0`. -/
theorem bsSymbol_div (k w : Fin 3 → ℝ) : k ⬝ᵥ bsSymbol k w = 0 := by
  simp [bsSymbol, dotProduct_smul, dot_self_cross]

/-- Step 2 (proved): `curl ∘ BS = id` symbol, `−k × û = w`, for `k ≠ 0`, `k · w = 0`. -/
theorem bsSymbol_curl (k w : Fin 3 → ℝ) (hk : k ≠ 0) (hw : k ⬝ᵥ w = 0) :
    -crossProduct k (bsSymbol k w) = w := by
  have hkk : k ⬝ᵥ k ≠ 0 := by
    intro h; exact hk (dotProduct_self_eq_zero.mp h)
  have hw' : k 0 * w 0 + k 1 * w 1 + k 2 * w 2 = 0 := by
    simpa [dotProduct, Fin.sum_univ_three] using hw
  have key : -crossProduct k (crossProduct k w) = (k ⬝ᵥ k) • w := by
    funext i
    fin_cases i
    · simp [crossProduct, dotProduct, Fin.sum_univ_three]; linear_combination (-(k 0)) * hw'
    · simp [crossProduct, dotProduct, Fin.sum_univ_three]; linear_combination (-(k 1)) * hw'
    · simp [crossProduct, dotProduct, Fin.sum_univ_three]; linear_combination (-(k 2)) * hw'
  simp only [bsSymbol, LinearMap.map_smul, ← smul_neg, key, smul_smul, inv_mul_cancel₀ hkk,
    one_smul]

/-- Step 3 hypothesis (named, OPEN): the trajectory `ω` is a coadjoint motion. -/
def IsCoadjointMotion (SDiff : Type*) [Group SDiff] [MulAction SDiff CoadjointOrbit]
    (ω : ℝ → CoadjointOrbit) : Prop :=
  ∃ g : ℝ → SDiff, ∀ t, ω t = g t • ω 0

/-- Step 3 (proved, conditional on `SDiffActionHyp` and `IsCoadjointMotion`):
every Casimir is conserved. -/
theorem casimir_conserved {SDiff : Type*} [Group SDiff] [MulAction SDiff CoadjointOrbit]
    (H : SDiffActionHyp SDiff) (ω : ℝ → CoadjointOrbit) (hω : IsCoadjointMotion SDiff ω)
    (f : ℝ → ℝ) (t : ℝ) : Casimir f (ω t) = Casimir f (ω 0) := by
  obtain ⟨g, hg⟩ := hω
  rw [hg t]; exact H.casimir_invariant f (g t) (ω 0)

/-- Step 4 (proved): the pointwise tether bound `S ≤ C M³ − κ M⁴` is not scale-consistent.
For any value `S` of the stretching and any `M ≠ 0`, `κ > 0`, the scaled family
`λ⁶ S ≤ C (λ² M)³ − κ (λ² M)⁴` fails for some `λ > 0`. -/
theorem tether_bound_not_scale_invariant (S C κ M : ℝ) (hκ : 0 < κ) (hM : M ≠ 0) :
    ¬ ∀ l : ℝ, 0 < l → l ^ 6 * S ≤ C * (l ^ 2 * M) ^ 3 - κ * (l ^ 2 * M) ^ 4 := by
  intro h
  have hM4 : 0 < M ^ 4 := by positivity
  set t : ℝ := (|C * M ^ 3 - S| + 1) / (κ * M ^ 4) with ht
  have htpos : 0 < t := by positivity
  have hl := h (Real.sqrt t) (Real.sqrt_pos.mpr htpos)
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt htpos.le
  have e6 : Real.sqrt t ^ 6 = t ^ 3 := by rw [show (6:ℕ) = 2 * 3 from rfl, pow_mul, hs]
  have e8 : Real.sqrt t ^ 8 = t ^ 4 := by rw [show (8:ℕ) = 2 * 4 from rfl, pow_mul, hs]
  have hl' : t ^ 3 * S ≤ t ^ 3 * (C * M ^ 3 - κ * t * M ^ 4) := by
    have : C * (Real.sqrt t ^ 2 * M) ^ 3 - κ * (Real.sqrt t ^ 2 * M) ^ 4
        = Real.sqrt t ^ 6 * C * M ^ 3 - κ * Real.sqrt t ^ 8 * M ^ 4 := by ring
    rw [this, e6, e8] at hl; nlinarith [hl]
  have hkt : κ * t * M ^ 4 = |C * M ^ 3 - S| + 1 := by
    rw [ht]; field_simp
  have h3 : 0 < t ^ 3 := by positivity
  have := le_of_mul_le_mul_left hl' h3
  have := le_abs_self (C * M ^ 3 - S)
  linarith

end PlanSteps
