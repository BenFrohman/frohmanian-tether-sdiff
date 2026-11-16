/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import FrohmanianTether.ClayStatements

/-!
# Truth Gate: semantics lock (see `TRUTH_GATE.md`)

PAPER_PATH: manuscript/main.tex
PAPER_SHA256: b1e6a8e942383a99f501062261ae75f57f69986059e0a2f1087ea9503f880de9
PAPER_SECTION: Section 2 "Main results of version 0.1.5", Theorem thm:mainA ("Main theorem, kernel-checked")

Locked paper claim: Theorem `thm:mainA` ("Main theorem, kernel-checked"), quoted verbatim:

PAPER_QUOTE_BEGIN
Assume, for every $\nu>0$,
\begin{enumerate}[label=(\roman*)]
\item \lean{PeriodicTetherClosingBound ν} (the Frohmanian tether bound, Definition~\ref{def:ptb}), and
\item \lean{PeriodicBKMContinuation ν}: for every smooth divergence-free $\mathbb{Z}^3$-periodic $u_0$, a single
ceiling $Y$ for $M$ along all classical periodic solutions from $u_0$ on all intervals $[0,T)$ yields a global
solution $(u,p)$ satisfying \lean{IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p}.
\end{enumerate}
Then \lean{Clay_B_exact} holds: for every $\nu>0$ and every smooth, divergence-free, $\mathbb{Z}^3$-periodic
$u_0$ there exist $(u,p)$, jointly $C^\infty$ on $[0,\infty)\times\R^3$, solving the Navier--Stokes equations
with zero forcing, with $u(0)=u_0$ and $u(t),p(t)$ periodic for all $t\ge0$.
PAPER_QUOTE_END

Reading of the paper's terms (fixed here, once):
* hypotheses (i) and (ii) are assumed together "for every `ν > 0`";
* "smooth, divergence-free, `ℤ³`-periodic `u₀`" is `ContDiff ℝ ⊤ u₀`, `∀ x, div u₀ x = 0`,
  `IsZ3Periodic u₀`;
* "jointly `C^∞` on `[0,∞) × ℝ³`" is `ContDiffOn ℝ ∞` of `(t, x) ↦ u t x` and of `(t, x) ↦ p t x`
  on `Set.Ici 0 ×ˢ Set.univ`;
* "solving the Navier–Stokes equations with zero forcing" is `navier_stokes_eq_Ici u p ν 0`
  (momentum equation with one-sided time derivative and `div u = 0`, for `t ≥ 0`);
* "`u(0) = u₀` and `u(t), p(t)` periodic for all `t ≥ 0`" is spelled out literally.

`formal_claim` is the statement of `FrohmanianTether.ClayStatements.clay_B_exact_of_periodic_tether_bound`.
`paper_claim` spells out the conclusion clause by clause instead of using `Clay_B_exact` and
`IsPeriodicSmoothSolution`, and takes the two hypotheses jointly as the paper does.

Scope: CONDITIONAL. Hypothesis (i), the periodic tether closing bound, is OPEN and as strong as
statement (B) itself; this lock certifies only the implication. It is not a proof of the
Navier–Stokes Millennium problem.
-/

namespace TruthGate

open NavierStokes3D FrohmanianTether FrohmanianTether.ClayStatements
open scoped ContDiff

-- TRUTH-GATE LOCK BEGIN
/-- The repository's main statement (`clay_B_exact_of_periodic_tether_bound`). -/
def formal_claim : Prop :=
  (∀ ν > (0 : ℝ), PeriodicTetherClosingBound ν) →
    (∀ ν > (0 : ℝ), PeriodicBKMContinuation ν) → Clay_B_exact

/-- The paper's Theorem thm:mainA, conclusion spelled out clause by clause. -/
def paper_claim : Prop :=
  (∀ ν : ℝ, 0 < ν → PeriodicTetherClosingBound ν ∧ PeriodicBKMContinuation ν) →
    ∀ (ν : ℝ) (u₀ : VelocityField), 0 < ν →
      ContDiff ℝ (⊤ : ℕ∞) u₀ → (∀ x, div u₀ x = 0) → IsZ3Periodic u₀ →
      ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
        ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
        ContDiffOn ℝ ∞ (fun q : ℝ × T3 => p q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
        navier_stokes_eq_Ici u p ν (fun _ _ => 0) ∧
        u 0 = u₀ ∧
        (∀ t ≥ (0 : ℝ), IsZ3Periodic (u t) ∧ IsZ3Periodic (p t))

/-- The fixed correspondence between the formal statement and the paper's claim. -/
theorem intended_correspondence : formal_claim ↔ paper_claim := by
  constructor
  · intro h hyp ν u₀ hν hs hd hp
    obtain ⟨u, p, hsol⟩ :=
      h (fun ν hν => (hyp ν hν).1) (fun ν hν => (hyp ν hν).2) ν u₀ hν hs hd hp
    exact ⟨u, p, hsol⟩
  · intro h hclose hBKM ν u₀ hν hs hd hp
    obtain ⟨u, p, hsol⟩ := h (fun ν hν => ⟨hclose ν hν, hBKM ν hν⟩) ν u₀ hν hs hd hp
    exact ⟨u, p, hsol⟩
-- TRUTH-GATE LOCK END

/-- The main theorem proves `formal_claim`. -/
theorem formal_claim_holds : formal_claim :=
  fun hclose hBKM => clay_B_exact_of_periodic_tether_bound hclose hBKM

/-- The paper's claim, transported across the correspondence. -/
theorem paper_claim_holds : paper_claim :=
  intended_correspondence.mp formal_claim_holds

end TruthGate
