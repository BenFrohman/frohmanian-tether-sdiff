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
PAPER_SECTION: Section 2 "Main results of version 0.1.5", Definition def:ptb ("The Frohmanian tether bound") and Theorem thm:mainA ("Main theorem, kernel-checked")

Locked paper claim: Theorem `thm:mainA` ("Main theorem, kernel-checked"), quoted verbatim,
together with the English of Definition `def:ptb` and the paper's definition of `M(t)` and of
the classical periodic solution class, from which the two hypotheses are independently
transcribed.

PAPER_QUOTE_BEGIN
Throughout, $M(t)=\|\omega(t)\|_{L^\infty}$ is \lean{vorticity_sup_norm (vorticity (u t))}, and
\lean{IsPeriodicSmoothSolutionOn ν T u₀ u p} is the class of classical solutions on $[0,T)$: $(u,p)$ jointly
$C^\infty$ on $[0,T)\times\R^3$, the equations with one-sided time derivative and zero forcing,
$\operatorname{div}u=0$, $u(0)=u_0$, and $u(t),p(t)$ $\mathbb{Z}^3$-periodic (exact text in
Appendix~\ref{app:lean:clay}).
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{definition}[The Frohmanian tether bound]\label{def:ptb}
\emph{Lean:} \leanbrk{TetherImpliesBKM.PeriodicTetherBound}.\par\noindent
For $\nu\in\R$ and a field $u_0$, \lean{PeriodicTetherBound ν u₀} asserts that there is $Y\in\R$ such that
$M(t)\le Y$ for every $T$, every classical periodic solution $(u,p)$ from $u_0$ on $[0,T)$ and every
$t\in[0,T)$. The \emph{closing bound} \lean{PeriodicTetherClosingBound ν} asserts \lean{PeriodicTetherBound ν u₀}
for every smooth divergence-free $\mathbb{Z}^3$-periodic $u_0$; this is a definitional identity
(\lean{periodicTetherClosingBound_iff}, proved by \lean{Iff.rfl}).
\end{definition}
PAPER_QUOTE_END

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

Reading of the paper's terms (fixed here, once), transcribed from the English above and not from
the repository's named hypothesis Props:

* hypotheses (i) and (ii) are assumed together "for every `ν > 0`";
* "smooth, divergence-free, `ℤ³`-periodic `u₀`" is `ContDiff ℝ ⊤ u₀`, `∀ x, div u₀ x = 0`,
  `IsZ3Periodic u₀`;
* `M(t)` is `vorticity_sup_norm (vorticity (u t))`, i.e. `‖ω(t)‖_∞`;
* a "classical periodic solution `(u,p)` from `u₀` on `[0,T)`" is the genuine NS class
  `IsPeriodicSmoothSolutionOn ν T u₀ u p` (jointly `C^∞` on `[0,T) × ℝ³`, one-sided time
  derivative, zero forcing, `div u = 0`, `u(0) = u₀`, and `u(t), p(t)` `ℤ³`-periodic);
* hypothesis (i) is the closing bound of Definition `def:ptb`: the Frohmanian tether bound
  `PeriodicTetherBound ν u₀` asserts that there is `Y ∈ ℝ` such that `M(t) ≤ Y` for every
  `T`, every classical periodic solution from `u₀` on `[0,T)` and every `t ∈ [0,T)`; the
  closing bound requires this for every smooth divergence-free `ℤ³`-periodic `u₀`. The
  tether kernel does not appear in that definition;
* hypothesis (ii) is the Beale–Kato–Majda continuation definition given in the theorem: for
  every smooth divergence-free `ℤ³`-periodic `u₀`, a single ceiling `Y` for `M` along all
  classical periodic solutions from `u₀` on all intervals `[0,T)` yields a global solution
  `(u,p)` in the genuine NS class `IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p`;
* "jointly `C^∞` on `[0,∞) × ℝ³`" is `ContDiffOn ℝ ∞` of `(t, x) ↦ u t x` and of `(t, x) ↦ p t x`
  on `Set.Ici 0 ×ˢ Set.univ`;
* "solving the Navier–Stokes equations with zero forcing" is `navier_stokes_eq_Ici u p ν 0`
  (momentum equation with one-sided time derivative and `div u = 0`, for `t ≥ 0`);
* "`u(0) = u₀` and `u(t), p(t)` periodic for all `t ≥ 0`" is spelled out literally.

`formal_claim` is the statement of `FrohmanianTether.ClayStatements.clay_B_exact_of_periodic_tether_bound`.
`paper_claim` writes both hypotheses out in full from the English of `def:ptb` and of (ii),
and spells out the conclusion clause by clause. It does not name, unfold, or otherwise refer
to the repository Props `PeriodicTetherClosingBound`, `PeriodicBKMContinuation` or
`Clay_B_exact`, nor to `formal_claim`.

Scope: CONDITIONAL. Hypothesis (i), the closing bound of Definition `def:ptb`, is OPEN and as
strong as statement (B) itself; this lock certifies only the implication. It is not a proof of
the Navier–Stokes Millennium problem, and it is not a proof of Navier–Stokes regularity.
Approved by Benjamin Stanley Frohman, 2026-11-17 00:22 CT, replying "OK" to "It needs your OK on three new sentences for the paper and a rewrite of the existing Clay B lock"; confirmed 00:32 CT: "yes fix and proceed!".
-/

namespace TruthGate

open NavierStokes3D FrohmanianTether FrohmanianTether.ClayStatements
open scoped ContDiff

-- TRUTH-GATE LOCK BEGIN
/-- The repository's main statement (`clay_B_exact_of_periodic_tether_bound`). -/
def formal_claim : Prop :=
  (∀ ν > (0 : ℝ), PeriodicTetherClosingBound ν) →
    (∀ ν > (0 : ℝ), PeriodicBKMContinuation ν) → Clay_B_exact

/-- The paper's Theorem thm:mainA. Hypotheses (i) and (ii) are written out from
Definition def:ptb (there is `Y` such that `M(t) ≤ Y`) and from the English of
hypothesis (ii) (a single ceiling `Y` for `M` yields a global solution in
`IsPeriodicSmoothSolution`). The conclusion is spelled out clause by clause. -/
def paper_claim : Prop :=
  (∀ ν : ℝ, 0 < ν →
      (∀ u₀ : VelocityField,
          ContDiff ℝ (⊤ : ℕ∞) u₀ → (∀ x, div u₀ x = 0) → IsZ3Periodic u₀ →
            ∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
              IsPeriodicSmoothSolutionOn ν T u₀ u p →
                ∀ t ∈ Set.Ico (0 : ℝ) T, vorticity_sup_norm (vorticity (u t)) ≤ Y) ∧
      (∀ u₀ : VelocityField,
          ContDiff ℝ (⊤ : ℕ∞) u₀ → (∀ x, div u₀ x = 0) → IsZ3Periodic u₀ →
            (∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
              IsPeriodicSmoothSolutionOn ν T u₀ u p →
                ∀ t ∈ Set.Ico (0 : ℝ) T, vorticity_sup_norm (vorticity (u t)) ≤ Y) →
              ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
                IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p)) →
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
  · intro hformal hpaper ν u₀ hν hsmooth hdiv hper
    have hclose : ∀ ν > (0 : ℝ), PeriodicTetherClosingBound ν := by
      intro ν' hν' u₀' hdiv' hsmooth' hper'
      exact (hpaper ν' hν').1 u₀' hsmooth' hdiv' hper'
    have hBKM : ∀ ν > (0 : ℝ), PeriodicBKMContinuation ν := by
      intro ν' hν' u₀' hdiv' hsmooth' hper' hY
      exact (hpaper ν' hν').2 u₀' hsmooth' hdiv' hper' hY
    obtain ⟨u, p, hsol⟩ := hformal hclose hBKM ν u₀ hν hsmooth hdiv hper
    exact ⟨u, p, hsol⟩
  · intro hpaper hclose hBKM ν u₀ hν hsmooth hdiv hper
    have hjoint : ∀ ν' : ℝ, 0 < ν' →
        (∀ u₀' : VelocityField,
            ContDiff ℝ (⊤ : ℕ∞) u₀' → (∀ x, div u₀' x = 0) → IsZ3Periodic u₀' →
              ∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
                IsPeriodicSmoothSolutionOn ν' T u₀' u p →
                  ∀ t ∈ Set.Ico (0 : ℝ) T, vorticity_sup_norm (vorticity (u t)) ≤ Y) ∧
        (∀ u₀' : VelocityField,
            ContDiff ℝ (⊤ : ℕ∞) u₀' → (∀ x, div u₀' x = 0) → IsZ3Periodic u₀' →
              (∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
                IsPeriodicSmoothSolutionOn ν' T u₀' u p →
                  ∀ t ∈ Set.Ico (0 : ℝ) T, vorticity_sup_norm (vorticity (u t)) ≤ Y) →
                ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
                  IsPeriodicSmoothSolution ν' u₀' (fun _ _ => 0) u p) := by
      intro ν' hν'
      refine ⟨?b1, ?b2⟩
      · intro u₀' hsmooth' hdiv' hper'
        exact hclose ν' hν' u₀' hdiv' hsmooth' hper'
      · intro u₀' hsmooth' hdiv' hper' hY
        exact hBKM ν' hν' u₀' hdiv' hsmooth' hper' hY
    obtain ⟨u, p, hsol⟩ := hpaper hjoint ν u₀ hν hsmooth hdiv hper
    exact ⟨u, p, hsol⟩
-- TRUTH-GATE LOCK END

/-- The main theorem proves `formal_claim`. -/
theorem formal_claim_holds : formal_claim :=
  fun hclose hBKM => clay_B_exact_of_periodic_tether_bound hclose hBKM

/-- The paper's claim, transported across the correspondence. -/
theorem paper_claim_holds : paper_claim :=
  intended_correspondence.mp formal_claim_holds

end TruthGate
