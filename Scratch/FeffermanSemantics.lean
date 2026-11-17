/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import Scratch.KatoContinuation

/-!
# Truth Gate locks for the Fefferman (A) paper (Scratch.FeffermanSemantics)

PAPER_PATH: papers/fefferman-clay-a-conditional/main.tex
PAPER_SHA256: 14179f79141f4a2b596f6fc08194be737e2f4bec8235d8f14bfc44175fa939dd
PAPER_SECTION: Theorem thm:kato-proved (Section "Kato infrastructure, and the proof of the Kato maximal solution", read through Definition def:kato), Theorem thm:r3bkm (same section), Theorem thm:clayA-rate (Section "The two rate hypotheses and the main conditional theorems", read through Definition def:smooth); terms from Section "Setting and conventions" and Section "Fefferman's Problem (A), stated literally"

Three locks, each `formal_claim_X ↔ paper_claim_X` with `X ∈ {kato, bkm, clayA}`:

* `kato`  — `KatoMaximal.katoMaximalSolution_of_feffermanDecay` ↔ Theorem `thm:kato-proved`;
* `bkm`   — `KatoContinuation.r3BKMContinuation_of_pos` ↔ Theorem `thm:r3bkm`;
* `clayA` — `KatoContinuation.clay_A_fefferman_of_rate` ↔ Theorem `thm:clayA-rate`.

Each `paper_claim_X` is written directly from the quoted English below, with the paper's own
symbols (`ν`, `u₀`, `u`, `p`, `ω`, `‖ω‖_∞ = sup_x |ω(x,t)|`, `S`, `C_k`, `T*` written `Tstar`,
`C`, `κ`). It does not name or unfold `formal_claim_X`, nor the repository Props
`KatoMaximalSolution`, `R3BKMContinuation`, `R3BKMContinuationAt`, `FrohmanianTetherRateSmooth`,
`Clay_A_Fefferman`, `FeffermanGlobalSolution`, `IsFeffermanSolutionOn`, `FeffermanDecay`, `Mω`,
`sobolevEnergy`, `hsSq` or `gradSup`; it uses only Mathlib and the basic Navier–Stokes operators
(`div`, `convective`, `pressureGradient`, `laplacian`, `vorticity`).

Verbatim quotes:

PAPER_QUOTE_BEGIN
Write
\[
M(t)\;:=\;\|\omega(t)\|_\infty
\;:=\;
\sup_{x\in\R^3}\bigl|\omega(x,t)\bigr|,
\]
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
Fefferman's official problem description~\cite{Fefferman} poses Problem~(A) as follows. Take $\nu>0$ and $n=3$. Let $u^\circ$ be a smooth divergence-free vector field on $\R^3$ satisfying
\begin{equation}
\tag{4}
\bigl|\partial_x^\alpha u^\circ(x)\bigr|
\le
C_{\alpha K}\,(1+|x|)^{-K}
\quad\text{on }\R^3,\text{ for any }\alpha,K.
\end{equation}
Take $f\equiv 0$. Then there exist smooth functions $p(x,t)$ and $u_i(x,t)$ on $\R^3\times[0,\infty)$ that satisfy (1)~(the momentum equation), (2)~($\operatorname{div}u=0$), (3)~($u(x,0)=u^\circ(x)$), (6)~($p,u\in C^\infty(\R^3\times[0,\infty))$) and (7)~($\int_{\R^3}|u(x,t)|^2\,dx<C$ for all $t\ge 0$).
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
The local solution class on which both rates are posed is \lean{IsFeffermanSolutionOn} (\lean{RepairedTetherRate.lean:56--65}): joint $C^\infty$ regularity of $(u,p)$ on $\R^3\times[0,T)$; the incompressible Navier--Stokes equations with $f\equiv 0$ and a one-sided time derivative at $t=0$; the initial condition $u(\cdot,0)=u_0$; and the energy inequality $\int_{\R^3}|u(t)|^2\le\int_{\R^3}|u_0|^2$, written as a comparison of lower Lebesgue integrals.
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
Throughout, Sobolev spaces are written $\Hs$, where $s\in\mathbb{N}$ is a nonnegative integer. (The letter $m$ is reserved for miscellaneous integers and is never used as a Sobolev index in the prose.) In the Lean development the same spaces appear as \lean{R3BKM.sobolevEnergy s} (spatial energy)
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{definition}[Smooth tether rate]
\label{def:smooth}
The proposition \lean{FrohmanianTetherRateSmooth} (\lean{Scratch/RepairedTetherRate.lean:74--81}) states: there exist $C,\kappa>0$, depending only on $u_0$ and $\nu$, such that along every local Fefferman-class solution issuing from $u_0$ on $[0,T)$, $M$ is finite and continuous on $[0,T)$, and at every $s\in[0,T)$ there is a right derivative $d$ of $M$ at $s$ satisfying $d\le C M(s)^2-\kappa M(s)^3$.
\end{definition}
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{definition}[Kato maximal solution]
\label{def:kato}
The proposition \lean{KatoMaximalSolution}\ $\nu$ $u_0$ (\lean{Scratch/R3BKMContinuation.lean:76--84}) states that there exist a time set $S$, fields $(u,p)$, and a constant $C_k\ge 0$, such that:
\begin{enumerate}[label=(\roman*)]
\item for every $T$ with $[0,T)\subseteq S$, the pair $(u,p)$ is an \lean{IsFeffermanSolutionOn} solution from $u_0$ on $[0,T)$;
\item $\|u(t)\|_{H^3}^2$ is finite for every $t\in S$, and the map $t\mapsto\|u(t)\|_{H^3}^2$ is continuous on $S$ and right-differentiable, with
\[
\frac{d}{dt}\|u\|_{H^3}^2
\;\le\;
C_k\,\|\nabla u\|_\infty\,\|u\|_{H^3}^2;
\]
\item either $S=[0,\infty)$, or $S=[0,T^*)$ for some $T^*\in(0,\infty)$ and $\|u\|_{H^3}^2$ is unbounded on $S$.
\end{enumerate}
\end{definition}
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{theorem}[Kato maximal solution for Fefferman data]
\label{thm:kato-proved}
Let $\nu>0$, and let $u_0$ be smooth, divergence-free, and satisfy Fefferman decay~(4). Then \lean{KatoMaximalSolution}\ $\nu$ $u_0$ holds in the sense of Definition~\ref{def:kato}: there exist a time set $S$, fields $(u,p)$ and a constant $C_k\ge 0$ satisfying (i)--(iii) of that definition. This is a maximal Fefferman-class solution with an $H^3$ blow-up alternative; it does not assert global regularity.
\end{theorem}
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{theorem}[Classical BKM continuation on $\R^3$]
\label{thm:r3bkm}
For every $\nu>0$, \lean{R3BKMContinuation}\ $\nu$ holds: for every smooth, divergence-free $u_0$ satisfying~(4), if one ceiling $Y$ bounds $\|\omega\|_\infty$ along every local Fefferman-class solution from $u_0$, that is, $\|\omega(t)\|_\infty$ is finite and $\|\omega(t)\|_\infty\le Y$ for every local Fefferman-class solution $(u,p)$ from $u_0$ on $[0,T)$ and every $t\in[0,T)$, then $u_0$ has a global Fefferman solution: smooth functions $p$ and $u$ on $\R^3\times[0,\infty)$ that satisfy (1), (2), (3), (6) and (7) of Section~\ref{sec:fefferman}. A uniform vorticity ceiling remains a hypothesis; this is not a regularity theorem.
\end{theorem}
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{theorem}[Conditional reduction to the Smooth rate alone]
\label{thm:clayA-rate}
Assume that for every $\nu>0$ and every Fefferman datum $u_0$ (smooth, divergence-free, satisfying~(4)), \lean{FrohmanianTetherRateSmooth}\ $u_0$ $\nu$ holds. Then \lean{Clay_A_Fefferman} holds. The rate hypothesis is not proved in this repository, so this does not establish \lean{Clay_A_Fefferman}.
\end{theorem}
PAPER_QUOTE_END

Reading of the paper's terms (fixed here, once):

* "smooth" is `ContDiff ℝ ∞`; "divergence-free" is `∀ x, div u₀ x = 0`; Fefferman decay (4)
  is written out with `∂ₓ^α` as the `k`-th Fréchet derivative applied to coordinate unit vectors;
* `‖ω(t)‖_∞ = M(t) = sup_x |ω(x,t)|` is `⨆ x, ‖vorticity (u t) x‖`; "`‖ω(t)‖_∞` is finite" is
  `BddAbove (Set.range fun x => ‖vorticity (u t) x‖)` (a real supremum is `0` on an unbounded
  range, Section 2);
* "local Fefferman-class solution from `u₀` on `[0,T)`" is written out from the paragraph quoted
  above (joint `C^∞`, momentum equation with `f ≡ 0` and one-sided `∂ₜ`, `div u = 0`,
  `u(·,0) = u₀`, energy inequality as lower Lebesgue integrals);
* "global Fefferman solution" is (1), (2), (3), (6), (7) of Problem (A), in that order;
* `‖u‖²_{H³}` is the paper's spatial energy (Section 2): the sum, over orders `k ≤ 3` and
  `α : Fin k → Fin 3`, of `∫ |∂_{α 0} ⋯ ∂_{α (k-1)} u(x)|² dx`; `‖∇u‖_∞` is `sup_x |∇u(x)|`;
* Definition `def:kato` (i)–(iii) and Definition `def:smooth` are written conjunct by conjunct in
  the order the paper states them.

Scope: Theorem `thm:kato-proved` is local Kato theory and does not assert global regularity.
Theorem `thm:r3bkm` is a conditional continuation statement: a uniform vorticity ceiling remains a
hypothesis. Theorem `thm:clayA-rate` is CONDITIONAL on `FrohmanianTetherRateSmooth` for all
Fefferman data, which is OPEN (not proved here); it does not establish `Clay_A_Fefferman`.
No Millennium Prize problem is claimed solved.

Approval: Benjamin Stanley Frohman approved the three sentences of these theorems and the locks
(2026-11-17 00:22 CT, "OK"; confirmed 00:32 CT, "yes fix and proceed!").
-/

open MeasureTheory NavierStokes3D FrohmanianTether RepairedTether R3BKM
open scoped ContDiff

noncomputable section

namespace TruthGateFefferman

-- TRUTH-GATE LOCK BEGIN
/-! ### Paper-side vocabulary, transcribed from the quoted English (not from the repository Props) -/

/-- "`u₀` smooth, divergence-free, and satisfying Fefferman decay (4)": `u₀ ∈ C^∞(ℝ³)`,
`div u₀ = 0`, and `|∂ₓ^α u₀(x)| ≤ C_{αK} (1 + |x|)^{-K}` for any `α` and `K`
(`∂ₓ^α`, `|α| = k`, is the `k`-th derivative applied to the unit vectors `e_{α 0}, …, e_{α (k-1)}`). -/
def paper_FeffermanDatum (u₀ : VelocityField) : Prop :=
  ContDiff ℝ ∞ u₀ ∧ (∀ x, div u₀ x = 0) ∧
    ∀ (k : ℕ) (α : Fin k → Fin 3) (K : ℝ), ∃ C : ℝ, ∀ x : T3,
      ‖iteratedFDeriv ℝ k u₀ x (fun j => EuclideanSpace.single (α j) (1 : ℝ))‖ ≤
        C * (1 + ‖x‖) ^ (-K)

/-- "Local Fefferman-class solution `(u, p)` from `u₀` on `[0, T)`": joint `C^∞` regularity of
`(u, p)` on `ℝ³ × [0, T)`; the incompressible Navier–Stokes equations with `f ≡ 0` and a one-sided
time derivative at `t = 0`; `u(·, 0) = u₀`; and `∫|u(t)|² ≤ ∫|u₀|²` as lower Lebesgue integrals. -/
def paper_FeffermanSolutionOn (ν T : ℝ) (u₀ : VelocityField)
    (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  ContDiffOn ℝ ∞ (fun q : T3 × ℝ => u q.2 q.1) (Set.univ ×ˢ Set.Ico (0 : ℝ) T) ∧
  ContDiffOn ℝ ∞ (fun q : T3 × ℝ => p q.2 q.1) (Set.univ ×ˢ Set.Ico (0 : ℝ) T) ∧
  (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : T3,
    derivWithin (fun s => u s x) (Set.Ici 0) t + convective (u t) (u t) x +
        pressureGradient (p t) x = ν • laplacian (u t) x + 0 ∧
      div (u t) x = 0) ∧
  (∀ x : T3, u 0 x = u₀ x) ∧
  (∀ t ∈ Set.Ico (0 : ℝ) T, ∫⁻ x, ‖u t x‖ₑ ^ 2 ≤ ∫⁻ x, ‖u₀ x‖ₑ ^ 2)

/-- "A global Fefferman solution": smooth `p` and `u` on `ℝ³ × [0, ∞)` satisfying, in the paper's
order, (1) the momentum equation with `f ≡ 0` (one-sided `∂ₜ` at `t = 0`), (2) `div u = 0`,
(3) `u(x, 0) = u₀(x)`, (6) `p, u ∈ C^∞(ℝ³ × [0, ∞))`, (7) `∫_{ℝ³} |u(x, t)|² dx < C` for all `t ≥ 0`. -/
def paper_GlobalSolution (ν : ℝ) (u₀ : VelocityField)
    (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  (∀ t ≥ (0 : ℝ), ∀ x : T3,
    derivWithin (fun s => u s x) (Set.Ici 0) t + convective (u t) (u t) x +
      pressureGradient (p t) x = ν • laplacian (u t) x + 0) ∧
  (∀ t ≥ (0 : ℝ), ∀ x : T3, div (u t) x = 0) ∧
  (∀ x : T3, u 0 x = u₀ x) ∧
  ContDiffOn ℝ ∞ (fun q : T3 × ℝ => p q.2 q.1) (Set.univ ×ˢ Set.Ici (0 : ℝ)) ∧
  ContDiffOn ℝ ∞ (fun q : T3 × ℝ => u q.2 q.1) (Set.univ ×ˢ Set.Ici (0 : ℝ)) ∧
  ∃ C : ℝ, ∀ t ≥ (0 : ℝ), ∫⁻ x, ‖u t x‖ₑ ^ 2 < ENNReal.ofReal C

/-- `‖f‖²_{H³}` as an extended real: the sum over orders `k ≤ 3` and all `α : Fin k → Fin 3`
of `∫ |∂_{α 0} ⋯ ∂_{α (k-1)} f(x)|² dx` (the paper's spatial energy, Section 2). -/
def paper_H3Energy (f : VelocityField) : ENNReal :=
  ∑ k ∈ Finset.range (3 + 1), ∑ α : Fin k → Fin 3,
    ∫⁻ x, ‖iteratedFDeriv ℝ k f x (fun j => EuclideanSpace.single (α j) (1 : ℝ))‖ₑ ^ 2

/-- `‖f‖²_{H³}` as a real number. -/
def paper_H3Sq (f : VelocityField) : ℝ := (paper_H3Energy f).toReal

/-- `‖∇f‖_∞ = sup_x |∇f(x)|`. -/
def paper_GradSup (f : VelocityField) : ℝ := ⨆ x, ‖fderiv ℝ f x‖

/-- Theorem `thm:kato-proved`, read through Definition `def:kato` (i)–(iii). Hypotheses in the
paper's order: `ν > 0`, then `u₀` smooth, divergence-free, satisfying (4). -/
def paper_claim_kato : Prop :=
  ∀ (ν : ℝ) (u₀ : VelocityField), 0 < ν → paper_FeffermanDatum u₀ →
    ∃ (S : Set ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure) (Ck : ℝ), 0 ≤ Ck ∧
      (∀ T : ℝ, Set.Ico (0 : ℝ) T ⊆ S → paper_FeffermanSolutionOn ν T u₀ u p) ∧
      (∀ t ∈ S, paper_H3Energy (u t) < ⊤) ∧
      ContinuousOn (fun t => paper_H3Sq (u t)) S ∧
      (∀ s ∈ S, ∃ d : ℝ, HasDerivWithinAt (fun t => paper_H3Sq (u t)) d (Set.Ici s) s ∧
        d ≤ Ck * paper_GradSup (u s) * paper_H3Sq (u s)) ∧
      (S = Set.Ici 0 ∨ ∃ Tstar : ℝ, 0 < Tstar ∧ S = Set.Ico 0 Tstar ∧
        ∀ B : ℝ, ∃ t ∈ S, B < paper_H3Sq (u t))

/-- Theorem `thm:r3bkm`: for every `ν > 0` and every smooth, divergence-free `u₀` satisfying (4),
if one ceiling `Y` bounds `‖ω‖_∞` (finite, and `‖ω(t)‖_∞ = sup_x |ω(x,t)| ≤ Y`) along every local
Fefferman-class solution from `u₀`, then `u₀` has a global Fefferman solution. -/
def paper_claim_bkm : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : VelocityField, paper_FeffermanDatum u₀ →
    (∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      paper_FeffermanSolutionOn ν T u₀ u p → ∀ t ∈ Set.Ico (0 : ℝ) T,
        BddAbove (Set.range fun x => ‖vorticity (u t) x‖) ∧ (⨆ x, ‖vorticity (u t) x‖) ≤ Y) →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure), paper_GlobalSolution ν u₀ u p

/-- Definition `def:smooth`: there exist `C, κ > 0` such that along every local Fefferman-class
solution from `u₀` on `[0, T)`, `M = ‖ω‖_∞` is finite and continuous on `[0, T)`, and at every
`s ∈ [0, T)` there is a right derivative `d` of `M` at `s` with `d ≤ C M(s)² − κ M(s)³`. -/
def paper_RateSmooth (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∃ C «κ» : ℝ, 0 < C ∧ 0 < «κ» ∧
    ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      paper_FeffermanSolutionOn ν T u₀ u p →
        (∀ t ∈ Set.Ico (0 : ℝ) T, BddAbove (Set.range fun x => ‖vorticity (u t) x‖)) ∧
        ContinuousOn (fun t => ⨆ x, ‖vorticity (u t) x‖) (Set.Ico (0 : ℝ) T) ∧
        (∀ s ∈ Set.Ico (0 : ℝ) T, ∃ d : ℝ,
          HasDerivWithinAt (fun t => ⨆ x, ‖vorticity (u t) x‖) d (Set.Ici s) s ∧
            d ≤ C * (⨆ x, ‖vorticity (u s) x‖) ^ 2 - «κ» * (⨆ x, ‖vorticity (u s) x‖) ^ 3)

/-- Theorem `thm:clayA-rate`: if `FrohmanianTetherRateSmooth u₀ ν` (Definition `def:smooth`)
holds for every `ν > 0` and every Fefferman datum `u₀`, then Fefferman's Problem (A) holds: for
every `ν > 0` and every smooth, divergence-free `u₀` satisfying (4) there is a global
Fefferman solution. -/
def paper_claim_clayA : Prop :=
  (∀ ν : ℝ, 0 < ν → ∀ u₀ : VelocityField, paper_FeffermanDatum u₀ → paper_RateSmooth u₀ ν) →
    ∀ (ν : ℝ) (u₀ : VelocityField), 0 < ν → paper_FeffermanDatum u₀ →
      ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure), paper_GlobalSolution ν u₀ u p

/-! ### Formal side: exactly the statements of the three locked theorems -/

/-- Statement of `KatoMaximal.katoMaximalSolution_of_feffermanDecay`. -/
def formal_claim_kato : Prop :=
  ∀ (u₀ : VelocityField), ContDiff ℝ ∞ u₀ → FeffermanDecay u₀ →
    ∀ (ν : ℝ), 0 < ν → (∀ x, div u₀ x = 0) → KatoMaximalSolution ν u₀

/-- Statement of `KatoContinuation.r3BKMContinuation_of_pos`. -/
def formal_claim_bkm : Prop :=
  ∀ (ν : ℝ), 0 < ν → R3BKMContinuation ν

/-- Statement of `KatoContinuation.clay_A_fefferman_of_rate`. -/
def formal_claim_clayA : Prop :=
  (∀ ν > (0 : ℝ), ∀ u₀ : VelocityField, ContDiff ℝ ∞ u₀ →
      (∀ x, div u₀ x = 0) → FeffermanDecay u₀ → FrohmanianTetherRateSmooth u₀ ν) →
    Clay_A_Fefferman

/-! ### Statement-level bridges (no theorem about Navier–Stokes is used) -/

/-- Fefferman's global solution, (6),(6),(1)+(2),(3),(7), versus the paper's order (1),(2),(3),(6),(7). -/
theorem globalSolution_iff (ν : ℝ) (u₀ : VelocityField) (u : TimeDependentVelocity)
    (p : TimeDependentPressure) :
    FeffermanGlobalSolution ν u₀ u p ↔ paper_GlobalSolution ν u₀ u p := by
  constructor
  · rintro ⟨hu, hp, hns, h0, hE⟩
    exact ⟨fun t ht x => (hns t ht x).1, fun t ht x => (hns t ht x).2, h0, hp, hu, hE⟩
  · rintro ⟨h1, h2, h0, hp, hu, hE⟩
    exact ⟨hu, hp, fun t ht x => ⟨h1 t ht x, h2 t ht x⟩, h0, hE⟩

/-- The repaired rate, conjuncts (continuity, derivative, finiteness), versus the paper's
order in `def:smooth` (finiteness, continuity, derivative). -/
theorem rateSmooth_iff (u₀ : VelocityField) (ν : ℝ) :
    FrohmanianTetherRateSmooth u₀ ν ↔ paper_RateSmooth u₀ ν := by
  constructor
  · rintro ⟨C, «κ», hC, hκ, h⟩
    refine ⟨C, «κ», hC, hκ, fun T u p hu => ?_⟩
    obtain ⟨hc, hd, hb⟩ := h T u p hu
    exact ⟨hb, hc, hd⟩
  · rintro ⟨C, «κ», hC, hκ, h⟩
    refine ⟨C, «κ», hC, hκ, fun T u p hu => ?_⟩
    obtain ⟨hb, hc, hd⟩ := h T u p hu
    exact ⟨hc, hd, hb⟩

/-- Fixed correspondence for `thm:kato-proved`. -/
theorem intended_correspondence_kato : formal_claim_kato ↔ paper_claim_kato := by
  constructor
  · intro h ν u₀ hν hdat
    obtain ⟨hs, hd, hdec⟩ := hdat
    exact h u₀ hs hdec ν hν hd
  · intro h u₀ hs hdec ν hν hd
    exact h ν u₀ hν ⟨hs, hd, hdec⟩

/-- Fixed correspondence for `thm:r3bkm`. -/
theorem intended_correspondence_bkm : formal_claim_bkm ↔ paper_claim_bkm := by
  constructor
  · intro h ν hν u₀ hdat hY
    obtain ⟨hs, hd, hdec⟩ := hdat
    obtain ⟨u, p, hg⟩ := h ν hν u₀ hs hd hdec hY
    exact ⟨u, p, (globalSolution_iff ν u₀ u p).1 hg⟩
  · intro h ν hν u₀ hs hd hdec hY
    obtain ⟨u, p, hg⟩ := h ν hν u₀ ⟨hs, hd, hdec⟩ hY
    exact ⟨u, p, (globalSolution_iff ν u₀ u p).2 hg⟩

/-- Fixed correspondence for `thm:clayA-rate`. -/
theorem intended_correspondence_clayA : formal_claim_clayA ↔ paper_claim_clayA := by
  constructor
  · intro h hrate ν u₀ hν hdat
    obtain ⟨hs, hd, hdec⟩ := hdat
    have hr : ∀ ν > (0 : ℝ), ∀ v : VelocityField, ContDiff ℝ ∞ v →
        (∀ x, div v x = 0) → FeffermanDecay v → FrohmanianTetherRateSmooth v ν :=
      fun ν' hν' v hs' hd' hdec' => (rateSmooth_iff v ν').2 (hrate ν' hν' v ⟨hs', hd', hdec'⟩)
    obtain ⟨u, p, hg⟩ := h hr ν u₀ hν hs hd hdec
    exact ⟨u, p, (globalSolution_iff ν u₀ u p).1 hg⟩
  · intro h hr ν u₀ hν hs hd hdec
    have hrate : ∀ ν : ℝ, 0 < ν → ∀ v : VelocityField, paper_FeffermanDatum v →
        paper_RateSmooth v ν := by
      intro ν' hν' v hv
      obtain ⟨hs', hd', hdec'⟩ := hv
      exact (rateSmooth_iff v ν').1 (hr ν' hν' v hs' hd' hdec')
    obtain ⟨u, p, hg⟩ := h hrate ν u₀ hν ⟨hs, hd, hdec⟩
    exact ⟨u, p, (globalSolution_iff ν u₀ u p).2 hg⟩
-- TRUTH-GATE LOCK END

/-! ### The locked theorems, and their transport to the paper side -/

theorem formal_claim_kato_holds : formal_claim_kato :=
  fun _u₀ hs hdec _ν hν hd => KatoMaximal.katoMaximalSolution_of_feffermanDecay hs hdec hν hd

theorem formal_claim_bkm_holds : formal_claim_bkm :=
  fun _ν hν => KatoContinuation.r3BKMContinuation_of_pos hν

theorem formal_claim_clayA_holds : formal_claim_clayA :=
  fun hrate => KatoContinuation.clay_A_fefferman_of_rate hrate

theorem paper_claim_kato_holds : paper_claim_kato :=
  intended_correspondence_kato.mp formal_claim_kato_holds

theorem paper_claim_bkm_holds : paper_claim_bkm :=
  intended_correspondence_bkm.mp formal_claim_bkm_holds

theorem paper_claim_clayA_holds : paper_claim_clayA :=
  intended_correspondence_clayA.mp formal_claim_clayA_holds

/-! ### Non-vacuity witnesses (the zero datum) -/

/-- The datum hypothesis of all three paper claims is satisfiable: `u₀ = 0`. -/
theorem paper_FeffermanDatum_zero : paper_FeffermanDatum 0 :=
  ⟨contDiff_zero_fun, fun x => div_zero_field x, feffermanDecay_zero⟩

/-- The rate hypothesis of `paper_claim_clayA` is satisfiable at `u₀ = 0`, for every `ν`. -/
theorem paper_RateSmooth_zero (ν : ℝ) : paper_RateSmooth 0 ν :=
  (rateSmooth_iff 0 ν).1 (frohmanianTetherRateSmooth_zero ν)

/-- The ceiling premise of `paper_claim_bkm` is satisfiable at `u₀ = 0`. -/
theorem paper_ceiling_zero (ν : ℝ) :
    ∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      paper_FeffermanSolutionOn ν T 0 u p → ∀ t ∈ Set.Ico (0 : ℝ) T,
        BddAbove (Set.range fun x => ‖vorticity (u t) x‖) ∧ (⨆ x, ‖vorticity (u t) x‖) ≤ Y :=
  ceiling_of_rate (frohmanianTetherRateSmooth_zero ν)

/-- The conclusion of `paper_claim_bkm` / `paper_claim_clayA` is satisfiable at `u₀ = 0`. -/
theorem paper_GlobalSolution_zero (ν : ℝ) :
    paper_GlobalSolution ν 0 (fun _ => 0) (fun _ => fun _ => (0 : ℝ)) :=
  (globalSolution_iff ν 0 _ _).1 (feffermanGlobalSolution_zero ν)

/-- The full instance: the paper's Kato conclusion at `ν = 1`, `u₀ = 0`. -/
theorem paper_kato_instance_zero :
    ∃ (S : Set ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure) (Ck : ℝ), 0 ≤ Ck ∧
      (∀ T : ℝ, Set.Ico (0 : ℝ) T ⊆ S → paper_FeffermanSolutionOn 1 T 0 u p) ∧
      (∀ t ∈ S, paper_H3Energy (u t) < ⊤) ∧
      ContinuousOn (fun t => paper_H3Sq (u t)) S ∧
      (∀ s ∈ S, ∃ d : ℝ, HasDerivWithinAt (fun t => paper_H3Sq (u t)) d (Set.Ici s) s ∧
        d ≤ Ck * paper_GradSup (u s) * paper_H3Sq (u s)) ∧
      (S = Set.Ici 0 ∨ ∃ Tstar : ℝ, 0 < Tstar ∧ S = Set.Ico 0 Tstar ∧
        ∀ B : ℝ, ∃ t ∈ S, B < paper_H3Sq (u t)) :=
  katoMaximalSolution_zero 1

end TruthGateFefferman

#print axioms TruthGateFefferman.intended_correspondence_kato
#print axioms TruthGateFefferman.intended_correspondence_bkm
#print axioms TruthGateFefferman.intended_correspondence_clayA
#print axioms TruthGateFefferman.paper_claim_kato_holds
#print axioms TruthGateFefferman.paper_claim_bkm_holds
#print axioms TruthGateFefferman.paper_claim_clayA_holds
#print axioms TruthGateFefferman.paper_FeffermanDatum_zero
#print axioms TruthGateFefferman.paper_RateSmooth_zero
#print axioms TruthGateFefferman.paper_ceiling_zero
#print axioms TruthGateFefferman.paper_GlobalSolution_zero
#print axioms TruthGateFefferman.paper_kato_instance_zero
