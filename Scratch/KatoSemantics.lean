/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import Scratch.KatoContinuation
import Scratch.KatoMaximalProperties

/-!
# Truth Gate locks for the local Kato paper (Scratch.KatoSemantics)

PAPER_PATH: papers/local-kato-theory/main.tex
PAPER_SHA256: 176853c29a9b0f21e3d09dbd0f332b0539cdd870cf2a24e3e449cdc81750fa8f
PAPER_SECTION: Theorem thm:T1 (Section "The main theorem", read through Definition def:kato), Theorem thm:T2-9 with items (T2)-(T9) (Section "Properties on the maximal time set"), Theorems thm:T10 and thm:T11 (Section "Two conditional statements"); terms from Section "Setting and notation"

Four locks, each `formal_claim_X ↔ paper_claim_X` with `X ∈ {T1, T2to9, T10, T11}`:

* `T1`    — `KatoMaximal.katoMaximalSolution_of_feffermanDecay` ↔ Theorem `thm:T1`;
* `T2to9` — `KatoMaximal.katoMaximalSolution_properties` ↔ Theorem `thm:T2-9`, items (T2)–(T9);
* `T10`   — `KatoContinuation.r3BKMContinuation_of_pos` ↔ Theorem `thm:T10`;
* `T11`   — `KatoContinuation.clay_A_fefferman_of_rate` ↔ Theorem `thm:T11`.

Each `paper_claim_X` is written from the quoted English below, with the paper's symbols (`ν`, `u₀`,
`u`, `p`, `S`, `S_k`, `C_k` written `Ck`, `T*` written `Tstar`, `∂^α`, `‖·‖²_{H³}`, `‖∇·‖_∞`,
`‖ω‖_∞`). It does not name or unfold any `formal_claim_X`, nor the repository Props and
definitions `KatoMaximalSolution`, `R3BKMContinuation`, `R3BKMContinuationAt`,
`FrohmanianTetherRateSmooth`, `Clay_A_Fefferman`, `FeffermanGlobalSolution`,
`IsFeffermanSolutionOn`, `FeffermanDecay`, `H3IBPVanishingFlux`, `WordIBP`,
`ViscousDissipationIBP`, `PartialIBP`, `wordDeriv`, `wordDerivScalar`, `convectiveCommutator`,
`directionalCoord`, `Mω`, `sobolevEnergy`, `hsSq`, `gradSup`, `Smax`, `inMaximal`,
`physicalMaximal` or `presMaximal`; it uses only Mathlib and the basic Navier–Stokes operators
(`div`, `convective` = `(u·∇)v`, `pressureGradient` = `∇p`, `laplacian` = `Δ`, `vorticity` = `ω`).

The rate hypothesis of Theorem `thm:T11` is stated in words in Definition `def:rate` (quoted
below) and quoted in `lean/DRate.lean`; `paper_RateSmooth` transcribes it conjunct by conjunct.

Verbatim quotes:

PAPER_QUOTE_BEGIN
\begin{definition}[Fefferman decay (4)] \lean{Scratch/RepairedTetherRate.lean:33--36}: $|\partial_x^\alpha u_0(x)|\le C_{\alpha K}(1+|x|)^{-K}$ for every multi-index $\alpha$ and every real $K$.
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{definition}[Local Fefferman-class solution on $\R^3\times[0,T)$] \lean{Scratch/RepairedTetherRate.lean:66--75}: $u$ and $p$ are jointly $C^\infty$ on $\R^3\times[0,T)$; for $t\in[0,T)$ and $x\in\R^3$, $\partial_t^+u+(u\cdot\nabla)u+\nabla p=\nu\Delta u$ (one-sided time derivative within $[0,\infty)$) and $\operatorname{div}u=0$; $u(\cdot,0)=u_0$; and $\int_{\R^3}|u(x,t)|^2\,dx\le\int_{\R^3}|u_0(x)|^2\,dx$ for $t\in[0,T)$, as lower Lebesgue integrals.
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{definition}[$H^3$ energy and $\|\nabla u\|_\infty$] \lean{Scratch/R3BKMContinuation.lean:44--55}. Throughout this paper $\|f\|_{H^m}^2$ denotes \lean{hsSq m f}, the real value of
$\sum_{k\le m}\sum_{\alpha:\{0,\dots,k-1\}\to\{1,2,3\}}\int_{\R^3}|\partial_{\alpha_0}\cdots\partial_{\alpha_{k-1}}f(x)|^2\,dx$ (ordered tuples of directions), and $\|\nabla f\|_\infty$ denotes \lean{gradSup f}$\,=\sup_x\|Df(x)\|$ as a real supremum.
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{definition}[Kato maximal solution]\label{def:kato} \lean{Scratch/R3BKMContinuation.lean:88--96}. \lean{KatoMaximalSolution ν u₀} states that there exist a time set $S$, fields $(u,p)$ and a constant $C_k\ge 0$ such that:
\begin{enumerate}[label=(\roman*)]
\item for every $T$ with $[0,T)\subseteq S$, $(u,p)$ is a local Fefferman-class solution from $u_0$ on $[0,T)$;
\item $\|u(t)\|_{H^3}^2<\infty$ for every $t\in S$; the map $t\mapsto\|u(t)\|_{H^3}^2$ is continuous on $S$; and at every $s\in S$ it has a right derivative $d$ (derivative within $[s,\infty)$) with $d\le C_k\,\|\nabla u(s)\|_\infty\,\|u(s)\|_{H^3}^2$;
\item either $S=[0,\infty)$, or $S=[0,T^*)$ for some $T^*>0$ and for every $B\in\R$ there is $t\in S$ with $\|u(t)\|_{H^3}^2>B$.
\end{enumerate}
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
Let $\nu>0$, and let $u_0$ be smooth, divergence-free, and satisfy Fefferman decay~(4). Then \lean{KatoMaximalSolution}\ $\nu$ $u_0$ holds in the sense of Definition~\ref{def:kato}: there exist a time set $S$, fields $(u,p)$ and a constant $C_k\ge 0$ satisfying (i)--(iii) of that definition. This is a maximal Fefferman-class solution with an $H^3$ blow-up alternative; it does not assert global regularity.
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
Let $\nu>0$, and let $u_0$ be smooth, divergence-free, and satisfy Fefferman decay~(4). Then there exist time sets $S_k\subseteq\R$ $(k\in\mathbb{N})$, fields $(u,p)$ and a constant $C_k\ge 0$ such that, with $S:=S_2$, $\|u(t)\|_{H^3}^2<\infty$ for every $t\in S$, and:
\begin{enumerate}[label=(T\arabic*),start=2,leftmargin=*]
\item\label{thm:T2} at every $s\in S$ the map $t\mapsto\|u(t)\|_{H^3}^2$ has a right derivative $d$ at $s$ (derivative within $[s,\infty)$) with $d\le C_k\,\|\nabla u(s)\|_\infty\,\|u(s)\|_{H^3}^2$;
\item\label{thm:T3} for every $t\in S$, every order $n\le 3$ and every $\alpha\in\{1,2,3\}^n$, writing $v=\partial^\alpha u(t)$, $q=\partial^\alpha p(t)$ and $E=\tfrac12|v|^2$: the functions $\langle u(t),\nabla E\rangle$, $(\operatorname{div}u(t))\,E$, $\langle v,\nabla q\rangle$ and $(\operatorname{div}v)\,q$ are integrable on $\R^3$; $\int_{\R^3}\operatorname{div}(E\,u(t))\,dx=0$ and $\int_{\R^3}\operatorname{div}(q\,v)\,dx=0$; $v$ is $C^2$; for all $i,j\in\{1,2,3\}$, with $\varphi=v_j$ and $\psi=\partial_i v_j$, both $\varphi$ and $\psi$ are differentiable at every point, $\varphi\,\partial_i\psi$ and $\psi\,\partial_i\varphi$ are integrable, and $\int_{\R^3}\operatorname{div}(\varphi\psi\,e_i)\,dx=0$; and the functions $\langle v,\Delta v\rangle$, $\langle v,(u(t)\cdot\nabla)v\rangle$, $\langle v,\partial^\alpha((u(t)\cdot\nabla)u(t))-(u(t)\cdot\nabla)v\rangle$, $\langle v,\partial^\alpha((u(t)\cdot\nabla)u(t))\rangle$, $\langle v,\partial^\alpha\nabla p(t)\rangle$ and $\langle v,\partial^\alpha\Delta u(t)\rangle$ are integrable;
\item\label{thm:T4} for every $T$ with $[0,T)\subseteq S$, $(u,p)$ is a local Fefferman-class solution from $u_0$ on $[0,T)$;
\item\label{thm:T5} for every $T$ with $[0,T)\subseteq S$, every $t\in[0,T)$ and every $x\in\R^3$, $\partial_t^+u(x,t)+(u(t)\cdot\nabla)u(t)(x)+\nabla p(t)(x)=\nu\,\Delta u(t)(x)$, with the time derivative taken within $[0,\infty)$;
\item\label{thm:T6} for every $T$ with $[0,T)\subseteq S$ and every $t\in[0,T)$, $\int_{\R^3}|u(x,t)|^2\,dx\le\int_{\R^3}|u_0(x)|^2\,dx$ (lower Lebesgue integrals);
\item\label{thm:T7} for every $k\ge 2$, $t\mapsto\|u(t)\|_{H^3}^2$ is continuous on $S_k$;
\item\label{thm:T8} for every $k\ge 2$, either $S_k=[0,\infty)$, or there is $T^*>0$ with $S_k=[0,T^*)$ and, for every $B\in\R$, some $t\in[0,T^*)$ with $\|u(t)\|_{H^3}^2>B$;
\item\label{thm:T9} for every $k\ge 2$, either $S_k=[0,\infty)$ or $S_k=[0,T^*)$ for some $T^*>0$.
\end{enumerate}
Here $\partial^\alpha f(x)$, for $\alpha=(\alpha_0,\dots,\alpha_{n-1})$, is the $n$-th derivative of $f$ at $x$ applied to $e_{\alpha_0},\dots,e_{\alpha_{n-1}}$, and $\partial_i$ is the derivative in direction $e_i$.
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
For every $\nu>0$, \lean{R3BKMContinuation}\ $\nu$ holds: for every smooth, divergence-free $u_0$ satisfying~(4), if one ceiling $Y$ bounds $\|\omega\|_\infty$ along every local Fefferman-class solution from $u_0$, that is, $\|\omega(t)\|_\infty$ is finite and $\|\omega(t)\|_\infty\le Y$ for every local Fefferman-class solution $(u,p)$ from $u_0$ on $[0,T)$ and every $t\in[0,T)$, then $u_0$ has a global Fefferman solution: smooth functions $p$ and $u$ on $\R^3\times[0,\infty)$ that satisfy (1), (2), (3), (6) and (7) of Fefferman's problem description. A uniform vorticity ceiling remains a hypothesis; this is not a regularity theorem.
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
Assume that for every $\nu>0$ and every Fefferman datum $u_0$ (smooth, divergence-free, satisfying~(4)), the smooth rate condition of Definition~\ref{def:rate} holds for $u_0$ and $\nu$. Then \lean{Clay\_A\_Fefferman} holds. The rate hypothesis is not proved in this repository, so this does not establish \lean{Clay\_A\_Fefferman}.
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{definition}[Smooth rate condition]\label{def:rate} \lean{FrohmanianTetherRateSmooth}\ $u_0$ $\nu$ (\lean{lean/DRate.lean}, quoted above) states: there are constants $C>0$ and $\kappa>0$ such that for every $T$ and every local Fefferman-class solution $(u,p)$ from $u_0$ on $[0,T)$, $\|\omega(t)\|_\infty=\sup_{x\in\R^3}|\omega(x,t)|$ is finite for every $t\in[0,T)$, the function $t\mapsto\|\omega(t)\|_\infty$ is continuous on $[0,T)$, and at every $s\in[0,T)$ it has a right derivative $d$ within $[s,\infty)$ with $d\le C\|\omega(s)\|_\infty^2-\kappa\|\omega(s)\|_\infty^3$.
PAPER_QUOTE_END

Scope: local Kato theory; no global regularity. Theorem `thm:T10` keeps a uniform vorticity ceiling
as a hypothesis. Theorem `thm:T11` is CONDITIONAL on `FrohmanianTetherRateSmooth` for all Fefferman
data, which is not proved. No Millennium Prize problem is claimed solved.
-/

open MeasureTheory NavierStokes3D FrohmanianTether RepairedTether R3BKM
open scoped ContDiff

noncomputable section

namespace TruthGateKato

-- TRUTH-GATE LOCK BEGIN
/-! ### Paper-side vocabulary, transcribed from the quoted English -/

/-- `∂^α f(x)` for `α ∈ {1,2,3}^n`: the `n`-th derivative of `f` at `x` applied to
`e_{α 0}, …, e_{α (n-1)}`. -/
def paper_D (n : ℕ) (α : Fin n → Fin 3) (f : VelocityField) : VelocityField :=
  fun x => iteratedFDeriv ℝ n f x (fun j => EuclideanSpace.single (α j) (1 : ℝ))

/-- `∂^α q(x)` for a scalar field `q`. -/
def paper_Ds (n : ℕ) (α : Fin n → Fin 3) (q : PressureField) : PressureField :=
  fun x => iteratedFDeriv ℝ n q x (fun j => EuclideanSpace.single (α j) (1 : ℝ))

/-- "`u₀` smooth, divergence-free, and satisfying Fefferman decay (4)". -/
def paper_FeffermanDatum (u₀ : VelocityField) : Prop :=
  ContDiff ℝ ∞ u₀ ∧ (∀ x, div u₀ x = 0) ∧
    ∀ (n : ℕ) (α : Fin n → Fin 3) (K : ℝ), ∃ C : ℝ, ∀ x : T3,
      ‖paper_D n α u₀ x‖ ≤ C * (1 + ‖x‖) ^ (-K)

/-- "Local Fefferman-class solution `(u,p)` from `u₀` on `ℝ³ × [0,T)`". -/
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

/-- Smooth `p`, `u` on `ℝ³ × [0, ∞)` with (1), (2), (3), (6), (7) of Fefferman's description. -/
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

/-- `‖f‖²_{H³}` as an extended real: `∑_{n ≤ 3} ∑_{α} ∫ |∂^α f(x)|² dx`. -/
def paper_H3Energy (f : VelocityField) : ENNReal :=
  ∑ n ∈ Finset.range (3 + 1), ∑ α : Fin n → Fin 3, ∫⁻ x, ‖paper_D n α f x‖ₑ ^ 2

/-- `‖f‖²_{H³}` as a real number. -/
def paper_H3Sq (f : VelocityField) : ℝ := (paper_H3Energy f).toReal

/-- `‖∇f‖_∞ = sup_x ‖Df(x)‖`. -/
def paper_GradSup (f : VelocityField) : ℝ := ⨆ x, ‖fderiv ℝ f x‖

/-- Item (T3): for every order `n ≤ 3` and `α ∈ {1,2,3}^n`, with `v = ∂^α u`, `q = ∂^α p`,
`E = ½|v|²`, the integrability and zero-flux conditions listed in the paper, in that order. -/
def paper_FluxPackage (u : VelocityField) (p : PressureField) : Prop :=
  ∀ n ∈ Finset.range 4, ∀ α : Fin n → Fin 3,
    Integrable (fun x => inner ℝ (u x)
      (gradient (fun y => (1 / 2 : ℝ) * ‖paper_D n α u y‖ ^ 2) x)) ∧
    Integrable (fun x => div u x * ((1 / 2 : ℝ) * ‖paper_D n α u x‖ ^ 2)) ∧
    (∫ x, div (fun y => ((1 / 2 : ℝ) * ‖paper_D n α u y‖ ^ 2) • u y) x = 0) ∧
    Integrable (fun x => inner ℝ (paper_D n α u x) (gradient (paper_Ds n α p) x)) ∧
    Integrable (fun x => div (paper_D n α u) x * paper_Ds n α p x) ∧
    (∫ x, div (fun y => paper_Ds n α p y • paper_D n α u y) x = 0) ∧
    (ContDiff ℝ 2 (paper_D n α u) ∧
      (∀ i j : Fin 3,
        (∀ x, DifferentiableAt ℝ (fun y => paper_D n α u y j) x) ∧
        (∀ x, DifferentiableAt ℝ
          (fun y => (fderiv ℝ (fun z => paper_D n α u z j) y) (EuclideanSpace.single i 1)) x) ∧
        Integrable (fun x => paper_D n α u x j *
          (fderiv ℝ (fun y => (fderiv ℝ (fun z => paper_D n α u z j) y)
            (EuclideanSpace.single i 1)) x) (EuclideanSpace.single i (1 : ℝ))) ∧
        Integrable (fun x => (fderiv ℝ (fun z => paper_D n α u z j) x)
            (EuclideanSpace.single i 1) *
          (fderiv ℝ (fun y => paper_D n α u y j) x) (EuclideanSpace.single i (1 : ℝ))) ∧
        (∫ x, div (fun y => (paper_D n α u y j *
            (fderiv ℝ (fun z => paper_D n α u z j) y) (EuclideanSpace.single i 1)) •
              EuclideanSpace.single i (1 : ℝ)) x = 0)) ∧
      Integrable (fun x => inner ℝ (paper_D n α u x) (laplacian (paper_D n α u) x))) ∧
    Integrable (fun x => inner ℝ (paper_D n α u x) (laplacian (paper_D n α u) x)) ∧
    Integrable (fun x => inner ℝ (paper_D n α u x) (convective u (paper_D n α u) x)) ∧
    Integrable (fun x => inner ℝ (paper_D n α u x)
      (paper_D n α (convective u u) x - convective u (paper_D n α u) x)) ∧
    Integrable (fun x => inner ℝ (paper_D n α u x) (paper_D n α (convective u u) x)) ∧
    Integrable (fun x => inner ℝ (paper_D n α u x) (paper_D n α (pressureGradient p) x)) ∧
    Integrable (fun x => inner ℝ (paper_D n α u x) (paper_D n α (laplacian u) x))

/-- Theorem `thm:T1`, read through Definition `def:kato` (i)–(iii). -/
def paper_claim_T1 : Prop :=
  ∀ (ν : ℝ) (u₀ : VelocityField), 0 < ν → paper_FeffermanDatum u₀ →
    ∃ (S : Set ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure) (Ck : ℝ), 0 ≤ Ck ∧
      (∀ T : ℝ, Set.Ico (0 : ℝ) T ⊆ S → paper_FeffermanSolutionOn ν T u₀ u p) ∧
      (∀ t ∈ S, paper_H3Energy (u t) < ⊤) ∧
      ContinuousOn (fun t => paper_H3Sq (u t)) S ∧
      (∀ s ∈ S, ∃ d : ℝ, HasDerivWithinAt (fun t => paper_H3Sq (u t)) d (Set.Ici s) s ∧
        d ≤ Ck * paper_GradSup (u s) * paper_H3Sq (u s)) ∧
      (S = Set.Ici 0 ∨ ∃ Tstar : ℝ, 0 < Tstar ∧ S = Set.Ico 0 Tstar ∧
        ∀ B : ℝ, ∃ t ∈ S, B < paper_H3Sq (u t))

/-- Theorem `thm:T2-9`, items (T2)–(T9), for one solution with `S = S_2`. -/
def paper_claim_T2to9 : Prop :=
  ∀ (ν : ℝ) (u₀ : VelocityField), 0 < ν → paper_FeffermanDatum u₀ →
    ∃ (S : ℕ → Set ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure) (Ck : ℝ),
      0 ≤ Ck ∧
      (∀ t ∈ S 2, paper_H3Energy (u t) < ⊤) ∧
      (∀ s ∈ S 2, ∃ d : ℝ, HasDerivWithinAt (fun t => paper_H3Sq (u t)) d (Set.Ici s) s ∧
        d ≤ Ck * paper_GradSup (u s) * paper_H3Sq (u s)) ∧
      (∀ t ∈ S 2, paper_FluxPackage (u t) (p t)) ∧
      (∀ T : ℝ, Set.Ico (0 : ℝ) T ⊆ S 2 → paper_FeffermanSolutionOn ν T u₀ u p) ∧
      (∀ T : ℝ, Set.Ico (0 : ℝ) T ⊆ S 2 → ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : T3,
        derivWithin (fun s => u s x) (Set.Ici 0) t + convective (u t) (u t) x +
            pressureGradient (p t) x = ν • laplacian (u t) x + 0) ∧
      (∀ T : ℝ, Set.Ico (0 : ℝ) T ⊆ S 2 → ∀ t ∈ Set.Ico (0 : ℝ) T,
        ∫⁻ x, ‖u t x‖ₑ ^ 2 ≤ ∫⁻ x, ‖u₀ x‖ₑ ^ 2) ∧
      (∀ k : ℕ, 2 ≤ k → ContinuousOn (fun t => paper_H3Sq (u t)) (S k)) ∧
      (∀ k : ℕ, 2 ≤ k → S k = Set.Ici (0 : ℝ) ∨
        ∃ Tstar : ℝ, 0 < Tstar ∧ S k = Set.Ico 0 Tstar ∧
          ∀ B : ℝ, ∃ t, t ∈ Set.Ico (0 : ℝ) Tstar ∧ B < paper_H3Sq (u t)) ∧
      (∀ k : ℕ, 2 ≤ k → S k = Set.Ici (0 : ℝ) ∨
        ∃ Tstar : ℝ, 0 < Tstar ∧ S k = Set.Ico 0 Tstar)

/-- Theorem `thm:T10`. -/
def paper_claim_T10 : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : VelocityField, paper_FeffermanDatum u₀ →
    (∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      paper_FeffermanSolutionOn ν T u₀ u p → ∀ t ∈ Set.Ico (0 : ℝ) T,
        BddAbove (Set.range fun x => ‖vorticity (u t) x‖) ∧ (⨆ x, ‖vorticity (u t) x‖) ≤ Y) →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure), paper_GlobalSolution ν u₀ u p

/-- The quoted definition `FrohmanianTetherRateSmooth u₀ ν` (`lean/DRate.lean`). -/
def paper_RateSmooth (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∃ C «κ» : ℝ, 0 < C ∧ 0 < «κ» ∧
    ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      paper_FeffermanSolutionOn ν T u₀ u p →
        (∀ t ∈ Set.Ico (0 : ℝ) T, BddAbove (Set.range fun x => ‖vorticity (u t) x‖)) ∧
        ContinuousOn (fun t => ⨆ x, ‖vorticity (u t) x‖) (Set.Ico (0 : ℝ) T) ∧
        (∀ s ∈ Set.Ico (0 : ℝ) T, ∃ d : ℝ,
          HasDerivWithinAt (fun t => ⨆ x, ‖vorticity (u t) x‖) d (Set.Ici s) s ∧
            d ≤ C * (⨆ x, ‖vorticity (u s) x‖) ^ 2 - «κ» * (⨆ x, ‖vorticity (u s) x‖) ^ 3)

/-- Theorem `thm:T11`. -/
def paper_claim_T11 : Prop :=
  (∀ ν : ℝ, 0 < ν → ∀ u₀ : VelocityField, paper_FeffermanDatum u₀ → paper_RateSmooth u₀ ν) →
    ∀ (ν : ℝ) (u₀ : VelocityField), 0 < ν → paper_FeffermanDatum u₀ →
      ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure), paper_GlobalSolution ν u₀ u p

/-! ### Formal side: exactly the statements of the four locked theorems -/

def formal_claim_T1 : Prop :=
  ∀ (u₀ : VelocityField), ContDiff ℝ ∞ u₀ → FeffermanDecay u₀ →
    ∀ (ν : ℝ), 0 < ν → (∀ x, div u₀ x = 0) → KatoMaximalSolution ν u₀

def formal_claim_T2to9 : Prop :=
  ∀ (u₀ : VelocityField), ContDiff ℝ ∞ u₀ → FeffermanDecay u₀ →
    ∀ (ν : ℝ), 0 < ν → (∀ x, div u₀ x = 0) →
    ∃ (S : ℕ → Set ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure) (Ck : ℝ),
      0 ≤ Ck ∧
      (∀ t ∈ S 2, sobolevEnergy 3 (u t) < ⊤) ∧
      (∀ s ∈ S 2, ∃ d : ℝ, HasDerivWithinAt (fun t => hsSq 3 (u t)) d (Set.Ici s) s ∧
        d ≤ Ck * gradSup (u s) * hsSq 3 (u s)) ∧
      (∀ t ∈ S 2, KatoPonce.H3IBPVanishingFlux (u t) (p t)) ∧
      (∀ T : ℝ, Set.Ico (0 : ℝ) T ⊆ S 2 → IsFeffermanSolutionOn ν T u₀ u p) ∧
      (∀ T : ℝ, Set.Ico (0 : ℝ) T ⊆ S 2 → ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : T3,
        derivWithin (fun s => u s x) (Set.Ici 0) t + convective (u t) (u t) x +
            pressureGradient (p t) x = ν • laplacian (u t) x + 0) ∧
      (∀ T : ℝ, Set.Ico (0 : ℝ) T ⊆ S 2 → ∀ t ∈ Set.Ico (0 : ℝ) T,
        ∫⁻ x, ‖u t x‖ₑ ^ 2 ≤ ∫⁻ x, ‖u₀ x‖ₑ ^ 2) ∧
      (∀ k : ℕ, 2 ≤ k → ContinuousOn (fun t => hsSq 3 (u t)) (S k)) ∧
      (∀ k : ℕ, 2 ≤ k → S k = Set.Ici (0 : ℝ) ∨
        ∃ Tstar : ℝ, 0 < Tstar ∧ S k = Set.Ico 0 Tstar ∧
          ∀ B : ℝ, ∃ t, t ∈ Set.Ico (0 : ℝ) Tstar ∧ B < hsSq 3 (u t)) ∧
      (∀ k : ℕ, 2 ≤ k → S k = Set.Ici (0 : ℝ) ∨
        ∃ Tstar : ℝ, 0 < Tstar ∧ S k = Set.Ico 0 Tstar)

def formal_claim_T10 : Prop :=
  ∀ (ν : ℝ), 0 < ν → R3BKMContinuation ν

def formal_claim_T11 : Prop :=
  (∀ ν > (0 : ℝ), ∀ u₀ : VelocityField, ContDiff ℝ ∞ u₀ →
      (∀ x, div u₀ x = 0) → FeffermanDecay u₀ → FrohmanianTetherRateSmooth u₀ ν) →
    Clay_A_Fefferman

/-! ### Statement-level bridges (no theorem about Navier–Stokes is used) -/

theorem fluxPackage_iff (u : VelocityField) (p : PressureField) :
    KatoPonce.H3IBPVanishingFlux u p ↔ paper_FluxPackage u p := by
  constructor
  · intro h n hn α
    obtain ⟨h1, h2, h3, h4, h5, h6, ⟨hc2, hpi, hii⟩, h8, h9, h10, h11, h12, h13⟩ := h n hn α
    refine ⟨h1, h2, h3, h4, h5, h6, ⟨hc2, fun i j => ?_, hii⟩, h8, h9, h10, h11, h12, h13⟩
    obtain ⟨a, b, c, d, e⟩ := hpi i j
    exact ⟨a, b, c, d, e⟩
  · intro h n hn α
    obtain ⟨h1, h2, h3, h4, h5, h6, ⟨hc2, hpi, hii⟩, h8, h9, h10, h11, h12, h13⟩ := h n hn α
    refine ⟨h1, h2, h3, h4, h5, h6, ⟨hc2, fun i j => ?_, hii⟩, h8, h9, h10, h11, h12, h13⟩
    obtain ⟨a, b, c, d, e⟩ := hpi i j
    exact ⟨a, b, c, d, e⟩

theorem globalSolution_iff (ν : ℝ) (u₀ : VelocityField) (u : TimeDependentVelocity)
    (p : TimeDependentPressure) :
    FeffermanGlobalSolution ν u₀ u p ↔ paper_GlobalSolution ν u₀ u p := by
  constructor
  · rintro ⟨hu, hp, hns, h0, hE⟩
    exact ⟨fun t ht x => (hns t ht x).1, fun t ht x => (hns t ht x).2, h0, hp, hu, hE⟩
  · rintro ⟨h1, h2, h0, hp, hu, hE⟩
    exact ⟨hu, hp, fun t ht x => ⟨h1 t ht x, h2 t ht x⟩, h0, hE⟩

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

theorem intended_correspondence_T1 : formal_claim_T1 ↔ paper_claim_T1 := by
  constructor
  · intro h ν u₀ hν hdat
    obtain ⟨hs, hd, hdec⟩ := hdat
    exact h u₀ hs hdec ν hν hd
  · intro h u₀ hs hdec ν hν hd
    exact h ν u₀ hν ⟨hs, hd, hdec⟩

theorem intended_correspondence_T2to9 : formal_claim_T2to9 ↔ paper_claim_T2to9 := by
  constructor
  · intro h ν u₀ hν hdat
    obtain ⟨hs, hd, hdec⟩ := hdat
    obtain ⟨S, u, p, Ck, hCk, hfin, hKP, hflux, hsol, hmom, hen, hcont, hblow, hshape⟩ :=
      h u₀ hs hdec ν hν hd
    exact ⟨S, u, p, Ck, hCk, hfin, hKP, fun t ht => (fluxPackage_iff (u t) (p t)).1 (hflux t ht),
      hsol, hmom, hen, hcont, hblow, hshape⟩
  · intro h u₀ hs hdec ν hν hd
    obtain ⟨S, u, p, Ck, hCk, hfin, hKP, hflux, hsol, hmom, hen, hcont, hblow, hshape⟩ :=
      h ν u₀ hν ⟨hs, hd, hdec⟩
    exact ⟨S, u, p, Ck, hCk, hfin, hKP, fun t ht => (fluxPackage_iff (u t) (p t)).2 (hflux t ht),
      hsol, hmom, hen, hcont, hblow, hshape⟩

theorem intended_correspondence_T10 : formal_claim_T10 ↔ paper_claim_T10 := by
  constructor
  · intro h ν hν u₀ hdat hY
    obtain ⟨hs, hd, hdec⟩ := hdat
    obtain ⟨u, p, hg⟩ := h ν hν u₀ hs hd hdec hY
    exact ⟨u, p, (globalSolution_iff ν u₀ u p).1 hg⟩
  · intro h ν hν u₀ hs hd hdec hY
    obtain ⟨u, p, hg⟩ := h ν hν u₀ ⟨hs, hd, hdec⟩ hY
    exact ⟨u, p, (globalSolution_iff ν u₀ u p).2 hg⟩

theorem intended_correspondence_T11 : formal_claim_T11 ↔ paper_claim_T11 := by
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

theorem formal_claim_T1_holds : formal_claim_T1 :=
  fun _u₀ hs hdec _ν hν hd => KatoMaximal.katoMaximalSolution_of_feffermanDecay hs hdec hν hd

theorem formal_claim_T2to9_holds : formal_claim_T2to9 :=
  KatoMaximal.katoMaximalSolution_properties

theorem formal_claim_T10_holds : formal_claim_T10 :=
  fun _ν hν => KatoContinuation.r3BKMContinuation_of_pos hν

theorem formal_claim_T11_holds : formal_claim_T11 :=
  fun hrate => KatoContinuation.clay_A_fefferman_of_rate hrate

theorem paper_claim_T1_holds : paper_claim_T1 :=
  intended_correspondence_T1.mp formal_claim_T1_holds

theorem paper_claim_T2to9_holds : paper_claim_T2to9 :=
  intended_correspondence_T2to9.mp formal_claim_T2to9_holds

theorem paper_claim_T10_holds : paper_claim_T10 :=
  intended_correspondence_T10.mp formal_claim_T10_holds

theorem paper_claim_T11_holds : paper_claim_T11 :=
  intended_correspondence_T11.mp formal_claim_T11_holds

/-! ### Non-vacuity witnesses (the zero datum) -/

/-- The datum hypothesis of every paper claim is satisfiable: `u₀ = 0`. -/
theorem paper_FeffermanDatum_zero : paper_FeffermanDatum 0 :=
  ⟨contDiff_zero_fun, fun x => div_zero_field x, feffermanDecay_zero⟩

/-- The rate hypothesis of `paper_claim_T11` is satisfiable at `u₀ = 0`, for every `ν`. -/
theorem paper_RateSmooth_zero (ν : ℝ) : paper_RateSmooth 0 ν :=
  (rateSmooth_iff 0 ν).1 (frohmanianTetherRateSmooth_zero ν)

/-- The ceiling premise of `paper_claim_T10` is satisfiable at `u₀ = 0`. -/
theorem paper_ceiling_zero (ν : ℝ) :
    ∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      paper_FeffermanSolutionOn ν T 0 u p → ∀ t ∈ Set.Ico (0 : ℝ) T,
        BddAbove (Set.range fun x => ‖vorticity (u t) x‖) ∧ (⨆ x, ‖vorticity (u t) x‖) ≤ Y :=
  ceiling_of_rate (frohmanianTetherRateSmooth_zero ν)

/-- The conclusion of `paper_claim_T10` / `paper_claim_T11` is satisfiable at `u₀ = 0`. -/
theorem paper_GlobalSolution_zero (ν : ℝ) :
    paper_GlobalSolution ν 0 (fun _ => 0) (fun _ => fun _ => (0 : ℝ)) :=
  (globalSolution_iff ν 0 _ _).1 (feffermanGlobalSolution_zero ν)

/-- The paper-side conclusion of (T2)–(T9) holds at `ν = 1`, `u₀ = 0` (non-vacuous instance). -/
theorem paper_T2to9_instance_zero :
    ∃ (S : ℕ → Set ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure) (Ck : ℝ),
      0 ≤ Ck ∧
      (∀ t ∈ S 2, paper_H3Energy (u t) < ⊤) ∧
      (∀ s ∈ S 2, ∃ d : ℝ, HasDerivWithinAt (fun t => paper_H3Sq (u t)) d (Set.Ici s) s ∧
        d ≤ Ck * paper_GradSup (u s) * paper_H3Sq (u s)) ∧
      (∀ t ∈ S 2, paper_FluxPackage (u t) (p t)) ∧
      (∀ T : ℝ, Set.Ico (0 : ℝ) T ⊆ S 2 → paper_FeffermanSolutionOn 1 T 0 u p) ∧
      (∀ T : ℝ, Set.Ico (0 : ℝ) T ⊆ S 2 → ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : T3,
        derivWithin (fun s => u s x) (Set.Ici 0) t + convective (u t) (u t) x +
            pressureGradient (p t) x = (1 : ℝ) • laplacian (u t) x + 0) ∧
      (∀ T : ℝ, Set.Ico (0 : ℝ) T ⊆ S 2 → ∀ t ∈ Set.Ico (0 : ℝ) T,
        ∫⁻ x, ‖u t x‖ₑ ^ 2 ≤ ∫⁻ x, ‖(0 : VelocityField) x‖ₑ ^ 2) ∧
      (∀ k : ℕ, 2 ≤ k → ContinuousOn (fun t => paper_H3Sq (u t)) (S k)) ∧
      (∀ k : ℕ, 2 ≤ k → S k = Set.Ici (0 : ℝ) ∨
        ∃ Tstar : ℝ, 0 < Tstar ∧ S k = Set.Ico 0 Tstar ∧
          ∀ B : ℝ, ∃ t, t ∈ Set.Ico (0 : ℝ) Tstar ∧ B < paper_H3Sq (u t)) ∧
      (∀ k : ℕ, 2 ≤ k → S k = Set.Ici (0 : ℝ) ∨
        ∃ Tstar : ℝ, 0 < Tstar ∧ S k = Set.Ico 0 Tstar) :=
  paper_claim_T2to9_holds 1 0 one_pos paper_FeffermanDatum_zero

end TruthGateKato

#print axioms TruthGateKato.intended_correspondence_T1
#print axioms TruthGateKato.intended_correspondence_T2to9
#print axioms TruthGateKato.intended_correspondence_T10
#print axioms TruthGateKato.intended_correspondence_T11
#print axioms TruthGateKato.paper_claim_T1_holds
#print axioms TruthGateKato.paper_claim_T2to9_holds
#print axioms TruthGateKato.paper_claim_T10_holds
#print axioms TruthGateKato.paper_claim_T11_holds
#print axioms TruthGateKato.paper_FeffermanDatum_zero
#print axioms TruthGateKato.paper_RateSmooth_zero
#print axioms TruthGateKato.paper_ceiling_zero
#print axioms TruthGateKato.paper_GlobalSolution_zero
#print axioms TruthGateKato.paper_T2to9_instance_zero
