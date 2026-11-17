# TRUTH GATE — the GOD gate. Read this first.

Author: Benjamin Stanley Frohman. This file is the root instruction for every person and every
automated agent (every bot) that touches this repository. Load it before any other file.

**Only truth and honest, kernel-proved theorems pass this gate. Nothing from this repository is
published, released, deposited on Zenodo, cited or claimed unless the `truth-gate` check is green
on the exact commit being cited.** That is why it is the GOD gate: it sits above every other
check, and no other green check can stand in for it.

## The issue this gate fixes

A paper states its claim in English. Lean can only prove `formal_claim ↔ paper_claim` once
`paper_claim` is itself written in Lean. If `paper_claim` were simply *defined to be*
`formal_claim` (or an alias of it, or something that unfolds to it), the theorem
`intended_correspondence` would be `Iff.rfl`: it would be empty and prove nothing about the
paper. A green certificate could then "certify" a statement different from the one the paper
makes (drift), whether by accident or by an injected instruction.

## The fix rule (binding, permanent)

1. `paper_claim` is an **independent Lean transcription of the paper's exact claim**, written in
   the paper's own terms, with every hypothesis the paper states. The verbatim English quote,
   the paper path, its sha256 and the section are recorded in the doc comment of
   `Semantics.lean` **and** in this file (below).
2. `paper_claim` must **not** be defined as, reference, or trivially alias `formal_claim`.
3. `intended_correspondence : formal_claim ↔ paper_claim` must have a **substantive proof**. It
   may not be `Iff.rfl`, `rfl`, `exact Iff.rfl` or similar, and it may not use the main theorem
   (it is a statement-level equivalence, not "both sides happen to be provable").
4. `formal_claim` is exactly the statement of the repository's main theorem, and
   `paper_claim_holds` is the main theorem transported across the correspondence.
5. Only `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, `admit`, `native_decide` or
   new `axiom` anywhere outside the draft directories in `TRUTH_GATE.lock`.
6. If the paper's English claim cannot be faithfully transcribed, or is not what Lean proves,
   the gate stays **red** and the mismatch is reported. Never patch over it: never weaken
   `paper_claim`, drop a hypothesis, or redefine it to match the formal side. If the
   formalization drifted, rewrite the formalization so it transports across the lock again.
7. Open problems stay hypotheses. No Millennium Prize problem is claimed solved; the gate only
   ensures the certificate proves precisely the locked claim and nothing else.
8. The locked region of `Semantics.lean`, the quote and `TRUTH_GATE.lock` change only with the
   author's explicit sign-off, as a PR that says "new lock" in its title.
9. Commits are authored by Benjamin Stanley Frohman only, with no AI co-author trailers. No
   force-push and no history rewriting.

## What `scripts/verify-lock.sh` checks mechanically

* `lake build` succeeds, with no `sorry` warning outside the draft directories;
* no `sorry` / `admit` / `native_decide` / `axiom` token outside the draft directories
  (comments and strings excluded);
* `Semantics.lean` has `PAPER_PATH`, `PAPER_SHA256`, `PAPER_SECTION` and a verbatim
  `PAPER_QUOTE`; the hash matches the paper file and the quote occurs in it; this file carries
  the same path, hash and quote;
* the lock region hash matches `TRUTH_GATE.lock`;
* `paper_claim`'s body does not mention `formal_claim`; the correspondence is not proved by
  `Iff.rfl`/`rfl`;
* in Lean: the bodies of `formal_claim` and `paper_claim` differ, the two are not
  definitionally equal, the correspondence proof does not reach the main theorem, the main
  theorem's statement is `formal_claim`, `paper_claim_holds` goes through the correspondence,
  and `#print axioms` shows only the three standard axioms.

What it cannot check: whether the transcription is the right reading of the English. That
reading is fixed once, in writing, below and in `Semantics.lean`, and is the author's sign-off.

## Running the gate locally

```
lake exe cache get
bash scripts/verify-lock.sh
```

Reports are written to `truth-gate-report/`.

## Failure classes (what a red Truth Gate means)

A red Truth Gate is not automatically a math failure. Since 2026-11-17, `scripts/verify-lock.sh`
runs every phase even after one fails. `scripts/truth_gate_classify.py` then sorts each failure
into exactly one class and prints a `TRUTH GATE VERDICT` block at the end of the log. The block
also goes to the job summary and to `truth-gate-report/classification.json`.

This exists because of frohmanian-tether-sdiff PR #13 (run 44039231121). That PR changed only CI,
but its merge ref was built on a main whose lock still had the old `paper_claim` form. The gate
printed `TRUTH GATE FAIL: this lock is NOT certifying` and `TRUTH GATE STATIC FAIL`, which read like
a proof failure, though every kernel check was green.

| Class | Raised by | What the verdict prints | What fixes it |
|---|---|---|---|
| **KERNEL/PROOF** | `lake build` fails; `sorry`/`admit`/`native_decide`/`axiom` outside the draft dirs; nonstandard axioms; a missing or ill-typed locked declaration; `intended_correspondence` fails to check | `KERNEL/PROOF FAILURE (a proof does not check)` and `This is a proof failure`, with the failing lines | Fix the proof. **This is the only class ever described as a proof failure.** |
| **LOCK-FORM** | `paper_claim` reuses a repository Prop or definition; a vacuous alias of `formal_claim`; an `rfl` correspondence; a partial lock; a lock marked `"certifying": false`; an edited lock region; missing `PAPER_*` fields | `LOCK-FORM: lock wording/form problem, not a math failure`, each offending identifier with `file:line` in the Semantics file and the `file:line` of its repository declaration, then the independent transcription that is required | Rewrite the paper side from the paper's own definition, in the paper's symbols, and prove `intended_correspondence` with real reasoning. A new lock needs the author's sign-off. |
| **PAPER-HASH** | the paper's sha256 differs from the lock | `PAPER-HASH: the paper changed after the lock (not a math failure)`, the commit whose bytes match the lock, every changed line, whether only copyright/license/attribution lines changed, and whether the locked quote is still verbatim | If the edit is intended, update `paper_sha256` in `TRUTH_GATE.lock`, the `PAPER_SHA256:` line in the Semantics file and the hash in this file, all in one commit. If the quote changed, that is a statement change and needs sign-off. |
| **STALE-BASE** | a PR's merge ref was built on an older main, and main has since changed the lock, a Semantics file, a paper or a gate script | `STALE-BASE: branch is behind main's lock; update branch (not a math failure)` | The workflow re-merges the PR head onto the current main and judges that merge, which is what would actually land. It goes red only if that merge conflicts, and then it says to update the branch. |

Two more labels can appear in the verdict:

* **`[INHERITED]`** appears when the PR touches no lock, Semantics, paper or gate file but a
  LOCK-FORM or PAPER-HASH failure remains. The failure comes from main, so it has to be fixed on
  main.
* **`UNCLASSIFIED`** appears when a checker crashed or printed a message no rule recognises. It is
  shown verbatim and is never presumed to be a math failure.

The last line always states the classes, for example
`VERDICT: FAIL (LOCK-FORM). Kernel checks passed: no math was found false.`

### Lock-form lint (runs on every PR, no Lean needed)

The `lock-form-lint` job in `.github/workflows/truth-gate.yml` runs
`python3 scripts/truth_gate_classify.py lint --fetch-deps`. It collects every declaration in
`lean_roots` and in the author's own Lake dependencies (every non-Mathlib package in
`lake-manifest.json`), then reads `paper_claim` and any paper-side helper defined in the Semantics
file. It rejects:

1. any Prop that is a whole hypothesis or the conclusion of `formal_claim` (for example the old
   sdiff form `(∀ ν > 0, PeriodicTetherClosingBound ν) → …`). This is never allowed, with or without
   a vocabulary entry;
2. any other repository name that is not listed, with a reason, in `TRUTH_GATE.vocabulary.json`
   (basic notions such as the velocity-field type);
3. any name in `paper_forbidden_names`, and any mention of `formal_claim`.

`TRUTH_GATE.vocabulary.json` is lint configuration. It cannot change the locked claim, because the
lock region hash still pins `paper_claim`. For an existing author-approved lock, it records only the
basic names that the approved claim already uses. Any new name on the paper side goes into the
new-lock PR together with the author's sign-off.

### Tests

`scripts/tests/test_truth_gate_classify.py` has one throw-away fixture repository per class:

* KERNEL/PROOF: build error, sorry, nonstandard axioms;
* LOCK-FORM: named hypothesis Prop, unlisted repository name, alias, non-certifying,
  partial lock, vacuous lock;
* PAPER-HASH: copyright-only change, and a change to the quote;
* STALE-BASE: re-merge onto the current main, and a merge conflict;
* `[INHERITED]` label.

The `lock-form-lint` job runs them on every PR:

```
python3 -m unittest discover -s scripts/tests -p 'test_truth_gate_classify.py' -v
```

## The locked claim of this repository

* Paper: `manuscript/main.tex`
* sha256: `b1e6a8e942383a99f501062261ae75f57f69986059e0a2f1087ea9503f880de9`
* Section: Section 2 "Main results of version 0.1.5", Definition def:ptb ("The Frohmanian tether bound") and Theorem thm:mainA ("Main theorem, kernel-checked")
* Main theorem(s): `FrohmanianTether.ClayStatements.clay_B_exact_of_periodic_tether_bound`
* Lock file: `TRUTH_GATE.lock`; semantics: `FrohmanianTether/Semantics.lean`
* Approver: **Benjamin Stanley Frohman, 2026-11-17 00:22 CT, replying "OK" to "It needs your OK on three new sentences for the paper and a rewrite of the existing Clay B lock"; confirmed 00:32 CT: "yes fix and proceed!"** (recorded in `TRUTH_GATE.lock` → `approvedBy`).

Verbatim quotes (the definition of `M(t)` and the classical solution class; Definition `def:ptb`; Theorem `thm:mainA`):

```
Throughout, $M(t)=\|\omega(t)\|_{L^\infty}$ is \lean{vorticity_sup_norm (vorticity (u t))}, and
\lean{IsPeriodicSmoothSolutionOn ν T u₀ u p} is the class of classical solutions on $[0,T)$: $(u,p)$ jointly
$C^\infty$ on $[0,T)\times\R^3$, the equations with one-sided time derivative and zero forcing,
$\operatorname{div}u=0$, $u(0)=u_0$, and $u(t),p(t)$ $\mathbb{Z}^3$-periodic (exact text in
Appendix~\ref{app:lean:clay}).
```

```
\begin{definition}[The Frohmanian tether bound]\label{def:ptb}
\emph{Lean:} \leanbrk{TetherImpliesBKM.PeriodicTetherBound}.\par\noindent
For $\nu\in\R$ and a field $u_0$, \lean{PeriodicTetherBound ν u₀} asserts that there is $Y\in\R$ such that
$M(t)\le Y$ for every $T$, every classical periodic solution $(u,p)$ from $u_0$ on $[0,T)$ and every
$t\in[0,T)$. The \emph{closing bound} \lean{PeriodicTetherClosingBound ν} asserts \lean{PeriodicTetherBound ν u₀}
for every smooth divergence-free $\mathbb{Z}^3$-periodic $u_0$; this is a definitional identity
(\lean{periodicTetherClosingBound_iff}, proved by \lean{Iff.rfl}).
\end{definition}
```

```
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
```

```lean
def formal_claim : Prop :=
  (∀ ν > (0 : ℝ), PeriodicTetherClosingBound ν) →
    (∀ ν > (0 : ℝ), PeriodicBKMContinuation ν) → Clay_B_exact

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
```

See the doc comment of `FrohmanianTether/Semantics.lean` for the fixed reading of the paper's terms and the scope.

## Re-audit (2026-11-16) and independent transcription

The 2026-11-16 re-audit reopened this lock because `paper_claim` named the repository Props
`PeriodicTetherClosingBound` and `PeriodicBKMContinuation` instead of writing the hypotheses
out from the paper's English (`def:ptb` and the BKM continuation definition in Theorem
`thm:mainA`). Those hypotheses carry the whole difficulty.

`paper_claim` has since been rewritten so that both hypotheses are independent Lean
transcriptions of that English, using only Mathlib primitives and the repository's genuine
Navier–Stokes objects (`IsPeriodicSmoothSolutionOn`, `IsPeriodicSmoothSolution`,
`vorticity_sup_norm`, `vorticity`, `navier_stokes_eq_Ici`, and the smoothness / divergence-free
/ periodicity conditions). Hypothesis (i) is written out as Definition `def:ptb` states it: there is `Y` such that
`M(t) ≤ Y` along every classical periodic solution. The tether kernel does not appear in
that statement. The correspondence `formal_claim ↔ paper_claim` is a genuine argument (reordering
the smoothness and divergence-free hypotheses, joining or splitting the two `ν > 0`
assumptions, and spelling the conclusion out of `IsPeriodicSmoothSolution` / `Clay_B_exact`),
not `Iff.rfl`.

Mechanical status: `TRUTH_GATE.lock` carries the new lock-region hash, `"certifying": true` and
the author's approval in `approvedBy`.

Approver: **Benjamin Stanley Frohman, 2026-11-17 00:22 CT, replying "OK" to "It needs your OK on three new sentences for the paper and a rewrite of the existing Clay B lock"; confirmed 00:32 CT: "yes fix and proceed!".**
Nothing here is a proof of statement (B) or of Navier–Stokes regularity. Hypothesis (i)
remains OPEN and as strong as statement (B) itself; the lock certifies only the implication.

## Additional locks: the Fefferman (A) paper

* Paper: `papers/fefferman-clay-a-conditional/main.tex`
* sha256: `14179f79141f4a2b596f6fc08194be737e2f4bec8235d8f14bfc44175fa939dd`
* Semantics: `Scratch/FeffermanSemantics.lean`; kernel audit: `scripts/TruthGateAuditFefferman.lean`;
  lock entry: `TRUTH_GATE.lock` → `additional_locks`
* Locks (each `formal_claim_X ↔ paper_claim_X`, proved by restructuring, not `Iff.rfl`):
  * `kato`: `KatoMaximal.katoMaximalSolution_of_feffermanDecay` ↔ Theorem `thm:kato-proved`
  * `bkm`: `KatoContinuation.r3BKMContinuation_of_pos` ↔ Theorem `thm:r3bkm`
  * `clayA`: `KatoContinuation.clay_A_fefferman_of_rate` ↔ Theorem `thm:clayA-rate`
* Each `paper_claim_X` is transcribed from the English below with the paper's own symbols
  (`ν`, `u₀`, `u`, `p`, `ω`, `‖ω‖_∞`). It does not name `KatoMaximalSolution`,
  `R3BKMContinuation`, `FrohmanianTetherRateSmooth`, `Clay_A_Fefferman`,
  `FeffermanGlobalSolution`, `IsFeffermanSolutionOn`, `FeffermanDecay`, `Mω`, `sobolevEnergy`,
  `hsSq`, `gradSup` or any `formal_claim`; `scripts/truth_gate_check.py` enforces this.
* Non-vacuity witnesses at `u₀ = 0`: `paper_FeffermanDatum_zero`, `paper_RateSmooth_zero`,
  `paper_ceiling_zero`, `paper_GlobalSolution_zero`, `paper_kato_instance_zero`.
* Approver: **Benjamin Stanley Frohman, 2026-11-17 00:22 CT, replying "OK" to "It needs your OK on three new sentences for the paper and a rewrite of the existing Clay B lock"; confirmed 00:32 CT: "yes fix and proceed!".**

Scope: `thm:kato-proved` is local Kato theory (a maximal solution with an `H³` blow-up
alternative), not global regularity. `thm:r3bkm` keeps a uniform vorticity ceiling as a hypothesis.
`thm:clayA-rate` is conditional on `FrohmanianTetherRateSmooth` for all Fefferman data, which is
OPEN; it does not establish `Clay_A_Fefferman`. No Millennium Prize problem is claimed solved.

Verbatim quotes:

```
Write
\[
M(t)\;:=\;\|\omega(t)\|_\infty
\;:=\;
\sup_{x\in\R^3}\bigl|\omega(x,t)\bigr|,
\]
```

```
Fefferman's official problem description~\cite{Fefferman} poses Problem~(A) as follows. Take $\nu>0$ and $n=3$. Let $u^\circ$ be a smooth divergence-free vector field on $\R^3$ satisfying
\begin{equation}
\tag{4}
\bigl|\partial_x^\alpha u^\circ(x)\bigr|
\le
C_{\alpha K}\,(1+|x|)^{-K}
\quad\text{on }\R^3,\text{ for any }\alpha,K.
\end{equation}
Take $f\equiv 0$. Then there exist smooth functions $p(x,t)$ and $u_i(x,t)$ on $\R^3\times[0,\infty)$ that satisfy (1)~(the momentum equation), (2)~($\operatorname{div}u=0$), (3)~($u(x,0)=u^\circ(x)$), (6)~($p,u\in C^\infty(\R^3\times[0,\infty))$) and (7)~($\int_{\R^3}|u(x,t)|^2\,dx<C$ for all $t\ge 0$).
```

```
The local solution class on which both rates are posed is \lean{IsFeffermanSolutionOn} (\lean{RepairedTetherRate.lean:56--65}): joint $C^\infty$ regularity of $(u,p)$ on $\R^3\times[0,T)$; the incompressible Navier--Stokes equations with $f\equiv 0$ and a one-sided time derivative at $t=0$; the initial condition $u(\cdot,0)=u_0$; and the energy inequality $\int_{\R^3}|u(t)|^2\le\int_{\R^3}|u_0|^2$, written as a comparison of lower Lebesgue integrals.
```

```
Throughout, Sobolev spaces are written $\Hs$, where $s\in\mathbb{N}$ is a nonnegative integer. (The letter $m$ is reserved for miscellaneous integers and is never used as a Sobolev index in the prose.) In the Lean development the same spaces appear as \lean{R3BKM.sobolevEnergy s} (spatial energy)
```

```
\begin{definition}[Smooth tether rate]
\label{def:smooth}
The proposition \lean{FrohmanianTetherRateSmooth} (\lean{Scratch/RepairedTetherRate.lean:74--81}) states: there exist $C,\kappa>0$, depending only on $u_0$ and $\nu$, such that along every local Fefferman-class solution issuing from $u_0$ on $[0,T)$, $M$ is finite and continuous on $[0,T)$, and at every $s\in[0,T)$ there is a right derivative $d$ of $M$ at $s$ satisfying $d\le C M(s)^2-\kappa M(s)^3$.
\end{definition}
```

```
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
```

```
\begin{theorem}[Kato maximal solution for Fefferman data]
\label{thm:kato-proved}
Let $\nu>0$, and let $u_0$ be smooth, divergence-free, and satisfy Fefferman decay~(4). Then \lean{KatoMaximalSolution}\ $\nu$ $u_0$ holds in the sense of Definition~\ref{def:kato}: there exist a time set $S$, fields $(u,p)$ and a constant $C_k\ge 0$ satisfying (i)--(iii) of that definition. This is a maximal Fefferman-class solution with an $H^3$ blow-up alternative; it does not assert global regularity.
\end{theorem}
```

```
\begin{theorem}[Classical BKM continuation on $\R^3$]
\label{thm:r3bkm}
For every $\nu>0$, \lean{R3BKMContinuation}\ $\nu$ holds: for every smooth, divergence-free $u_0$ satisfying~(4), if one ceiling $Y$ bounds $\|\omega\|_\infty$ along every local Fefferman-class solution from $u_0$, that is, $\|\omega(t)\|_\infty$ is finite and $\|\omega(t)\|_\infty\le Y$ for every local Fefferman-class solution $(u,p)$ from $u_0$ on $[0,T)$ and every $t\in[0,T)$, then $u_0$ has a global Fefferman solution: smooth functions $p$ and $u$ on $\R^3\times[0,\infty)$ that satisfy (1), (2), (3), (6) and (7) of Section~\ref{sec:fefferman}. A uniform vorticity ceiling remains a hypothesis; this is not a regularity theorem.
\end{theorem}
```

```
\begin{theorem}[Conditional reduction to the Smooth rate alone]
\label{thm:clayA-rate}
Assume that for every $\nu>0$ and every Fefferman datum $u_0$ (smooth, divergence-free, satisfying~(4)), \lean{FrohmanianTetherRateSmooth}\ $u_0$ $\nu$ holds. Then \lean{Clay_A_Fefferman} holds. The rate hypothesis is not proved in this repository, so this does not establish \lean{Clay_A_Fefferman}.
\end{theorem}
```
