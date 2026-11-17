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

## The locked claim of this repository

* Paper: `manuscript/main.tex`
* sha256: `b1e6a8e942383a99f501062261ae75f57f69986059e0a2f1087ea9503f880de9`
* Section: Section 2 "Main results of version 0.1.5", Theorem thm:mainA ("Main theorem, kernel-checked")
* Main theorem(s): `FrohmanianTether.ClayStatements.clay_B_exact_of_periodic_tether_bound`
* Lock file: `TRUTH_GATE.lock`; semantics: `FrohmanianTether/Semantics.lean`

Verbatim quote:

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
  (∀ ν : ℝ, 0 < ν → PeriodicTetherClosingBound ν ∧ PeriodicBKMContinuation ν) →
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

## Re-audit (2026-11-16): this lock is NOT certifying

Status: **REOPENED. The gate is red on purpose.** `TRUTH_GATE.lock` carries `"certifying": false`, and
`scripts/truth_gate_check.py` fails while it does. Nothing was deleted: `Semantics.lean`, the quotes,
the hashes and the history are unchanged.

Rule applied (Benjamin Stanley Frohman, 2026-11-16):
* There are no partial locks. A lock certifies only a step on the correct path to the full theorem
  that is kernel-proved as the actual true answer, so that the next step can build on it.
* Drifted, dummy, placeholder or stand-in types, names or categories are rejected.
* Cross-ontology connections are not rejected for looking unrelated. The kernel check, and whether
  the piece genuinely helps reach the full structured proof, decide.
* `paper_claim` is an independent transcription of the verbatim paper quote, never an alias of
  `formal_claim`, and the correspondence is never `rfl`/`Iff.rfl`.

Locked claim under review: clay_B_exact_of_periodic_tether_bound (Theorem thm:mainA)

Why it is reopened:
* The hypotheses are not independently transcribed. `paper_claim` keeps the repository Props `PeriodicTetherClosingBound` and `PeriodicBKMContinuation` as named Props, although the paper gives a precise English definition (def:ptb). The hypotheses carry the whole difficulty, so the lock leans on repository definitions exactly where it matters.
* Stand-in naming. By its definition, the "Frohmanian tether bound" is the plain uniform bound `‖ω(t)‖_∞ ≤ Y` over all classical periodic solutions on all `[0,T)`. Nothing tether-specific enters, and the repository's own docstring says "the Frohmanian assembly contributes no step that BKM does not". The name presents an open vorticity bound as a tether result.
* Non-vacuity is not certified. The bound is open and as strong as Statement (B), and there is no witness. Neither the bound nor its satisfiability is shown.

What would re-certify it: Either re-lock with an independent transcription of both hypotheses from the paper's English, naming the bound honestly as a uniform vorticity bound (as in BenFrohman/Clay-), or retire this lock in favour of the Clay- reduction.
