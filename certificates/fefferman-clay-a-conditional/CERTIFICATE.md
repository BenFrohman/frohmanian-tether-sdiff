# Kernel certificate: "A Kernel-Checked Conditional Reduction of Fefferman's Navier–Stokes Problem (A) to a Lipschitz Tether Rate and a Kato Maximal Solution" (10.5281/zenodo.24152113)

Lean does not issue a signed "official" certificate. This folder records reproducible machine checks of the Lean code the paper cites: the exact commits, toolchain, build logs, `#print axioms` output, a sorry/axiom scan, and a replay of the modules through Lean's kernel with the toolchain's `leanchecker`.

**Scope.** The main theorem `RepairedTether.clay_A_fefferman_of_rateLipschitz_of_kato` (Scratch/TetherRateLipschitz.lean:251) is **conditional**: it derives `Clay_A_Fefferman` from the hypotheses `FrohmanianTetherRateLipschitz` and `KatoMaximalSolution`, and neither hypothesis is proved here. The axiom results below say that each listed theorem is proved from `propext`, `Classical.choice` and `Quot.sound` only. They do not discharge any hypothesis.

Common to both pins: toolchain `leanprover/lean4:v4.30.0-rc1`; Mathlib `0c154d67103f74be3a0f2c509f72ccbf5be9f2a7` (lake-manifest.json), obtained with `lake exe cache get` and never rebuilt from source.

## Pin 1: `b497281f935f256d2a05372d5955296794f1d46d` (branch `feat/r3-bkm-continuation`), Kato and Scratch infrastructure

| Check | Result | Files |
|---|---|---|
| CI run | https://github.com/BenFrohman/frohmanian-tether-sdiff/actions/runs/43158531834 (success; artifact 13917566315) | [b497281-ci-43158531834/](b497281-ci-43158531834/) |
| CI Scratch axiom audit (`lake env lean scripts/PrintScratchAxioms.lean`) | `SCRATCH AUDIT SUMMARY: theorems audited: 102; clean: 102; violations: 0` | [scratch_axioms.txt](b497281-ci-43158531834/scratch_axioms.txt), script [PrintScratchAxioms-b497281.lean.txt](PrintScratchAxioms-b497281.lean.txt) |
| CI repository-wide audit | `AUDIT SUMMARY: theorems audited: 782 ... violations: 0`; `AUDIT PASS` | [axioms.txt](b497281-ci-43158531834/axioms.txt), [print_axioms.txt](b497281-ci-43158531834/print_axioms.txt) |
| Local `lake build FrohmanianTether Scratch` (2026-11-16, clean worktree at b497281) | `Build completed successfully (8343 jobs).` | [build.log](b497281-local/build.log) |
| Local Scratch axiom audit | 102/102 clean; identical to the CI listing | [scratch_axioms.txt](b497281-local/scratch_axioms.txt) |
| sorry / admit / native_decide / axiom scan (`scripts/check_no_sorry.py`) | `OK: no sorry/admit/native_decide, no axiom declarations` | [sorry-scan.txt](b497281-local/sorry-scan.txt) |
| Kernel replay of all 43 Scratch modules (leanchecker, local) | `43 of 43 Scratch modules replayed through the kernel, 0 failures` | [leanchecker.txt](b497281-local/leanchecker.txt), [modules.txt](b497281-local/modules.txt) |

## Pin 2: `feat/tether-rate-derivation`, the main theorem and the Appendix B theorems

The rate theorems were committed at `5d8e6d679666d4cbd785326422695165655ab1ef`. Commit `7745af09d3b41df0931e6996f3d4e6fac0b676a4` (its child) changes no Lean source. It adds `scripts/PrintRateAxioms.lean` (`#print axioms` for all 69 theorems of the paper's Appendix B, including `RepairedTether.ceiling_of_rate`, `TetheredLyapunov.comparison_ode_stability_Icc_right` and `VorticityMaxAttained.isFeffermanSolutionOn_arctanShear`), `scripts/check_rate_axioms.py`, and CI steps that build the Scratch modules, run the audit and replay the modules with leanchecker. Before this, the branch's CI never compiled Scratch.

| Check | Result | Files |
|---|---|---|
| CI run at 7745af0 | https://github.com/BenFrohman/frohmanian-tether-sdiff/actions/runs/43932523196 (success) | [7745af0-ci-43932523196/](7745af0-ci-43932523196/) |
| CI `lake build` of the 17 Scratch modules | `Build completed successfully (8305 jobs).` | [build-rate.log](7745af0-ci-43932523196/build-rate.log) |
| CI `#print axioms`, 69 Appendix B theorems | `RATE AUDIT PASS: 69/69 theorems depend only on propext, Classical.choice, Quot.sound` | [axioms-rate.txt](7745af0-ci-43932523196/axioms-rate.txt), raw [axioms-rate.raw.txt](7745af0-ci-43932523196/axioms-rate.raw.txt), script [PrintRateAxioms.lean.txt](PrintRateAxioms.lean.txt) |
| CI kernel replay (leanchecker) of the 17 Scratch modules + TetheredLyapunov + StrainBoundRefutation | all 19 exit 0 | [leanchecker-rate.txt](7745af0-ci-43932523196/leanchecker-rate.txt) |
| CI repository-wide audit | `AUDIT PASS` | [axioms.txt](7745af0-ci-43932523196/axioms.txt) |
| Local `lake build FrohmanianTether Scratch.FeffermanSchwartz Scratch.FeffermanSobolev Scratch.GradBound Scratch.HeatSobolev Scratch.InverseSobolev Scratch.LerayHeat Scratch.LogBoundLocal Scratch.MildExistence Scratch.NonlinearHm Scratch.ProductHm Scratch.R3BKMContinuation Scratch.SobolevFourier Scratch.TetherRateCounterexample Scratch.TetherRateDerivation Scratch.TetherRateLipschitz Scratch.RepairedTetherRate Scratch.VorticityMaxAttained ` at 5d8e6d6 (2026-11-16) | `Build completed successfully (8327 jobs).` | [build.log](5d8e6d6-local/build.log) |
| Local `#print axioms`, 69 theorems | 69/69 standard axioms only; identical to CI | [axioms.txt](5d8e6d6-local/axioms.txt) |
| Local sorry / axiom scan | `OK: no sorry/admit/native_decide, no axiom declarations` | [sorry-scan.txt](5d8e6d6-local/sorry-scan.txt) |
| Local kernel replay (leanchecker), same 19 modules | all exit 0 | [leanchecker.txt](5d8e6d6-local/leanchecker.txt) |

The five theorems the paper names in its main text:

```
'RepairedTether.clay_A_fefferman_of_rateLipschitz_of_kato' depends on axioms: [propext, Classical.choice, Quot.sound]
'LogBoundLocal.clay_A_fefferman_of_rate_of_kato' depends on axioms: [propext, Classical.choice, Quot.sound]
'RepairedTether.frohmanianTetherRateLipschitz_of_smooth_of_locallyBddRightDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'RepairedTether.comparison_ode_stability_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
'VorticityMaxAttained.not_isFeffermanSolutionOn_implies_vorticityMaximumAttained' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## About leanchecker

`leanchecker` ships with the toolchain. For each module it loads the imports from their `.olean` files and replays every declaration of the module through the kernel. Its own documentation calls it a tool to detect environment hacking, not an independent external verifier. Imported Mathlib and core declarations are trusted from their `.olean` files. The stock binary treats its argument as a module-name prefix and replays every matching module in parallel. On pin 2 every module named is a leaf, so it was run as shipped. On pin 1 it was run from the toolchain's own source `src/lean/LeanChecker.lean` with one change, `target.isPrefixOf m` -> `target == m`, one module per run.

## Rebuild (one command each)

Pin 2 (main theorem, 69 Appendix B theorems):

```
git clone https://github.com/BenFrohman/frohmanian-tether-sdiff.git && cd frohmanian-tether-sdiff && git checkout 7745af09d3b41df0931e6996f3d4e6fac0b676a4 && lake exe cache get && lake build FrohmanianTether Scratch.FeffermanSchwartz Scratch.FeffermanSobolev Scratch.GradBound Scratch.HeatSobolev Scratch.InverseSobolev Scratch.LerayHeat Scratch.LogBoundLocal Scratch.MildExistence Scratch.NonlinearHm Scratch.ProductHm Scratch.R3BKMContinuation Scratch.SobolevFourier Scratch.TetherRateCounterexample Scratch.TetherRateDerivation Scratch.TetherRateLipschitz Scratch.RepairedTetherRate Scratch.VorticityMaxAttained  && lake env lean scripts/PrintRateAxioms.lean > /tmp/rate.txt && python3 scripts/check_rate_axioms.py /tmp/rate.txt | tail -n 1
```

Pin 1 (102 Scratch theorems):

```
git clone https://github.com/BenFrohman/frohmanian-tether-sdiff.git && cd frohmanian-tether-sdiff && git checkout b497281f935f256d2a05372d5955296794f1d46d && lake exe cache get && lake build FrohmanianTether Scratch && lake env lean scripts/PrintScratchAxioms.lean | tail -n 2
```
