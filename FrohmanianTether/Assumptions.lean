/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import Mathlib.Logic.Basic   -- for minimal Prop infrastructure if needed

/-!
# Assumptions

This repository declares **no axioms** (checked by `scripts/check_no_sorry.py` and the strict
`scripts/AxiomAudit.lean`, which allow only `propext`, `Classical.choice` and `Quot.sound`).
It contains no `sorry`, `admit` or `native_decide`.

Every open assumption is an explicit hypothesis (a Lean argument or a named `Prop`), so every
theorem that uses one is a conditional implication. The categorized list of remaining
hypotheses is kept in `CERTIFICATE.md` and in the manuscript (`manuscript/main.tex`,
Section "Remaining assumptions, by category"). Nothing in this repository proves global
regularity of the 3D Navier–Stokes equations.
-/

namespace FrohmanianTether

end FrohmanianTether
