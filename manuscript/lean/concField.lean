/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TestFieldFamily.lean, line 117

/-!
# manuscript.lean.concField

Machine-checked Lean 4 module.
-/

@[expose] public def concField (x : T3) {r : ℝ} (hr : 0 < r) : CoadjointOrbit :=
  curlOrbit (concBump x hr) (concBump x hr).contDiff
