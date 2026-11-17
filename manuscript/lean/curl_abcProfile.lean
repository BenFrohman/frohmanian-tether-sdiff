/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 629

/-!
# manuscript.lean.curl_abcProfile

Machine-checked Lean 4 module.
-/

public theorem curl_abcProfile (k A B C : ℝ) (x : T3) :
    curl (abcProfile k A B C) x = k • abcProfile k A B C x := ...
