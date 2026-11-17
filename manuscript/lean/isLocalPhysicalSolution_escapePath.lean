/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherDefinitionAudit.lean, line 173

/-!
# manuscript.lean.isLocalPhysicalSolution_escapePath

Machine-checked Lean 4 module.
-/

public theorem isLocalPhysicalSolution_escapePath (ν : ℝ) :
    IsLocalPhysicalSolution ν 0 0 escapePath (fun _ _ => 0) := ...
