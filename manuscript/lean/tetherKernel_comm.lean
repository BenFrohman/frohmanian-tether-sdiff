/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/SymplecticTether.lean, line 261

/-!
# manuscript.lean.tetherKernel_comm

Machine-checked Lean 4 module.
-/

public theorem tetherKernel_comm (ω : CoadjointOrbit) (F G : Functional) :
    TetherKernel ω F G = TetherKernel ω G F := ...
