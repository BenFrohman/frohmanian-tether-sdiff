/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
public theorem tethered_jacobi_identity (F G H : Functional) (ω : CoadjointOrbit)
    (X Y Z : VelocityField)
    (_hF : FunctionalDerivative F ω = X)
    (_hG : FunctionalDerivative G ω = Y)
    (_hH : FunctionalDerivative H ω = Z)
    (hident : jacobiator F G H ω =
      ∫ x, cyclicLiePairing X Y Z x ∂volume)
    (hvanish : (∫ x, cyclicLiePairing X Y Z x ∂volume) = 0) :
    jacobiator F G H ω = 0 := ...
