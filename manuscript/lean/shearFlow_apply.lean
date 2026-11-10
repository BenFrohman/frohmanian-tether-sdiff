-- FrohmanianTether/ExplicitFlows.lean, line 328
public theorem shearFlow_apply (ν k a : ℝ) {t : ℝ} (ht : 0 ≤ t) (y : T3) :
    shearFlow ν k a t y =
      WithLp.toLp 2 ![Real.exp (-(ν * k ^ 2) * t) * a * Real.sin (k * y 2), 0, 0] := ...
