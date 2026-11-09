-- FrohmanianTether/Uniqueness.lean, line 357
public theorem polarizes_tetherKernel_zero_of_not_differentiable
    (hP : Polarizes TetherKernel)
    {ω : CoadjointOrbit} (hω : ¬ ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x)
    (F G : Functional) : TetherKernel ω F G = 0 := ...
