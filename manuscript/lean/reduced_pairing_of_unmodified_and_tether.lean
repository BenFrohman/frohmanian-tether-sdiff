-- FrohmanianTether/SymplecticTether.lean, line 642
public theorem reduced_pairing_of_unmodified_and_tether
    (u : TimeDependentVelocity) (p : TimeDependentPressure) (ν : ℝ)
    (t : ℝ) (_ht : 0 ≤ t) (x : T3)
    (_hNS : NS_PDE u p ν)
    (_hreg : VorticityTransportRegularity u p t x)
    (_hu : DifferentiableAt ℝ (u t) x)
    (C M : ℝ)
    (_hCZ : ‖fderiv ℝ (u t) x‖ ≤ C * vorticity_sup_norm (vorticity (u t)))
    (_htransp : inner ℝ (vorticity (u t) x)
      (convective (u t) (vorticity (u t)) x) = 0)
    (_hvisc : inner ℝ (vorticity (u t) x)
      (laplacian (vorticity (u t)) x) ≤ 0)
    (_hν : 0 ≤ ν)
    (_hmax : ‖vorticity (u t) x‖ = M ∧
      M = vorticity_sup_norm (vorticity (u t)))
    (_htether : ProducesControllableNegativeFeedback TetherKernel)
    (_hκ : kappa = CalderonZygmundConstant3D)
    (hcancels : inner ℝ (vorticity (u t) x)
        (convective (vorticity (u t)) (u t) x) +
      kappa * M ^ 4 ≤ C * M ^ 3) :
    inner ℝ (vorticity (u t) x)
        (convective (vorticity (u t)) (u t) x) ≤
      (C * M - kappa * M ^ 2) * M ^ 2 := ...
