/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
-- NS_Millennium_Proof/Modules/SymplecticTether.lean (sorry-free)
@[expose] public def ConjecturedUnmodifiedTetherPairing
    (u : TimeDependentVelocity) (p : TimeDependentPressure) (ν : ℝ)
    (t : ℝ) (x : T3) (C M : ℝ) : Prop :=
  0 ≤ t →
  NS_PDE u p ν →
  VorticityTransportRegularity u p t x →
  DifferentiableAt ℝ (u t) x →
  PointwiseStrainSupBound (u t) (vorticity (u t)) C x →
  inner ℝ (vorticity (u t) x) (convective (u t) (vorticity (u t)) x) = 0 →
  inner ℝ (vorticity (u t) x) (laplacian (vorticity (u t)) x) ≤ 0 →
  0 ≤ ν →
  (‖vorticity (u t) x‖ = M ∧ M = vorticity_sup_norm (vorticity (u t))) →
  ProducesControllableNegativeFeedback TetherKernel →
  kappa = CalderonZygmundConstant3D →
  inner ℝ (vorticity (u t) x) (convective (vorticity (u t)) (u t) x) ≤
    (C * M - kappa * M ^ 2) * M ^ 2

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
      (C * M - kappa * M ^ 2) * M ^ 2 :=
  (reduced_pairing_iff_cancels_kappa_M4
    (inner ℝ (vorticity (u t) x) (convective (vorticity (u t)) (u t) x))
    C kappa M).mpr hcancels
