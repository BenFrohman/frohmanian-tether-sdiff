/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.NS_Equations

/-!
# Navier--Stokes parabolic scaling of vorticity

For `u_λ(x) = λ u(λ x)` (the spatial part of `u_λ(x,t) = λ u(λx, λ²t)`), the vorticity scales as
`ω_λ(x) = λ² ω(λ x)`. Proved from `fderiv` via the chain rule, assuming each velocity component is
differentiable at `λ x`.
-/

@[expose] public section

namespace ScalingIdentities

open NavierStokes3D

/-- The spatially rescaled velocity `x ↦ λ u(λ x)`. -/
noncomputable def rescale (lam : ℝ) (u : VelocityField) : VelocityField :=
  fun y => lam • u (lam • y)

theorem directionalCoord_rescale (lam : ℝ) (u : VelocityField) (comp dir : Fin 3) (x : T3)
    (hd : DifferentiableAt ℝ (fun y => u y comp) (lam • x)) :
    directionalCoord (rescale lam u) comp dir x = lam ^ 2 * directionalCoord u comp dir (lam • x) := by
  unfold directionalCoord rescale
  have h2 : HasFDerivAt (fun y : T3 => lam • y) (lam • ContinuousLinearMap.id ℝ T3) x :=
    (hasFDerivAt_id x).const_smul lam
  have h := (hd.hasFDerivAt.comp x h2).const_mul lam
  have hfun : (fun y : T3 => (lam • u (lam • y)) comp) = fun y => lam * ((fun y => u y comp) ∘ fun y : T3 => lam • y) y := by
    funext y; simp
  rw [hfun, h.fderiv]
  simp [pow_two, mul_assoc]

theorem vorticity_rescale (lam : ℝ) (u : VelocityField) (x : T3)
    (hd : ∀ i, DifferentiableAt ℝ (fun y => u y i) (lam • x)) :
    vorticity (rescale lam u) x = lam ^ 2 • vorticity u (lam • x) := by
  unfold vorticity curl
  simp only [directionalCoord_rescale lam u _ _ x (hd _), ← mul_sub, smul_add]
  ext i
  fin_cases i <;> simp [EuclideanSpace.single_apply]

#print axioms directionalCoord_rescale
#print axioms vorticity_rescale

end ScalingIdentities
