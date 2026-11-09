-- FrohmanianTether/ArnoldGeometric.lean, line 947
public noncomputable def KineticEnergyHamiltonian (ω : CoadjointOrbit) : ℝ :=
  (1/2) * ∫ x, ‖BiotSavart ω.val x‖^2 ∂(volume)
