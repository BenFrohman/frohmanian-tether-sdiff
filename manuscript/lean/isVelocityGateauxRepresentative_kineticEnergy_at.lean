-- FrohmanianTether/ArnoldGeometric.lean, line 1102
public theorem isVelocityGateauxRepresentative_kineticEnergy_at
    (ω ε : CoadjointOrbit)
    (hω : ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x)
    (hε : ∀ i x, DifferentiableAt ℝ (fun y => ε.val y i) x)
    (hkerω : ∀ x, Integrable
      (fun y => biotSavartKernel x y • cross (ω.val y) (x - y)))
    (hkerε : ∀ x, Integrable
      (fun y => biotSavartKernel x y • cross (ε.val y) (x - y)))
    (hF_meas : ∀ᶠ t in nhds (0 : ℝ),
      AEStronglyMeasurable
        (fun x => (1 / 2 : ℝ) *
          ‖BiotSavart ω.val x + t • BiotSavart ε.val x‖ ^ 2)
        NavierStokes3D.volume)
    (hF_int : Integrable
      (fun x => (1 / 2 : ℝ) * ‖BiotSavart ω.val x‖ ^ 2)
      NavierStokes3D.volume)
    (hbound : Integrable
      (fun x => ‖BiotSavart ω.val x‖ * ‖BiotSavart ε.val x‖ +
        ‖BiotSavart ε.val x‖ ^ 2)
      NavierStokes3D.volume)
    (hinner : AEStronglyMeasurable
      (fun x => inner ℝ (BiotSavart ω.val x) (BiotSavart ε.val x))
      NavierStokes3D.volume) :
    HasDerivAt
      (fun t : ℝ =>
        KineticEnergyHamiltonian
          ⟨fun x => ω.val x + t • ε.val x,
            fun x => orbit_add_smul_div_free ω ε t hω hε x⟩)
      (∫ x, pairing (velocity_from_vorticity ω x) (BiotSavart ε.val x)
        ∂volume) 0 := ...
