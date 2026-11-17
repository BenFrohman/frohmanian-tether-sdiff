@[expose] public def Mω (u : TimeDependentVelocity) (t : ℝ) : ℝ :=
  vorticity_sup_norm (vorticity (u t))
