structure WordIBP (u : VelocityField) (p : PressureField)
    (k : ℕ) (α : Fin k → Fin 3) : Prop where
  integrable_transport_pair : Integrable
    (fun x => inner ℝ (u x) (gradient (fun y => (1 / 2 : ℝ) * ‖wordDeriv k α u y‖ ^ 2) x))
  integrable_transport_div : Integrable
    (fun x => div u x * ((1 / 2 : ℝ) * ‖wordDeriv k α u x‖ ^ 2))
  flux_transport :
    ∫ x, div (fun y => ((1 / 2 : ℝ) * ‖wordDeriv k α u y‖ ^ 2) • u y) x ∂volume = 0
  integrable_pressure_pair : Integrable
    (fun x => inner ℝ (wordDeriv k α u x) (gradient (wordDerivScalar k α p) x))
  integrable_pressure_div : Integrable
    (fun x => div (wordDeriv k α u) x * wordDerivScalar k α p x)
  flux_pressure :
    ∫ x, div (fun y => wordDerivScalar k α p y • wordDeriv k α u y) x ∂volume = 0
  viscous : ViscousDissipationIBP (wordDeriv k α u)
  integrable_viscous :
    Integrable (fun x => inner ℝ (wordDeriv k α u x) (laplacian (wordDeriv k α u) x))
  integrable_transport :
    Integrable (fun x => inner ℝ (wordDeriv k α u x) (convective u (wordDeriv k α u) x))
  integrable_commutator :
    Integrable (fun x => inner ℝ (wordDeriv k α u x) (convectiveCommutator k α u x))
  integrable_convective :
    Integrable (fun x => inner ℝ (wordDeriv k α u x) (wordDeriv k α (convective u u) x))
  integrable_pressure :
    Integrable (fun x => inner ℝ (wordDeriv k α u x)
      (wordDeriv k α (pressureGradient p) x))
  integrable_laplacian :
    Integrable (fun x => inner ℝ (wordDeriv k α u x) (wordDeriv k α (laplacian u) x))
