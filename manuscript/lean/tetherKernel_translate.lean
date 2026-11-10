-- FrohmanianTether/TetherEquivariantC1.lean, line 259
public theorem tetherKernel_translate (h : T3) (F G : Functional) (ω : CoadjointOrbit) :
    TetherKernel (translate h • ω) (fun η => F ((translate h)⁻¹ • η))
      (fun η => G ((translate h)⁻¹ • η)) = TetherKernel ω F G := ...
