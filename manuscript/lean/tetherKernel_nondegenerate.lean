-- FrohmanianTether/TetherNondegeneracy.lean, line 320
public theorem tetherKernel_nondegenerate :
    ∃ (ω φ : CoadjointOrbit) (hφ : IsTestDirection φ), IsRegularVorticity ω ∧
      TetherKernel ω (linFun φ) (linFun φ) ≠ 0 := ...
