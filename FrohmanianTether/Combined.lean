/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
module

public import FrohmanianTether.SymplecticTether
public import FrohmanianTether.SymplecticConstraint
public import FrohmanianTether.Uniqueness
public import FrohmanianTether.PlanSteps
public import FrohmanianTether.ClosureBlueprint
public import FrohmanianTether.ClayStatements
public import FrohmanianTether.TetheredLyapunov

/-!
# Combined geometric + analytic layer (one target)

C1–C3 status for `TetherKernel` (checked 2026-11-04):
* C1 `InvariantUnderCoadjointAction` — NOT PROVED. The former route used the hypothesis
  `TetherIntegralPreserved`, which was removed (see `SymplecticTether`, section C1); the
  theorems `tetherKernel_C1_of_casimir`, `tetherKernel_C1_of_volumePreserving` and the
  capstone `combined_conditional_capstone` that depended on it were deleted.
* C2 `DegenerateWRTKineticEnergy` — NOT PROVED. The former route assumed `δH/δω = u`
  (`KineticEnergyDerivIsVelocity`), which is false with these definitions
  (`KineticEnergyDerivative.not_forall_functionalDerivative_kineticEnergy_eq_velocity`);
  that hypothesis and every theorem using it were removed.
* C3 `ProducesControllableNegativeFeedback` — UNCONDITIONAL (`tetherKernel_C3`, equality).
* IF C2 held, symmetry would force `T(M,H) = 0` for every `M` (`tetherKernel_left_H_zero`,
  which takes C2 as a hypothesis): no damping.
-/

@[expose] public section

namespace Combined

open FrohmanianTether ArnoldGeometric NavierStokes3D MeasureTheory ForMathlib

/-- C3, unconditional. -/
theorem tetherKernel_C3' : ProducesControllableNegativeFeedback TetherKernel :=
  tetherKernel_C3

/-- C2 + symmetry ⇒ `T(M,H) = 0` for every functional `M` (any symmetric `B`). -/
theorem left_H_zero_of_C2_symm
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h_sym : ∀ ω F G, B ω F G = B ω G F) (hC2 : DegenerateWRTKineticEnergy B)
    (ω : CoadjointOrbit) (M : Functional) :
    B ω KineticEnergyHamiltonian M = 0 := by
  rw [h_sym]; exact hC2 M ω

/-- For the tether: C2 ⇒ `T(M,H) = T(H,M) = 0`; the tether contributes no damping to `M`. -/
theorem tetherKernel_left_H_zero (hC2 : DegenerateWRTKineticEnergy TetherKernel)
    (ω : CoadjointOrbit) (M : Functional) :
    TetherKernel ω KineticEnergyHamiltonian M = 0 ∧ TetherKernel ω M KineticEnergyHamiltonian = 0 :=
  ⟨left_H_zero_of_C2_symm TetherKernel tetherKernel_comm hC2 ω M, hC2 M ω⟩

end Combined

end

#print axioms Combined.tetherKernel_C3'
#print axioms Combined.left_H_zero_of_C2_symm
#print axioms Combined.tetherKernel_left_H_zero
