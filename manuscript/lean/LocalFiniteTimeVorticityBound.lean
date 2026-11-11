-- FrohmanianTether/TetheredLyapunov.lean, line 1474
@[expose] public def LocalFiniteTimeVorticityBound (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∀ T₀ : ℝ, ∃ C : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
    T ≤ T₀ → IsLocalPhysicalSolution ν T u₀ u p →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        BddAbove (Set.range fun x => ‖vorticity (u t) x‖) ∧
          vorticity_sup_norm (vorticity (u t)) ≤ C
