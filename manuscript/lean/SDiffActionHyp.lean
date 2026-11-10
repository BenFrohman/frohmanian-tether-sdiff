-- FrohmanianTether/ArnoldGeometric.lean, line 225
public structure SDiffActionHyp (SDiff : Type*) [Group SDiff] [MulAction SDiff CoadjointOrbit] :
    Prop where
  casimir_invariant : ∀ (f : ℝ → ℝ) (g : SDiff) (ω : CoadjointOrbit),
    (∫ x, f ‖(g • ω).val x‖ ∂volume) = ∫ x, f ‖ω.val x‖ ∂volume
