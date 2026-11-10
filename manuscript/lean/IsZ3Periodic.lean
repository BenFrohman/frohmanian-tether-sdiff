-- FrohmanianTether/ClayStatements.lean, line 208
@[expose] public def IsZ3Periodic {α : Type*} (f : T3 → α) : Prop :=
  ∀ (k : Fin 3 → ℤ) (x : T3), f (x + latticeVec k) = f x
