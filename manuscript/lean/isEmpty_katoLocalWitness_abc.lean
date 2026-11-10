-- FrohmanianTether/ExplicitFlows.lean, line 762
public theorem isEmpty_katoLocalWitness_abc (ν : ℝ) (m : ℤ) {A B C : ℝ}
    (hABC : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) :
    IsEmpty (KatoLocalWitness (abcProfile (2 * Real.pi * m) A B C) ν) := ...
