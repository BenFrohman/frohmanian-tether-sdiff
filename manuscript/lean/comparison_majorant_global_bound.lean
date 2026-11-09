/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
public theorem comparison_majorant_global_bound (C κ'' y0 : ℝ) (hC : 0 < C) (hκ : 0 < κ'')
    (hy0 : 0 ≤ y0) :
    ∃ Y : ℝ, ∀ t ≥ (0 : ℝ),
      0 ≤ ComparisonODE C κ'' y0 t ∧ ComparisonODE C κ'' y0 t ≤ Y :=
  ⟨max y0 (C / κ''), fun t ht =>
    TetheredLyapunov.uniform_majorant_bound C κ'' y0 hC hκ hy0 t ht⟩
