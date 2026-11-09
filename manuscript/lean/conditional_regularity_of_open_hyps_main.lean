/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
-- NS_Millennium_Proof/Modules/ConditionalRegularity.lean
public theorem conditional_regularity_of_open_hyps
    (u0 : TimeDependentVelocity)
    (h_div_free : ∀ t x, div (u0 t) x = 0)
    (h_smooth : IsSmooth (u0 0))
    (h_finite_energy : Integrable (fun x : T3 => ‖u0 0 x‖ ^ 2))
    (ν : ℝ) (h_ν_pos : ν > 0)
    (w : KatoLocalWitness (u0 0) ν)
    (hRiccati : FrohmanianTetherBound (u0 0) ν)
    (hcrit : TetheredLyapunov.PhysicalBKMContinuationCriterionFor (u0 0) ν)
    (huniq : TetheredLyapunov.KatoUniquenessOnExistenceTimes (u0 0) ν w) :
  ∃ (u : TimeDependentVelocity),
    (∀ t ≥ (0 : ℝ), IsSmooth (u t)) ∧
    (u 0 = u0 0) ∧
    (∀ t ≥ (0 : ℝ), satisfies_NavierStokes u ν) ∧
    (∀ t ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u t)) ≥ 0) ∧
    (∀ v : TimeDependentVelocity,
      (∀ t ≥ (0 : ℝ), IsSmooth (v t)) →
      v 0 = u0 0 →
      (∀ t ≥ (0 : ℝ), satisfies_NavierStokes v ν) →
      ∀ t ≥ (0 : ℝ), v t = u t) := by
  obtain ⟨hNS, hu0, hsm, hnn, _hdiv⟩ :=
    TetheredLyapunov.conditional_regularity_of_bkm_uniqueness (u0 0) ν h_ν_pos
      w (TetheredLyapunov.physicalFiniteTimeVorticityBound_of_uniform
          (TetheredLyapunov.physicalUniformVorticityCeiling_of_tetherBound hRiccati))
      hcrit huniq
  refine ⟨w.u, hsm, hu0, ?ns, hnn, ?uniq⟩
  · intro _t _ht
    exact ⟨w.phys, w.p, hNS⟩
  · intro v hsmv hv0 hNSv t ht
    obtain ⟨hphys_v, q, hq⟩ := hNSv 0 le_rfl
    have ht1 : 0 < t + 1 := by linarith
    have hmem : t + 1 ∈ existenceTimes (u0 0) ν :=
      mem_existenceTimes (u0 0) ν ht1 v q hv0 hq (fun s hs => hsmv s hs.1) hphys_v
    exact (huniq (t + 1) v q hmem hv0 hq (fun s hs => hsmv s hs.1) hphys_v
      t ⟨ht, le_of_lt (lt_add_one t)⟩).symm
