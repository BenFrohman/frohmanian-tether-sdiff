/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.NS_Equations

/-!
# Refutation of the removed hypothesis `PointwiseStrainSupBound`

The removed predicate was `PointwiseStrainSupBound u ω C x : ‖Du(x)‖ ≤ C · ‖ω‖_∞`, used with
`ω = curl u`. As a general bound it is false for every constant `C`: the pure strain field
`u(y) = (y₁, y₀, 0)` is linear with `Du = L ≠ 0` and `curl u = 0`, so `‖ω‖_∞ = 0` while
`‖Du‖ > 0` (`not_forall_strain_le_sup_vorticity`). (On decaying fields the Biot–Savart /
Riesz operators are Calderón–Zygmund and bounded on `Lᵖ`, `1 < p < ∞`, but not on `L∞`, so a
pointwise `L∞` bound fails there too; that classical fact is not formalized here.)

The predicate and every theorem that took it (or the same inequality inline) as a hypothesis
were deleted; see `CERTIFICATE.md`.
-/

namespace StrainBoundRefutation

open NavierStokes3D

noncomputable section

/-- The linear pure-strain map `y ↦ (y₁, y₀, 0)`. -/
public def strainLin : T3 →ₗ[ℝ] T3 where
  toFun y := EuclideanSpace.single 0 (y 1) + EuclideanSpace.single 1 (y 0)
  map_add' a b := by
    ext i; fin_cases i <;> simp
  map_smul' c a := by
    ext i; fin_cases i <;> simp

/-- The pure-strain map as a continuous linear map. -/
public def strainCLM : T3 →L[ℝ] T3 := LinearMap.toContinuousLinearMap strainLin

theorem strainCLM_apply (y : T3) :
    strainCLM y = EuclideanSpace.single 0 (y 1) + EuclideanSpace.single 1 (y 0) := rfl

theorem fderiv_coord_strain (x : T3) (i : Fin 3) :
    fderiv ℝ (fun y => (strainCLM : T3 → T3) y i) x =
      (PiLp.proj (p := 2) (fun _ : Fin 3 => ℝ) i).comp strainCLM := by
  have : (fun y => (strainCLM : T3 → T3) y i) =
      ⇑((PiLp.proj (p := 2) (fun _ : Fin 3 => ℝ) i).comp strainCLM) := rfl
  rw [this, ContinuousLinearMap.fderiv]

theorem directionalCoord_strain (comp dir : Fin 3) (x : T3) :
    directionalCoord (strainCLM : T3 → T3) comp dir x =
      strainCLM (EuclideanSpace.single dir 1) comp := by
  unfold directionalCoord
  rw [fderiv_coord_strain]
  rfl

/-- The pure-strain field is irrotational. -/
theorem curl_strain (x : T3) : curl (strainCLM : T3 → T3) x = 0 := by
  unfold curl
  simp only [directionalCoord_strain, strainCLM_apply]
  ext i; fin_cases i <;> simp

theorem vorticity_sup_norm_curl_strain :
    vorticity_sup_norm (curl (strainCLM : T3 → T3)) = 0 := by
  unfold vorticity_sup_norm
  simp [curl_strain]

theorem strainCLM_ne_zero : strainCLM ≠ 0 := by
  intro h
  have h1 := congrArg (fun L : T3 →L[ℝ] T3 => L (EuclideanSpace.single 1 1) 0) h
  simp [strainCLM_apply] at h1

/-- **Refutation.** For every constant `C`, the pointwise strain bound
`‖Du(x)‖ ≤ C · ‖curl u‖_∞` (the removed hypothesis `PointwiseStrainSupBound u (curl u) C x`)
fails for the pure-strain field at every point. -/
public theorem not_forall_strain_le_sup_vorticity (C : ℝ) :
    ¬ ∀ (u : VelocityField) (x : T3),
      ‖fderiv ℝ u x‖ ≤ C * vorticity_sup_norm (curl u) := by
  intro h
  have h0 := h (strainCLM : T3 → T3) 0
  rw [vorticity_sup_norm_curl_strain, mul_zero, ContinuousLinearMap.fderiv] at h0
  exact strainCLM_ne_zero (norm_le_zero_iff.mp h0)

end

end StrainBoundRefutation

#print axioms StrainBoundRefutation.not_forall_strain_le_sup_vorticity
