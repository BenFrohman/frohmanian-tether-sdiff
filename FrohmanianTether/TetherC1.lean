/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.TetherNondegeneracy
public import FrohmanianTether.ConcreteSDiff

/-!
# Coadjoint invariance (C1) of the tether kernel under the concrete action

`InvariantUnderCoadjointAction SDiff B` asks `B (g • ω) F G = B ω F G` for all `g, F, G, ω`,
with the functionals `F, G` **not** transported by `g`. For the concrete group
`ConcreteSDiff.G` (measure-preserving, divergence-preserving bijections acting by
`g • ω = ω ∘ g⁻¹`) this module REFUTES that statement for `TetherKernel`:

* `ConcreteSDiff.translate h` — the translation `x ↦ x + h` is an element of `ConcreteSDiff.G`.
* `not_tetherKernel_invariant_concrete` — `¬ InvariantUnderCoadjointAction ConcreteSDiff.G
  TetherKernel`. With `g` the translation by `3 e₀`, `ω = rotOrbit 0` and `g • ω = rotOrbit (3 e₀)`,
  the functional `F = |linFun φ · - linFun φ (g • ω)|` has no gradient at `g • ω` (so the tether
  vanishes there) while at `ω` it is smooth with gradient `± φ`, where the tether is nonzero.

The equivariant form (`F, G` transported by `g`) is not formalized here.
-/

open MeasureTheory NavierStokes3D ArnoldGeometric ForMathlib FrohmanianTether TetherNondegeneracy
open scoped InnerProductSpace

noncomputable section

namespace ConcreteSDiff

/-- Translations preserve divergence-freeness under composition. -/
public theorem divPres_add_right (h : T3) : DivPres (fun x => x + h) := by
  intro ω x
  have hfd : ∀ i : Fin 3, fderiv ℝ (fun y => (ω.val ∘ fun x => x + h) y i) x =
      fderiv ℝ (fun y => ω.val y i) (x + h) := fun i =>
    fderiv_comp_add_right (f := fun y => ω.val y i) h
  simp only [NavierStokes3D.div, hfd]
  exact ω.property (x + h)

/-- The translation `x ↦ x + h` satisfies the defining predicate of the concrete group. -/
public theorem good_addRight (h : T3) : Good (Equiv.addRight h) := by
  have hinv : ((Equiv.addRight h)⁻¹ : Equiv.Perm T3) = fun x => x + -h := by
    funext x; simp [Equiv.Perm.inv_def]
  refine ⟨measurable_add_const h, ?_, measurePreserving_add_right MeasureTheory.volume h, ?_,
    divPres_add_right h, ?_⟩
  · rw [hinv]; exact measurable_add_const _
  · rw [hinv]; exact measurePreserving_add_right MeasureTheory.volume _
  · rw [hinv]; exact divPres_add_right _

/-- The translation by `h`, as an element of the concrete group. -/
@[expose] public def translate (h : T3) : G := ⟨Equiv.addRight h, good_addRight h⟩

public theorem translate_smul_rotOrbit (h : T3) : translate h • rotOrbit 0 = rotOrbit h := by
  have hext : ∀ a b : CoadjointOrbit, a.val = b.val → a = b := by
    rintro ⟨_, _⟩ ⟨_, _⟩ rfl; rfl
  refine hext _ _ ?_
  funext x
  rw [smul_val]
  have : (((translate h)⁻¹ : G) : Equiv.Perm T3) x = x - h := by
    simp [translate, Equiv.Perm.inv_def, sub_eq_add_neg]
  simp only [Function.comp_apply, this, rotOrbit, rotField, sub_zero]

end ConcreteSDiff

namespace TetherNondegeneracy

/-- Sharper form of `tetherKernel_nondegenerate`: at `rotOrbit 0` the tether is nonzero on the
linear functional of `rotOrbit 0` or on that of `rotOrbit (3 e₀)`. -/
public theorem tetherKernel_rot_nondegenerate :
    TetherKernel (rotOrbit 0) (linFun (rotOrbit 0)) (linFun (rotOrbit 0)) ≠ 0 ∨
      TetherKernel (rotOrbit 0) (linFun (rotOrbit ((3:ℝ) • eb 0)))
        (linFun (rotOrbit ((3:ℝ) • eb 0))) ≠ 0 := by
  set ω := rotOrbit 0
  have hω : IsRegularVorticity ω := (rot_test 0).regular
  obtain ⟨U, ℓ, -, hI⟩ := tetherIntegral_L2 hω
  have hE : 0 < Enstrophy ω := by
    simpa [Enstrophy, Casimir, ω, rotOrbit] using integral_rotField_pos 0
  have hk : kappa ≠ 0 := by rw [kappa_eq_three_halves]; norm_num
  set h0 := rot_test 0
  set h1 := rot_test ((3:ℝ) • eb 0)
  set T0 := testToL2 _ h0
  set T1 := testToL2 _ h1
  have key : ∀ (φ : CoadjointOrbit) (hφ : IsTestDirection φ),
      TetherKernel ω (linFun φ) (linFun φ) = -kappa * Enstrophy ω *
        inner ℝ (testToL2 φ hφ - ℓ (testToL2 φ hφ) • U) (testToL2 φ hφ - ℓ (testToL2 φ hφ) • U) := by
    intro φ hφ
    rw [tetherKernel_eq, functionalDerivative_eq (linFun_gradient hω φ hφ), hI]
  by_contra hall
  push Not at hall
  have z : ∀ (φ : CoadjointOrbit) (hφ : IsTestDirection φ),
      TetherKernel ω (linFun φ) (linFun φ) = 0 → testToL2 φ hφ = ℓ (testToL2 φ hφ) • U := by
    intro φ hφ this
    rw [key φ hφ] at this
    have hc : -kappa * Enstrophy ω ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hk) hE.ne'
    exact sub_eq_zero.mp (inner_self_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc))
  have p0 : 0 < inner ℝ T0 T0 := by
    rw [inner_self_testToL2]; exact integral_rotField_pos 0
  have p1 : 0 < inner ℝ T1 T1 := by
    rw [inner_self_testToL2]; exact integral_rotField_pos _
  have d01 : inner ℝ T0 T1 = 0 := by
    rw [inner_testToL2]; simp [rotOrbit, rotField_disjoint]
  have e0 : T0 = ℓ T0 • U := z _ h0 hall.1
  have e1 : T1 = ℓ T1 • U := z _ h1 hall.2
  clear_value T0 T1
  rw [e0, e1] at d01
  rw [e0] at p0
  rw [e1] at p1
  simp only [real_inner_smul_left, real_inner_smul_right] at p0 p1 d01
  have hU : inner ℝ U U ≠ 0 := by intro h; rw [h] at p0; simp at p0
  have hl0 : ℓ T0 ≠ 0 := by intro h; rw [h] at p0; simp at p0
  have hl1 : ℓ T1 = 0 := by
    rcases mul_eq_zero.mp d01 with h | h
    · exact h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hl0
      · exact absurd h hU
  rw [hl1] at p1; simp at p1

/-- Away from its kink, `absFun φ ω'` has the functional gradient `± φ`. -/
public theorem absFun_gradient_pos {ω ω' φ : CoadjointOrbit} (hω : IsRegularVorticity ω)
    (hφ : IsTestDirection φ) (hd : 0 < linFun φ ω - linFun φ ω') :
    IsFunctionalGradient (absFun φ ω') ω (testToL2 φ hφ) := by
  obtain ⟨hmem, hω', hder⟩ := linFun_gradient hω φ hφ
  refine ⟨hmem, hω, fun ε hε => ?_⟩
  have h := hder ε hε
  have hev : (fun t => absFun φ ω' (orbitLine ω ε hω hε.regular t)) =ᶠ[nhds 0]
      (fun t => linFun φ (orbitLine ω ε hω hε.regular t) - linFun φ ω') := by
    have hc : ContinuousAt (fun t => linFun φ (orbitLine ω ε hω hε.regular t) - linFun φ ω') 0 :=
      (h.continuousAt).sub continuousAt_const
    have hpos : ∀ᶠ t in nhds (0:ℝ),
        0 < linFun φ (orbitLine ω ε hω hε.regular t) - linFun φ ω' := by
      apply hc.eventually (Ioi_mem_nhds _)
      simpa [linFun_orbitLine hω φ hφ ε hε] using hd
    filter_upwards [hpos] with t ht
    simp only [absFun, abs_of_pos ht]
  exact (h.sub_const _).congr_of_eventuallyEq hev

public theorem absFun_gradient_neg {ω ω' φ : CoadjointOrbit} (hω : IsRegularVorticity ω)
    (hφ : IsTestDirection φ) (hd : linFun φ ω - linFun φ ω' < 0) :
    IsFunctionalGradient (absFun φ ω') ω (-testToL2 φ hφ) := by
  obtain ⟨hmem, hω', hder⟩ := linFun_gradient hω φ hφ
  refine ⟨neg_mem hmem, hω, fun ε hε => ?_⟩
  have h := hder ε hε
  have hev : (fun t => absFun φ ω' (orbitLine ω ε hω hε.regular t)) =ᶠ[nhds 0]
      (fun t => -(linFun φ (orbitLine ω ε hω hε.regular t) - linFun φ ω')) := by
    have hc : ContinuousAt (fun t => linFun φ (orbitLine ω ε hω hε.regular t) - linFun φ ω') 0 :=
      (h.continuousAt).sub continuousAt_const
    have hneg : ∀ᶠ t in nhds (0:ℝ),
        linFun φ (orbitLine ω ε hω hε.regular t) - linFun φ ω' < 0 := by
      apply hc.eventually (Iio_mem_nhds _)
      simpa [linFun_orbitLine hω φ hφ ε hε] using hd
    filter_upwards [hneg] with t ht
    simp only [absFun, abs_of_neg ht]
  have h2 := (h.sub_const (linFun φ ω')).neg
  rw [inner_neg_left]
  exact h2.congr_of_eventuallyEq hev

/-- Off its kink, `absFun φ ω'` has the same tether at `ω` as `linFun φ`. -/
public theorem tetherKernel_absFun_eq {ω ω' φ : CoadjointOrbit} (hω : IsRegularVorticity ω)
    (hφ : IsTestDirection φ) (hd : linFun φ ω ≠ linFun φ ω') :
    TetherKernel ω (absFun φ ω') (absFun φ ω') = TetherKernel ω (linFun φ) (linFun φ) := by
  rcases lt_or_gt_of_ne (sub_ne_zero.mpr hd) with hlt | hgt
  · obtain ⟨U, ℓ, hadd, hI⟩ := tetherIntegral_L2 hω
    have hℓneg : ∀ v, ℓ (-v) = -ℓ v := by
      intro v
      have h0 : ℓ 0 = 0 := by have := hadd 0 0; simp at this; linarith
      have := hadd v (-v); rw [add_neg_cancel, h0] at this; linarith
    rw [tetherKernel_eq, tetherKernel_eq, functionalDerivative_eq (absFun_gradient_neg hω hφ hlt),
      functionalDerivative_eq (linFun_gradient hω φ hφ)]
    congr 1
    have e1 := hI (-testToL2 φ hφ) (-testToL2 φ hφ)
    have e2 := hI (testToL2 φ hφ) (testToL2 φ hφ)
    rw [e1, e2, hℓneg]
    have : -testToL2 φ hφ - -ℓ (testToL2 φ hφ) • U = -(testToL2 φ hφ - ℓ (testToL2 φ hφ) • U) := by
      rw [neg_smul, sub_neg_eq_add, neg_sub', sub_neg_eq_add]
    rw [this, inner_neg_neg]
  · rw [tetherKernel_eq, tetherKernel_eq, functionalDerivative_eq (absFun_gradient_pos hω hφ hgt),
      functionalDerivative_eq (linFun_gradient hω φ hφ)]

end TetherNondegeneracy

namespace FrohmanianTether

open TetherNondegeneracy ConcreteSDiff in
/-- **Refutation of C1 for `TetherKernel` under the concrete action.** -/
public theorem not_tetherKernel_invariant_concrete :
    ¬ InvariantUnderCoadjointAction ConcreteSDiff.G TetherKernel := by
  intro hC1
  set h : T3 := (3:ℝ) • eb 0
  set g : ConcreteSDiff.G := translate h
  have hgω : CoadjointAction g (rotOrbit 0) = rotOrbit h := translate_smul_rotOrbit h
  have hω : IsRegularVorticity (rotOrbit 0) := (rot_test 0).regular
  have s00 : linFun (rotOrbit 0) (rotOrbit 0) = ∫ x, ‖rotField 0 x‖ ^ 2 := by
    simp [linFun, rotOrbit]
  have shh : linFun (rotOrbit h) (rotOrbit h) = ∫ x, ‖rotField h x‖ ^ 2 := by
    simp [linFun, rotOrbit]
  have s0h : linFun (rotOrbit 0) (rotOrbit h) = 0 := by
    simp only [linFun, rotOrbit]
    rw [show (fun x => inner ℝ (rotField h x) (rotField 0 x)) = fun _ => (0:ℝ) from
      funext fun x => by rw [real_inner_comm]; exact rotField_disjoint x]
    simp
  have sh0 : linFun (rotOrbit h) (rotOrbit 0) = 0 := by
    simp only [linFun, rotOrbit]
    rw [show (fun x => inner ℝ (rotField 0 x) (rotField h x)) = fun _ => (0:ℝ) from
      funext rotField_disjoint]
    simp
  -- generic step: a test field `φ` separating `ω` from `g • ω` with nonzero tether
  have main : ∀ φ : CoadjointOrbit, IsTestDirection φ → 0 < ∫ x, ‖φ.val x‖ ^ 2 →
      linFun φ (rotOrbit 0) ≠ linFun φ (rotOrbit h) →
      TetherKernel (rotOrbit 0) (linFun φ) (linFun φ) ≠ 0 → False := by
    intro φ hφ hpos hsep hT
    have e := hC1 g (absFun φ (rotOrbit h)) (absFun φ (rotOrbit h)) (rotOrbit 0)
    rw [hgω, tetherKernel_eq_zero_left _
      (FunctionalDerivative_eq_zero_of_not (absFun_no_gradient hφ hpos)),
      tetherKernel_absFun_eq hω hφ hsep] at e
    exact hT e.symm
  rcases tetherKernel_rot_nondegenerate with hT | hT
  · refine main _ (rot_test 0) (integral_rotField_pos 0) ?_ hT
    rw [s00, s0h]; exact (integral_rotField_pos 0).ne'
  · refine main _ (rot_test h) (integral_rotField_pos h) ?_ hT
    rw [sh0, shh]; exact (integral_rotField_pos h).ne

end FrohmanianTether

end
