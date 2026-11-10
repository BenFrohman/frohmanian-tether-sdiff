/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.TetherC1
public import FrohmanianTether.TetherWeightProof

/-!
# Equivariant (transported) C1: the functionals move with the vorticity

`InvariantUnderTransportedCoadjointAction S B` asks
`B (g • ω) (F ∘ (g⁻¹ • ·)) (G ∘ (g⁻¹ • ·)) = B ω F G`: when the vorticity is moved by `g`, the
test functionals are moved along with it (`(g · F)(η) = F (g⁻¹ • η)`).

For the translation subgroup `ConcreteSDiff.transSubgroup` of the concrete group this module
PROVES it for `TetherKernel` (`tetherKernel_transported_invariant`). The ingredients:

* `translate_smul_val`: `(τ_h • ω)(x) = ω(x - h)`.
* `l2Translate h`: translation on `L²` (Mathlib's `Lp.compMeasurePreservingₗᵢ`), a linear
  isometry mapping test fields to test fields (`l2Translate_testToL2`) and hence `DivFreeL2`
  into itself (`l2Translate_mem_divFreeL2`).
* `isFunctionalGradient_translate`: if `g` is the functional gradient of `F` at `ω`, then
  `l2Translate h g` is the gradient of the transported functional at `τ_h • ω`; hence
  `functionalDerivative_translate`.
* `biotSavart_translate`: Biot–Savart commutes with translations
  (`integral_add_right_eq_self`), so `Π_u` is transported (`tI_translate`).
* `ConcreteSDiff.enstrophy_invariant`.

Sanity: the property is not vacuous (`not_transported_invariant_pointEval`: a point-evaluation
kernel fails it), and it differs from the fixed-functional C1, which is refuted for the same
subgroup (`not_tetherKernel_invariant_transSubgroup`).

Not formalized (open): rotations and general volume-preserving diffeomorphisms acting by the
geometric push-forward `(Dφ ω) ∘ φ⁻¹`; the concrete group acts by scalar composition, which is
the right transport only for translations.
-/

open MeasureTheory NavierStokes3D ArnoldGeometric ForMathlib FrohmanianTether TetherNondegeneracy
  TetherWeightProof ConcreteSDiff
open scoped InnerProductSpace

noncomputable section

namespace FrohmanianTether

/-- **Equivariant C1**: the kernel is invariant when the vorticity AND the functionals are
transported by the action, `(g · F)(η) = F (g⁻¹ • η)`. -/
@[expose] public def InvariantUnderTransportedCoadjointAction (SDiff : Type*) [Group SDiff]
    [MulAction SDiff CoadjointOrbit] (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ (g : SDiff) (F G : Functional) (ω : CoadjointOrbit),
    B (CoadjointAction g ω) (fun η => F (g⁻¹ • η)) (fun η => G (g⁻¹ • η)) = B ω F G

end FrohmanianTether

namespace ConcreteSDiff

public theorem orbit_ext {a b : CoadjointOrbit} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

public theorem translate_inv (h : T3) : (translate h)⁻¹ = translate (-h) := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  simp [translate, Equiv.Perm.inv_def]

public theorem translate_smul_val (h : T3) (ω : CoadjointOrbit) :
    (translate h • ω).val = fun y => ω.val (y - h) := by
  rw [smul_val, translate_inv]
  funext y
  simp [translate, sub_eq_add_neg]

public theorem translate_inv_smul_val (h : T3) (ω : CoadjointOrbit) :
    ((translate h)⁻¹ • ω).val = fun y => ω.val (y + h) := by
  rw [translate_inv, translate_smul_val]
  simp

/-- Translations form a subgroup of the concrete group. -/
@[expose] public def transSubgroup : Subgroup G where
  carrier := {g | ∃ h, g = translate h}
  one_mem' := ⟨0, by
    apply Subtype.ext; apply Equiv.ext; intro x; simp [translate]⟩
  mul_mem' := by
    rintro _ _ ⟨h, rfl⟩ ⟨k, rfl⟩
    refine ⟨k + h, ?_⟩
    apply Subtype.ext; apply Equiv.ext; intro x
    simp [translate, add_assoc]
  inv_mem' := by
    rintro _ ⟨h, rfl⟩
    exact ⟨-h, translate_inv h⟩

public theorem translate_mem (h : T3) : translate h ∈ transSubgroup := ⟨h, rfl⟩

/-- Translation preserves test directions. -/
public theorem translate_test {φ : CoadjointOrbit} (hφ : IsTestDirection φ) (h : T3) :
    IsTestDirection (translate h • φ) := by
  rw [IsTestDirection, translate_smul_val]
  exact ⟨hφ.1.comp (contDiff_id.sub contDiff_const), hφ.2.comp_homeomorph (Homeomorph.subRight h)⟩

public theorem translate_regular {ω : CoadjointOrbit} (hω : IsRegularVorticity ω) (h : T3) :
    IsRegularVorticity (translate h • ω) := by
  intro i x
  rw [translate_smul_val]
  exact (hω i (x - h)).comp x (differentiableAt_id.sub_const h)

end ConcreteSDiff

namespace TetherEquivariant

public theorem mp_sub (h : T3) : MeasurePreserving (fun x : T3 => x - h)
    (MeasureTheory.volume : Measure T3) MeasureTheory.volume :=
  measurePreserving_sub_right _ h

/-- Translation by `h` on `L²`: `v ↦ v (· - h)`. -/
@[expose] public def l2Translate (h : T3) : L2Field →ₗᵢ[ℝ] L2Field :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : T3 => x - h) (mp_sub h)

public theorem l2Translate_ae (h : T3) (v : L2Field) :
    ⇑(l2Translate h v) =ᵐ[MeasureTheory.volume] fun x => v (x - h) :=
  Lp.coeFn_compMeasurePreserving v (mp_sub h)

public theorem l2Translate_testToL2 (h : T3) {φ : CoadjointOrbit} (hφ : IsTestDirection φ) :
    l2Translate h (testToL2 φ hφ) = testToL2 (translate h • φ) (translate_test hφ h) := by
  apply Lp.ext
  have h1 := l2Translate_ae h (testToL2 φ hφ)
  have h2 : ⇑(testToL2 (translate h • φ) (translate_test hφ h)) =ᵐ[MeasureTheory.volume]
      (translate h • φ).val := (translate_test hφ h).memLp.coeFn_toLp
  have h3 : (fun x => (testToL2 φ hφ) (x - h)) =ᵐ[MeasureTheory.volume] fun x => φ.val (x - h) :=
    ae_eq_comp (mp_sub h).aemeasurable (by rw [(mp_sub h).map_eq]; exact hφ.memLp.coeFn_toLp)
  filter_upwards [h1, h2, h3] with x e1 e2 e3
  rw [e1, e2, e3, translate_smul_val]

public theorem l2Translate_mem_divFreeL2 (h : T3) {v : L2Field} (hv : v ∈ DivFreeL2) :
    l2Translate h v ∈ DivFreeL2 := by
  have hc : Continuous (l2Translate h) := (l2Translate h).continuous
  have hspan : ∀ w ∈ Submodule.span ℝ testFields,
      l2Translate h w ∈ Submodule.span ℝ testFields := by
    intro w hw
    have : Submodule.span ℝ testFields ≤
        (Submodule.span ℝ testFields).comap (l2Translate h).toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨φ, hφ, rfl⟩
      change l2Translate h (testToL2 φ hφ) ∈ Submodule.span ℝ testFields
      rw [l2Translate_testToL2]
      exact Submodule.subset_span ⟨_, _, rfl⟩
    exact this hw
  unfold DivFreeL2 at hv ⊢
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hv ⊢
  exact map_mem_closure hc hv (fun w hw => hspan w hw)

/-- **Gradient transport.** -/
public theorem isFunctionalGradient_translate (h : T3) {F : CoadjointOrbit → ℝ}
    {ω : CoadjointOrbit} {g : L2Field} (hg : IsFunctionalGradient F ω g) :
    IsFunctionalGradient (fun η => F ((translate h)⁻¹ • η)) (translate h • ω)
      (l2Translate h g) := by
  obtain ⟨hmem, hω, hder⟩ := hg
  refine ⟨l2Translate_mem_divFreeL2 h hmem, translate_regular hω h, fun ε hε => ?_⟩
  set ε' := (translate h)⁻¹ • ε
  have hε' : IsTestDirection ε' := by
    simpa [ε', translate_inv] using translate_test hε (-h)
  have hline : ∀ t, (translate h)⁻¹ • orbitLine (translate h • ω) ε (translate_regular hω h)
      hε.regular t = orbitLine ω ε' hω hε'.regular t := by
    intro t
    apply orbit_ext
    rw [translate_inv_smul_val]
    funext y
    simp [orbitLine, ε', translate_inv_smul_val, translate_smul_val]
  have hinner : inner ℝ g (testToL2 ε' hε') = inner ℝ (l2Translate h g) (testToL2 ε hε) := by
    have e : l2Translate h (testToL2 ε' hε') = testToL2 ε hε := by
      rw [l2Translate_testToL2]
      congr 1
      simp [ε']
    rw [← e, LinearIsometry.inner_map_map]
  have := hder ε' hε'
  rw [hinner] at this
  simpa only [hline] using this

public theorem functionalDerivative_translate (h : T3) (F : CoadjointOrbit → ℝ)
    (ω : CoadjointOrbit) :
    FunctionalDerivative (fun η => F ((translate h)⁻¹ • η)) (translate h • ω)
      =ᵐ[MeasureTheory.volume] fun x => FunctionalDerivative F ω (x - h) := by
  by_cases hex : ∃ g, IsFunctionalGradient F ω g
  · obtain ⟨g, hg⟩ := hex
    rw [functionalDerivative_eq hg, functionalDerivative_eq (isFunctionalGradient_translate h hg)]
    exact l2Translate_ae h g
  · have hnot : ¬ ∃ g, IsFunctionalGradient (fun η => F ((translate h)⁻¹ • η))
        (translate h • ω) g := by
      rintro ⟨g, hg⟩
      apply hex
      have h2 := isFunctionalGradient_translate (-h) hg
      refine ⟨l2Translate (-h) g, ?_⟩
      convert h2 using 1
      · funext η
        rw [translate_inv (-h), neg_neg, inv_smul_smul]
      · rw [← translate_inv, inv_smul_smul]
    rw [FunctionalDerivative_eq_zero_of_not hex, FunctionalDerivative_eq_zero_of_not hnot]
    rfl

public theorem biotSavartKernel_add (x z h : T3) :
    biotSavartKernel x (z + h) = biotSavartKernel (x - h) z := by
  by_cases e : x = z + h
  · subst e; simp
  · have e' : x - h ≠ z := fun h' => e (by rw [← h']; abel)
    rw [biotSavartKernel_of_ne e, biotSavartKernel_of_ne e',
      show x - (z + h) = (x - h) - z by abel]

/-- **Biot–Savart commutes with translations.** -/
public theorem biotSavart_translate (h : T3) (ω : CoadjointOrbit) :
    velocity_from_vorticity (translate h • ω) = fun x => velocity_from_vorticity ω (x - h) := by
  funext x
  simp only [velocity_from_vorticity_eq_BiotSavart, BiotSavart_apply, translate_smul_val,
    show (NavierStokes3D.volume : Measure T3) = MeasureTheory.volume from rfl]
  rw [← integral_add_right_eq_self _ h]
  congr 1
  funext z
  rw [biotSavartKernel_add]
  congr 2
  · simp
  · abel

/-- The projected pairing is transported by translations. -/
public theorem tI_translate (h : T3) (ω : CoadjointOrbit)
    {a b a' b' : T3 → EuclideanSpace ℝ (Fin 3)}
    (ha : a' =ᵐ[MeasureTheory.volume] fun x => a (x - h))
    (hb : b' =ᵐ[MeasureTheory.volume] fun x => b (x - h)) :
    tI (translate h • ω) a' b' = tI ω a b := by
  set u := velocity_from_vorticity ω
  have hu : velocity_from_vorticity (translate h • ω) = fun x => u (x - h) := biotSavart_translate h ω
  have hvol : (NavierStokes3D.volume : Measure T3) = MeasureTheory.volume := rfl
  have hcoef : ∀ {v v' : T3 → EuclideanSpace ℝ (Fin 3)},
      (v' =ᵐ[MeasureTheory.volume] fun x => v (x - h)) →
      projCoef (translate h • ω) v' = projCoef ω v := by
    intro v v' hv
    unfold projCoef
    rw [hu, hvol]
    congr 1
    · rw [show (∫ y, pairing (v' y) (u (y - h))) = ∫ y, pairing (v (y - h)) (u (y - h)) from
        integral_congr_ae (by filter_upwards [hv] with y hy; rw [hy])]
      exact integral_sub_right_eq_self (fun y => pairing (v y) (u y)) h
    · exact integral_sub_right_eq_self (fun y => ‖u y‖ ^ 2) h
  have hpi : ∀ {v v' : T3 → EuclideanSpace ℝ (Fin 3)},
      (v' =ᵐ[MeasureTheory.volume] fun x => v (x - h)) →
      Pi_u (velocity_from_vorticity (translate h • ω)) v'
        =ᵐ[MeasureTheory.volume] fun x => Pi_u u v (x - h) := by
    intro v v' hv
    filter_upwards [hv] with x hx
    rw [pi_u_eq, pi_u_eq, hcoef hv, hx, hu]
  unfold tI
  rw [show (∫ x, inner ℝ (Pi_u (velocity_from_vorticity (translate h • ω)) a' x)
      (Pi_u (velocity_from_vorticity (translate h • ω)) b' x)) =
      ∫ x, inner ℝ (Pi_u u a (x - h)) (Pi_u u b (x - h)) from
    integral_congr_ae (by filter_upwards [hpi ha, hpi hb] with x h1 h2; rw [h1, h2])]
  exact integral_sub_right_eq_self (fun x => inner ℝ (Pi_u u a x) (Pi_u u b x)) h

/-- **Transported C1 for the tether, one translation at a time.** -/
public theorem tetherKernel_translate (h : T3) (F G : Functional) (ω : CoadjointOrbit) :
    TetherKernel (translate h • ω) (fun η => F ((translate h)⁻¹ • η))
      (fun η => G ((translate h)⁻¹ • η)) = TetherKernel ω F G := by
  rw [tetherKernel_eq, tetherKernel_eq, tI_translate h ω (functionalDerivative_translate h F ω)
    (functionalDerivative_translate h G ω), enstrophy_invariant]

end TetherEquivariant

namespace FrohmanianTether

open TetherEquivariant

/-- **Equivariant C1 holds for the tether under the translation subgroup.** -/
public theorem tetherKernel_transported_invariant :
    InvariantUnderTransportedCoadjointAction transSubgroup TetherKernel := by
  rintro ⟨g, ⟨h, rfl⟩⟩ F G ω
  exact tetherKernel_translate h F G ω

/-- Generic form of the C1 refutation: any action with an element moving `rotOrbit 0` to
`rotOrbit (3 e₀)` breaks the fixed-functional C1 for the tether. -/
public theorem not_tetherKernel_invariant_of_shift (S : Type*) [Group S]
    [MulAction S CoadjointOrbit] (g : S)
    (hg : CoadjointAction g (rotOrbit 0) = rotOrbit ((3:ℝ) • eb 0)) :
    ¬ InvariantUnderCoadjointAction S TetherKernel := by
  intro hC1
  set h : T3 := (3:ℝ) • eb 0
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
  have main : ∀ φ : CoadjointOrbit, IsTestDirection φ → 0 < ∫ x, ‖φ.val x‖ ^ 2 →
      linFun φ (rotOrbit 0) ≠ linFun φ (rotOrbit h) →
      TetherKernel (rotOrbit 0) (linFun φ) (linFun φ) ≠ 0 → False := by
    intro φ hφ hpos hsep hT
    have e := hC1 g (absFun φ (rotOrbit h)) (absFun φ (rotOrbit h)) (rotOrbit 0)
    rw [hg, tetherKernel_eq_zero_left _
      (FunctionalDerivative_eq_zero_of_not (absFun_no_gradient hφ hpos)),
      tetherKernel_absFun_eq hω hφ hsep] at e
    exact hT e.symm
  rcases tetherKernel_rot_nondegenerate with hT | hT
  · refine main _ (rot_test 0) (integral_rotField_pos 0) ?_ hT
    rw [s00, s0h]; exact (integral_rotField_pos 0).ne'
  · refine main _ (rot_test h) (integral_rotField_pos h) ?_ hT
    rw [sh0, shh]; exact (integral_rotField_pos h).ne

/-- The fixed-functional C1 fails for the tether already on the translation subgroup, where the
transported C1 holds: the two predicates are different. -/
public theorem not_tetherKernel_invariant_transSubgroup :
    ¬ InvariantUnderCoadjointAction transSubgroup TetherKernel :=
  not_tetherKernel_invariant_of_shift transSubgroup ⟨translate _, translate_mem _⟩
    (translate_smul_rotOrbit _)

/-- A point-evaluation kernel, used to show the transported C1 is not vacuous. -/
@[expose] public def pointEvalKernel (ω : CoadjointOrbit) (_F _G : Functional) : ℝ :=
  ‖ω.val ((1/2 : ℝ) • eb 0)‖

/-- Sanity: the transported C1 is a genuine constraint (it fails for `pointEvalKernel`). -/
public theorem not_transported_invariant_pointEval :
    ¬ InvariantUnderTransportedCoadjointAction transSubgroup pointEvalKernel := by
  intro hI
  have e := hI ⟨translate ((3:ℝ) • eb 0), translate_mem _⟩ (fun _ => 0) (fun _ => 0) (rotOrbit 0)
  have hsm : CoadjointAction (⟨translate ((3:ℝ) • eb 0), translate_mem _⟩ : transSubgroup)
      (rotOrbit 0) = rotOrbit ((3:ℝ) • eb 0) := translate_smul_rotOrbit _
  rw [hsm] at e
  simp only [pointEvalKernel, rotOrbit] at e
  have h1 : rotField ((3:ℝ) • eb 0) ((1/2 : ℝ) • eb 0) = 0 := by
    apply rotField_eq_zero_of_far
    rw [← sub_smul, norm_smul]
    simp [eb]; norm_num
  have h2 : rotField 0 ((1/2 : ℝ) • eb 0) ≠ 0 := by
    simpa using rotField_ne_zero 0
  rw [h1, norm_zero] at e
  exact h2 (norm_eq_zero.1 e.symm)

end FrohmanianTether

end
