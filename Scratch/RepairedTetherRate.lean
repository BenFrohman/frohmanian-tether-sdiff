import FrohmanianTether.ClayStatements

/-! Scratch (local only, not part of the library).

1. `Clay_A_Fefferman`: Fefferman's official Problem (A), stated literally.
2. `FrohmanianTetherRateSmooth`: a repaired tether rate. It quantifies over local solutions in
   Fefferman's smooth class on `ℝ³ × [0, T)`, so the junk-derivative counterexample
   (`Scratch/TetherRateCounterexample.lean`, whose datum is nowhere differentiable) is excluded.
3. `clay_A_fefferman_of_frohmanianTetherRateSmooth`: rate + named classical continuation
   hypothesis ⟹ `Clay_A_Fefferman`. Both hypotheses are shown satisfiable at `u₀ = 0`.
4. The global-solution form of the rate is vacuous when no global solution exists
   (`frohmanianTetherRateSmoothGlobal_of_no_global_solution`), so it cannot feed Clay (A). -/

open MeasureTheory NavierStokes3D FrohmanianTether
open scoped ContDiff

noncomputable section
namespace RepairedTether

/-- Fefferman (4): `|∂ₓ^α u°(x)| ≤ C_{αK} (1 + |x|)^{-K}` on `ℝ³`, for any `α` and `K`.
`∂ₓ^α` with `|α| = k` is `iteratedFDeriv ℝ k u₀ x` applied to the coordinate unit vectors
`e_{α 0}, …, e_{α (k-1)}` (every multi-index arises from some tuple and conversely). `K` is real. -/
@[expose] public def FeffermanDecay (u₀ : VelocityField) : Prop :=
  ∀ (k : ℕ) (α : Fin k → Fin 3) (K : ℝ), ∃ C : ℝ, ∀ x : T3,
    ‖iteratedFDeriv ℝ k u₀ x (fun j => EuclideanSpace.single (α j) (1 : ℝ))‖ ≤
      C * (1 + ‖x‖) ^ (-K)

/-- Fefferman (1)(f = 0), (2), (3), (6), (7) for `(p, u)` on `ℝ³ × [0, ∞)`.
(6): `p, u ∈ C^∞(ℝ³ × [0, ∞))`, jointly in `(x, t)`.
(1),(2): `ClayStatements.navier_stokes_eq_Ici` with `f ≡ 0`, one-sided `∂ₜ` at `t = 0`.
(3): `u(x, 0) = u°(x)`.
(7): `∫_{ℝ³} |u(x,t)|² dx < C` for all `t ≥ 0`, as a Lebesgue integral of a nonnegative
function (so no "nonintegrable ↦ 0" convention can make it hold). -/
@[expose] public def FeffermanGlobalSolution (ν : ℝ) (u₀ : VelocityField)
    (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  ContDiffOn ℝ ∞ (fun q : T3 × ℝ => u q.2 q.1) (Set.univ ×ˢ Set.Ici (0 : ℝ)) ∧
  ContDiffOn ℝ ∞ (fun q : T3 × ℝ => p q.2 q.1) (Set.univ ×ˢ Set.Ici (0 : ℝ)) ∧
  ClayStatements.navier_stokes_eq_Ici u p ν (fun _ _ => 0) ∧
  (∀ x : T3, u 0 x = u₀ x) ∧
  ∃ C : ℝ, ∀ t ≥ (0 : ℝ), ∫⁻ x, ‖u t x‖ₑ ^ 2 < ENNReal.ofReal C

/-- **Clay (A), Fefferman's official statement.** "Take `ν > 0` and `n = 3`. Let `u°(x)` be any
smooth, divergence-free vector field satisfying (4). Take `f(x, t)` to be identically zero.
Then there exist smooth functions `p(x, t)`, `uᵢ(x, t)` on `ℝ³ × [0, ∞)` that satisfy
(1), (2), (3), (6), (7)." OPEN. -/
@[expose] public def Clay_A_Fefferman : Prop :=
  ∀ (ν : ℝ) (u₀ : VelocityField),
    0 < ν → ContDiff ℝ ∞ u₀ → (∀ x, div u₀ x = 0) → FeffermanDecay u₀ →
      ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
        FeffermanGlobalSolution ν u₀ u p

/-- Local solution in Fefferman's smooth class on `ℝ³ × [0, T)`: `u` and `p` are
jointly `C^∞` on `ℝ³ × [0, T)`; the momentum and divergence equations hold on
`[0, T)` with a one-sided time derivative at `t = 0`; `u(x, 0) = u°(x)`; and the
energy inequality `∫|u(t)|² ≤ ∫|u°|²` holds for every `t ∈ [0, T)`. -/
@[expose] public def IsFeffermanSolutionOn (ν T : ℝ) (u₀ : VelocityField)
    (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  ContDiffOn ℝ ∞ (fun q : T3 × ℝ => u q.2 q.1) (Set.univ ×ˢ Set.Ico (0 : ℝ) T) ∧
  ContDiffOn ℝ ∞ (fun q : T3 × ℝ => p q.2 q.1) (Set.univ ×ˢ Set.Ico (0 : ℝ) T) ∧
  (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : T3,
    derivWithin (fun s => u s x) (Set.Ici 0) t + convective (u t) (u t) x +
        pressureGradient (p t) x = ν • laplacian (u t) x + 0 ∧
      div (u t) x = 0) ∧
  (∀ x : T3, u 0 x = u₀ x) ∧
  (∀ t ∈ Set.Ico (0 : ℝ) T, ∫⁻ x, ‖u t x‖ₑ ^ 2 ≤ ∫⁻ x, ‖u₀ x‖ₑ ^ 2)

/-- `M(t) = ‖ω(t)‖_∞`. -/
@[expose] public def Mω (u : TimeDependentVelocity) (t : ℝ) : ℝ :=
  vorticity_sup_norm (vorticity (u t))

/-- **Repaired Frohmanian tether rate** (OPEN for general data). Along every local solution in
Fefferman's smooth class from `u₀`, `M = ‖ω‖_∞` is finite, continuous, and has a right derivative
with `M' ≤ C M² − κ M³` (`C, κ > 0` depending only on `u₀, ν`). -/
@[expose] public def FrohmanianTetherRateSmooth (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∃ C kap : ℝ, 0 < C ∧ 0 < kap ∧
    ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsFeffermanSolutionOn ν T u₀ u p →
        ContinuousOn (Mω u) (Set.Ico (0 : ℝ) T) ∧
        (∀ s ∈ Set.Ico (0 : ℝ) T, ∃ d : ℝ,
          HasDerivWithinAt (Mω u) d (Set.Ici s) s ∧ d ≤ C * Mω u s ^ 2 - kap * Mω u s ^ 3) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, BddAbove (Set.range fun x => ‖vorticity (u t) x‖))

/-- **Continuation on ℝ³ for datum `u₀`.** If one ceiling `Y` bounds `‖ω‖_∞` along
every local Fefferman-class solution from `u₀`, then `u₀` has a global solution
exactly as Fefferman (A) requires. The BKM logarithmic inequality is proved
(`LogBoundLocal.bkmLogInequality`); the implication is reduced to
`KatoMaximalSolution` by `R3BKM.r3BKMContinuation_of_kato_of_log`. -/
@[expose] public def R3BKMContinuationAt (ν : ℝ) (u₀ : VelocityField) : Prop :=
  (∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsFeffermanSolutionOn ν T u₀ u p → ∀ t ∈ Set.Ico (0 : ℝ) T,
        BddAbove (Set.range fun x => ‖vorticity (u t) x‖) ∧ Mω u t ≤ Y) →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure), FeffermanGlobalSolution ν u₀ u p

@[expose] public def R3BKMContinuation (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField, ContDiff ℝ ∞ u₀ → (∀ x, div u₀ x = 0) → FeffermanDecay u₀ →
    R3BKMContinuationAt ν u₀

/-- Rate ⟹ uniform ceiling `max (M(u₀)) (C/κ)` on every local solution. -/
theorem ceiling_of_rate {ν : ℝ} {u₀ : VelocityField} (h : FrohmanianTetherRateSmooth u₀ ν) :
    ∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsFeffermanSolutionOn ν T u₀ u p → ∀ t ∈ Set.Ico (0 : ℝ) T,
        BddAbove (Set.range fun x => ‖vorticity (u t) x‖) ∧ Mω u t ≤ Y := by
  obtain ⟨C, kap, hC, hκ, hr⟩ := h
  refine ⟨max (vorticity_sup_norm (vorticity u₀)) (C / kap), fun T u p hu t ht => ?_⟩
  obtain ⟨hc, hd, hb⟩ := hr T u p hu
  refine ⟨hb t ht, ?_⟩
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Ico 0 T := fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  have := TetheredLyapunov.comparison_ode_stability_Icc_right C kap hC hκ (Mω u) t
    (hc.mono hsub)
    (fun s hs => hd s ⟨hs.1, lt_trans hs.2 ht.2⟩) t ⟨ht.1, le_rfl⟩
  have hu0 : u 0 = u₀ := funext hu.2.2.2.1
  simpa [Mω, hu0] using this

/-- **Conditional theorem.** The conclusion is exactly Fefferman's Problem (A). -/
public theorem clay_A_fefferman_of_frohmanianTetherRateSmooth
    (hrate : ∀ ν > (0 : ℝ), ∀ u₀ : VelocityField, ContDiff ℝ ∞ u₀ → (∀ x, div u₀ x = 0) →
      FeffermanDecay u₀ → FrohmanianTetherRateSmooth u₀ ν)
    (hBKM : ∀ ν > (0 : ℝ), R3BKMContinuation ν) :
    Clay_A_Fefferman :=
  fun ν u₀ hν hs hd hdec =>
    hBKM ν hν u₀ hs hd hdec (ceiling_of_rate (hrate ν hν u₀ hs hd hdec))

/-! ### Non-vacuity at `u₀ = 0` -/

lemma feffermanDecay_zero : FeffermanDecay 0 := fun k α K =>
  ⟨0, fun x => by
    have : iteratedFDeriv ℝ k (0 : VelocityField) x = 0 := by
      have h := iteratedFDeriv_fun_zero (𝕜 := ℝ) (E := T3) (F := EuclideanSpace ℝ (Fin 3)) (n := k)
      exact congrFun h x
    simp [this]⟩

lemma feffermanGlobalSolution_zero (ν : ℝ) :
    FeffermanGlobalSolution ν 0 (fun _ => 0) (fun _ => fun _ => (0 : ℝ)) := by
  refine ⟨contDiffOn_const, contDiffOn_const, fun t _ x => ⟨?_, ?_⟩, fun _ => rfl, ⟨1, fun t _ => ?_⟩⟩
  · simp [convective, laplacian, pressureGradient]
  · simp [div]
  · simp

/-- Hypothesis `R3BKMContinuationAt` holds at `u₀ = 0` (zero solution). -/
theorem r3BKMContinuationAt_zero (ν : ℝ) : R3BKMContinuationAt ν 0 :=
  fun _ => ⟨_, _, feffermanGlobalSolution_zero ν⟩

/-- Clay (A)'s conclusion is satisfiable at `u₀ = 0` (sanity check on the statement). -/
theorem clay_A_fefferman_instance_zero (ν : ℝ) :
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure), FeffermanGlobalSolution ν 0 u p :=
  ⟨_, _, feffermanGlobalSolution_zero ν⟩

/-- Every local Fefferman-class solution from `0` vanishes on `[0, T)` (energy inequality). -/
lemma eq_zero_of_isFeffermanSolutionOn_zero {ν T : ℝ} {u : TimeDependentVelocity}
    {p : TimeDependentPressure} (hu : IsFeffermanSolutionOn ν T 0 u p) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, u t = 0 := by
  intro t ht
  have hc : Continuous (u t) := by
    have hm : Set.MapsTo (fun x : T3 => (x, t)) Set.univ (Set.univ ×ˢ Set.Ico (0 : ℝ) T) :=
      fun x _ => ⟨Set.mem_univ _, ht⟩
    have := hu.1.continuousOn.comp (Continuous.continuousOn (by fun_prop)) hm
    simpa [continuousOn_univ] using this
  have hE := hu.2.2.2.2 t ht
  simp only [Pi.zero_apply, enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, lintegral_zero, nonpos_iff_eq_zero] at hE
  have hmeas : AEMeasurable (fun x => ‖u t x‖ₑ ^ 2) MeasureTheory.volume :=
    (hc.measurable.enorm.pow_const 2).aemeasurable
  rw [lintegral_eq_zero_iff' hmeas] at hE
  have hae : u t =ᵐ[MeasureTheory.volume] (0 : VelocityField) := by
    filter_upwards [hE] with x hx
    simpa using hx
  exact (Continuous.ae_eq_iff_eq MeasureTheory.volume hc continuous_const).mp hae

/-- Hypothesis `FrohmanianTetherRateSmooth` holds at `u₀ = 0`. -/
theorem frohmanianTetherRateSmooth_zero (ν : ℝ) : FrohmanianTetherRateSmooth 0 ν := by
  refine ⟨1, 1, one_pos, one_pos, fun T u p hu => ?_⟩
  have hz : ∀ τ ∈ Set.Ico (0 : ℝ) T, Mω u τ = 0 := fun τ hτ => by
    simp only [Mω]; rw [eq_zero_of_isFeffermanSolutionOn_zero hu τ hτ, ClayStatements.vorticity_sup_norm_zero_field]
  refine ⟨continuousOn_const.congr hz, fun s hs => ⟨0, ?_, ?_⟩, fun t ht => ?_⟩
  · have hev : Mω u =ᶠ[nhdsWithin s (Set.Ici s)] fun _ => (0 : ℝ) := by
      filter_upwards [Ico_mem_nhdsGE hs.2] with τ hτ
      exact hz τ ⟨hs.1.trans hτ.1, hτ.2⟩
    exact (hasDerivWithinAt_const s _ (0 : ℝ)).congr_of_eventuallyEq hev (hz s hs)
  · rw [hz s hs]; norm_num
  · rw [eq_zero_of_isFeffermanSolutionOn_zero hu t ht]
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    simp [vorticity, curl_zero]

/-! ### The global-solution form cannot feed Clay (A) -/

/-- Global-solution form of the repaired rate (`FrohmanianTetherRate` restricted to
spatially smooth solutions). -/
@[expose] public def FrohmanianTetherRateSmoothGlobal (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∀ u : ℝ → VelocityField, ∀ p : ℝ → PressureField,
    0 < ν → NS_PDE u p ν → u 0 = u₀ → IsPhysicalNSSolution u →
      (∀ t ≥ (0 : ℝ), ContDiff ℝ ∞ (u t)) →
      ∃ C kap : ℝ, 0 < C ∧ 0 < kap ∧
        (∀ s ≥ (0 : ℝ), DifferentiableAt ℝ (Mω u) s) ∧
        (∀ s ≥ (0 : ℝ), deriv (Mω u) s ≤ C * Mω u s ^ 2 - kap * Mω u s ^ 3) ∧
        Continuous (Mω u) ∧
        (∀ τ ≥ (0 : ℝ), BddAbove (Set.range fun x => ‖vorticity (u τ) x‖))

/-- It holds automatically for any datum with no global smooth physical solution (in particular
for any datum that blows up), so it carries no information about existence. -/
theorem frohmanianTetherRateSmoothGlobal_of_no_global_solution {u₀ : VelocityField} {ν : ℝ}
    (h : ¬ ∃ (u : ℝ → VelocityField) (p : ℝ → PressureField), NS_PDE u p ν ∧ u 0 = u₀ ∧
      IsPhysicalNSSolution u ∧ ∀ t ≥ (0 : ℝ), ContDiff ℝ ∞ (u t)) :
    FrohmanianTetherRateSmoothGlobal u₀ ν :=
  fun u p _ hNS hu0 hphys hsm => absurd ⟨u, p, hNS, hu0, hphys, hsm⟩ h

end RepairedTether

#print axioms RepairedTether.clay_A_fefferman_of_frohmanianTetherRateSmooth
#print axioms RepairedTether.frohmanianTetherRateSmooth_zero
#print axioms RepairedTether.r3BKMContinuationAt_zero
#print axioms RepairedTether.feffermanDecay_zero
#print axioms RepairedTether.clay_A_fefferman_instance_zero
#print axioms RepairedTether.frohmanianTetherRateSmoothGlobal_of_no_global_solution
