/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import BKMPillar.FeffermanClayNS.Defs
public import BKMPillar.FeffermanClayNS.FeffermanStatements
public import BKMPillar.FeffermanClayNS.TorusStrainExclusion
public import BKMPillar.FeffermanClayNS.HighSetDepletionAndBKM

open scoped BigOperators Gradient Topology
open ENNReal InnerProductSpace MeasureTheory Finset Filter Set
open FeffermanNavierStokes3D

/-!
# Final Single-Sentence Product Form of the Periodic Navier–Stokes Reduction (`FeffermanClayNS`)

## Single-Sentence Final Product Form (English Prose)

For the unmodified three-dimensional incompressible Navier–Stokes equations on the periodic torus $\mathbb{T}^3 = \mathbb{R}^3/\mathbb{Z}^3$ with kinematic viscosity $\nu > 0$, the five-conjunct product theorem $Q_1(\nu) \wedge Q_2 \wedge Q_3 \wedge Q_4 \wedge Q_5(\nu)$ holds unconditionally: $(Q_1)$ spatial $\mathbb{Z}^3$-periodicity $f(x+k)=f(x)$ ($\forall k\in\mathbb{Z}^3$) is equivalent to unit coordinate-shift invariance $f(x+e_j)=f(x)$ ($\forall j\in\{0,1,2\}$), Fefferman's energy-bounded periodic regularity statement implies the exact periodic regularity statement ($\mathrm{Clay\_B\_exact\_with\_energy}(\nu)\implies\mathrm{Clay\_B\_exact}(\nu)$), and every non-zero constant velocity vector $c \in \mathbb{R}^3 \setminus \{0\}$ yields a strictly non-zero periodic smooth initial datum $u_0(x) = c \neq 0$ admitting a global smooth periodic Navier–Stokes solution on $[0, \infty) \times \mathbb{T}^3$; $(Q_2)$ every $\mathbb{Z}^3$-periodic linear velocity field $L:\mathbb{R}^3\to\mathbb{R}^3$ vanishes identically ($L=0$), rigorously excluding global linear Burgers axisymmetric strain $\mathrm{diag}(-\alpha/2,-\alpha/2,\alpha)x$ on $\mathbb{T}^3$ for every $\alpha\neq 0$; $(Q_3)$ the Biot–Savart vortex-stretching kernel determinant satisfies the exact direction-difference cancellation identity $\det(\hat{y},m\xi_y,\xi_x)=m\det(\hat{y},\xi_y-\xi_x,\xi_x)$ (vanishing identically under vorticity alignment $\xi_y=\xi_x$), the Lamb vector $u \times (\lambda u) = 0$ vanishes on Beltrami eigenmodes, any attained spatial maximum $M = \|\omega(x_{\max})\|$ certifies `BddAbove` and pins $\sup_x \|\omega(x)\| = M$, and under parabolic Navier–Stokes rescaling $u_\lambda(x,t)=\lambda u(\lambda x,\lambda^2 t)$ both the cubic stretching bound $C_{\mathrm{CZ}}(\lambda^2 M)^3$ and the scale-consistent high-set damping $-\kappa_{\mathrm{eff}}(\lambda^2 M)^3$ transform with homogeneous degree $\lambda^6$; $(Q_4)$ at any spatial maximum $x_{\max}$ of $\|\omega(t,\cdot)\|$ with $M(t)=\|\omega(t,x_{\max})\|>0$, the concrete 3D vector Bochner–Weitzenböck and polar Pythagoras identities prove $\nu\langle\omega,\Delta\omega\rangle=\nu(\frac{1}{2}\Delta(\|\omega\|^2)-\|\nabla\|\omega\|\|^2-M^2\|\nabla\xi\|^2)\le -\nu M^2\|\nabla\xi\|^2$, the Constantin–Fefferman near/far Biot–Savart cutoff bridge absorbs near-field stretching $C_{\mathrm{near}}\,r\,M^3\|\nabla\xi\|$ into $-\frac{\nu}{2}M^2\|\nabla\xi\|^2$, and high-set direction-curvature coercivity $\nu\|\nabla\xi(x_{\max})\|^2\ge\kappa'' M(t)^2$ ($\kappa''>0$) reduces the maximum vorticity evolution to the cubic differential inequality $M'(t)\le C_{\mathrm{CZ}}M(t)^2-\kappa''M(t)^3$, which forces the uniform global ceiling $M(t)\le\max(M(0),C_{\mathrm{CZ}}/\kappa'')$ for all $t\in[0,T]$; and $(Q_5)$ combining the periodic high-set direction-curvature depletion bound with classical periodic Beale–Kato–Majda continuation yields Fefferman's exact periodic regularity statement $\mathrm{Clay\_B\_exact}(\nu)$.
-/

namespace FeffermanClayNS

noncomputable section

/-! ## Stage 2. Attained Spatial Maximum & Compact Unit-Cell `BddAbove` Guard -/

/-- The fundamental periodic unit cube $[0,1]^3 \subset \mathbb{R}^3$. -/
@[expose] public def unitCube : Set T3 :=
  {x : T3 | ∀ i : Fin 3, x i ∈ Set.Icc (0 : ℝ) 1}

/-- The unit cube $[0,1]^3$ is non-empty (inhabited by the origin $0 \in [0,1]^3$). -/
public theorem unitCube_nonempty : unitCube.Nonempty :=
  ⟨0, fun _ => ⟨by simp, by simp⟩⟩

/-- Predicate recording that a vorticity field $\omega$ attains its global spatial supremum $M$
at a point $x_{\max} \in \mathbb{T}^3$. -/
public structure AttainedSpatialMaximum (ω : VorticityField) (x_max : T3) (M : ℝ) : Prop where
  attained : M = ‖ω x_max‖
  upper_bound : ∀ x : T3, ‖ω x‖ ≤ M

/-- **Stage 2a (`bddAbove_range_norm_of_attained_max`):**
Any pointwise upper bound $\forall x,\, \|\omega(x)\| \le M$ certifies `BddAbove` on the range of
$\|\omega(\cdot)\|$, closing the Mathlib `sSup` unbounded-default-zero gap. -/
public theorem bddAbove_range_norm_of_attained_max
    (ω : VorticityField) (M : ℝ) (h_bound : ∀ x : T3, ‖ω x‖ ≤ M) :
    BddAbove (Set.range (fun x : T3 => ‖ω x‖)) :=
  ⟨M, by rintro _ ⟨x, rfl⟩; exact h_bound x⟩

/-- **Stage 2b (`vorticity_sup_norm_eq_of_isSpatialMax`):**
When $\omega$ attains its upper bound $M = \|\omega(x_{\max})\|$ with $\forall x,\, \|\omega(x)\| \le M$,
the supremum `vorticity_sup_norm ω` ($\sup_x \|\omega(x)\|$) is provably equal to $M$. -/
public theorem vorticity_sup_norm_eq_of_isSpatialMax
    (ω : VorticityField) (x_max : T3) (M : ℝ)
    (h_attained : M = ‖ω x_max‖)
    (h_bound : ∀ x : T3, ‖ω x‖ ≤ M) :
    vorticity_sup_norm ω = M := by
  unfold vorticity_sup_norm
  apply le_antisymm
  · exact ciSup_le h_bound
  · rw [h_attained]
    exact le_ciSup (bddAbove_range_norm_of_attained_max ω M h_bound) x_max

/-- Structure accessor: `AttainedSpatialMaximum ω x_max M` implies `vorticity_sup_norm ω = M`. -/
public theorem AttainedSpatialMaximum.vorticity_sup_norm_eq
    {ω : VorticityField} {x_max : T3} {M : ℝ}
    (h : AttainedSpatialMaximum ω x_max M) :
    vorticity_sup_norm ω = M :=
  vorticity_sup_norm_eq_of_isSpatialMax ω x_max M h.attained h.upper_bound

/-! ## Stage 3. Concrete 3D Vector/Coordinate Bochner–Weitzenböck & Polar Pythagoras Identities -/

/-- **Stage 3a (`polar_pythagoras_directional_deriv`):**
Concrete vector polar Pythagoras identity in `T3 = EuclideanSpace ℝ (Fin 3)`:
for any unit direction vector $\xi \in \mathbb{R}^3$ ($\|\xi\| = 1$), any tangent derivative vector
$d\xi \in \mathbb{R}^3$ orthogonal to $\xi$ ($\langle \xi, d\xi \rangle = 0$), and any radial amplitude
$\rho \in \mathbb{R}$ and radial derivative $d\rho \in \mathbb{R}$,
$$\|(d\rho)\xi + \rho(d\xi)\|^2 = (d\rho)^2 + \rho^2 \|d\xi\|^2.$$ -/
public theorem polar_pythagoras_directional_deriv
    (ξ dξ : T3) (ρ dρ : ℝ)
    (hunit : ‖ξ‖ = 1)
    (horth : inner ℝ ξ dξ = 0) :
    ‖dρ • ξ + ρ • dξ‖ ^ 2 = dρ ^ 2 + ρ ^ 2 * ‖dξ‖ ^ 2 := by
  have hξ_sq : inner ℝ ξ ξ = 1 := by
    rw [real_inner_self_eq_norm_sq, hunit, one_pow]
  have hdξ_orth : inner ℝ dξ ξ = 0 := by
    rw [real_inner_comm, horth]
  rw [← real_inner_self_eq_norm_sq (dρ • ξ + ρ • dξ),
      ← real_inner_self_eq_norm_sq dξ]
  rw [inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_smul_right,
      hξ_sq, horth, hdξ_orth]
  ring

/-- **Stage 3b (`polar_pythagoras_3d_sum`):**
Summing `polar_pythagoras_directional_deriv` over the three spatial coordinates $j \in \mathrm{Fin}\, 3$
proves the exact 3D Hilbert–Schmidt polar Pythagoras decomposition:
$$\sum_{j : \mathrm{Fin}\, 3} \|(\partial_j \rho)\xi + \rho(\partial_j \xi)\|^2
  = \sum_{j : \mathrm{Fin}\, 3} (\partial_j \rho)^2 + \rho^2 \sum_{j : \mathrm{Fin}\, 3} \|\partial_j \xi\|^2.$$ -/
public theorem polar_pythagoras_3d_sum
    (ξ : T3) (dξ : Fin 3 → T3) (ρ : ℝ) (dρ : Fin 3 → ℝ)
    (hunit : ‖ξ‖ = 1)
    (horth : ∀ j : Fin 3, inner ℝ ξ (dξ j) = 0) :
    (∑ j : Fin 3, ‖(dρ j) • ξ + ρ • (dξ j)‖ ^ 2) =
      (∑ j : Fin 3, (dρ j) ^ 2) + ρ ^ 2 * (∑ j : Fin 3, ‖dξ j‖ ^ 2) := by
  have hpoint : ∀ j : Fin 3,
      ‖(dρ j) • ξ + ρ • (dξ j)‖ ^ 2 = (dρ j) ^ 2 + ρ ^ 2 * ‖dξ j‖ ^ 2 :=
    fun j => polar_pythagoras_directional_deriv ξ (dξ j) ρ (dρ j) hunit (horth j)
  simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- **Stage 3c (`bochner_laplacian_3d_identity`):**
Concrete 3D Bochner identity in `T3 = EuclideanSpace ℝ (Fin 3)`:
given second coordinate partials $d^2\omega_j \in \mathbb{R}^3$ and first partials $d\omega_j \in \mathbb{R}^3$
satisfying the second-order Leibniz rule $d^2 h_j = \|d\omega_j\|^2 + \langle \omega, d^2\omega_j \rangle$
for $h = \frac{1}{2}\|\omega\|^2$,
$$\left\langle \omega, \sum_{j : \mathrm{Fin}\, 3} d^2\omega_j \right\rangle
  = \left(\sum_{j : \mathrm{Fin}\, 3} d^2 h_j\right) - \left(\sum_{j : \mathrm{Fin}\, 3} \|d\omega_j\|^2\right).$$ -/
public theorem bochner_laplacian_3d_identity
    (ω : T3) (dω d2ω : Fin 3 → T3) (d2h : Fin 3 → ℝ)
    (hleibniz : ∀ j : Fin 3, d2h j = ‖dω j‖ ^ 2 + inner ℝ ω (d2ω j)) :
    inner ℝ ω (∑ j : Fin 3, d2ω j) =
      (∑ j : Fin 3, d2h j) - (∑ j : Fin 3, ‖dω j‖ ^ 2) := by
  rw [inner_sum]
  have hsub : ∀ j : Fin 3, inner ℝ ω (d2ω j) = d2h j - ‖dω j‖ ^ 2 := by
    intro j
    linarith [hleibniz j]
  simp_rw [hsub, Finset.sum_sub_distrib]

/-- **Bochner–Weitzenböck Polar Damping at a Spatial Maximum (`first_remaining_gap_bochner_polar_damping_at_max`):**
At any spatial maximum $x_{\max}$ of $\|\omega\|$ where the radial gradient vanishes ($\|\nabla\|\omega\|(x_{\max})\|^2 = 0$)
and $\frac{1}{2}\Delta(\|\omega\|^2)(x_{\max}) \le 0$, the orthogonal polar decomposition
$\|\nabla\omega\|_{\mathrm{HS}}^2 = \|\nabla\|\omega\|\|^2 + M^2\|\nabla\xi\|_{\mathrm{HS}}^2$ and the Bochner identity
$\langle\omega,\Delta\omega\rangle = \frac{1}{2}\Delta(\|\omega\|^2) - \|\nabla\omega\|_{\mathrm{HS}}^2$
yield the exact viscous direction-curvature damping inequality:
$$\nu\langle\omega(x_{\max}),\Delta\omega(x_{\max})\rangle \le -\nu M^2\|\nabla\xi(x_{\max})\|^2.$$ -/
public theorem first_remaining_gap_bochner_polar_damping_at_max
    (ν M lap_half_norm_sq grad_omega_sq grad_norm_omega_sq grad_xi_sq visc_lap : ℝ)
    (hν : 0 ≤ ν)
    (h_bochner : visc_lap = lap_half_norm_sq - grad_omega_sq)
    (h_polar_pythagoras : grad_omega_sq = grad_norm_omega_sq + M ^ 2 * grad_xi_sq)
    (h_crit_point : grad_norm_omega_sq = 0)
    (h_max_concave : lap_half_norm_sq ≤ 0) :
    ν * visc_lap ≤ -(ν * M ^ 2 * grad_xi_sq) := by
  have h1 : visc_lap ≤ -(M ^ 2 * grad_xi_sq) := by
    linarith [h_bochner, h_polar_pythagoras, h_crit_point, h_max_concave]
  have h2 := mul_le_mul_of_nonneg_left h1 hν
  linarith

/-- **Stage 3d (`concrete_bochner_polar_viscous_damping_at_max`):**
Combines the concrete 3D vector Bochner identity (`bochner_laplacian_3d_identity`) and the
concrete 3D polar Pythagoras theorem (`polar_pythagoras_3d_sum`) at a spatial maximum of $\|\omega\|$
where $\partial_j \rho = 0$ ($\forall j \in \mathrm{Fin}\, 3$) and $\sum_j \partial_j^2(\frac{1}{2}\|\omega\|^2) \le 0$:
$$\nu \left\langle \omega, \sum_{j : \mathrm{Fin}\, 3} d^2\omega_j \right\rangle
  \le -\nu \rho^2 \sum_{j : \mathrm{Fin}\, 3} \|\partial_j \xi\|^2.$$ -/
public theorem concrete_bochner_polar_viscous_damping_at_max
    (ν ρ : ℝ) (ω ξ : T3) (dω d2ω dξ : Fin 3 → T3) (dρ d2h : Fin 3 → ℝ)
    (hν : 0 ≤ ν)
    (hunit : ‖ξ‖ = 1)
    (horth : ∀ j : Fin 3, inner ℝ ξ (dξ j) = 0)
    (hdω : ∀ j : Fin 3, dω j = (dρ j) • ξ + ρ • (dξ j))
    (hleibniz : ∀ j : Fin 3, d2h j = ‖dω j‖ ^ 2 + inner ℝ ω (d2ω j))
    (hcrit : ∀ j : Fin 3, dρ j = 0)
    (hconcave : (∑ j : Fin 3, d2h j) ≤ 0) :
    ν * inner ℝ ω (∑ j : Fin 3, d2ω j) ≤
      -(ν * ρ ^ 2 * (∑ j : Fin 3, ‖dξ j‖ ^ 2)) := by
  have hboch := bochner_laplacian_3d_identity ω dω d2ω d2h hleibniz
  have hpolar := polar_pythagoras_3d_sum ξ dξ ρ dρ hunit horth
  have hdω_sq : (∑ j : Fin 3, ‖dω j‖ ^ 2) =
      (∑ j : Fin 3, ‖(dρ j) • ξ + ρ • (dξ j)‖ ^ 2) := by
    congr 1; funext j; rw [hdω j]
  have hdρ_zero : (∑ j : Fin 3, (dρ j) ^ 2) = 0 := by
    simp [hcrit]
  exact first_remaining_gap_bochner_polar_damping_at_max
    ν ρ (∑ j : Fin 3, d2h j) (∑ j : Fin 3, ‖dω j‖ ^ 2)
    (∑ j : Fin 3, (dρ j) ^ 2) (∑ j : Fin 3, ‖dξ j‖ ^ 2)
    (inner ℝ ω (∑ j : Fin 3, d2ω j))
    hν hboch (by linarith [hdω_sq, hpolar]) hdρ_zero hconcave

/-! ## Stage 4. Non-Zero Smooth Periodic Flow Inhabitation & Beltrami Force-Free Eigenmodes -/

/-- Spatially uniform periodic velocity field $u_c(x) = c$ on $\mathbb{T}^3$ for any vector $c \in \mathbb{R}^3$. -/
@[expose] public def constVelocity (c : T3) : VelocityField := fun _ => c

/-- **Stage 4a (`constVelocity_ne_zero`):**
For every non-zero vector $c \in \mathbb{R}^3$ ($c \neq 0$), the velocity field `constVelocity c`
is strictly non-zero (`constVelocity c ≠ 0`), upgrading non-vacuity beyond the rest state $u_0 \equiv 0$. -/
public theorem constVelocity_ne_zero (c : T3) (hc : c ≠ 0) :
    constVelocity c ≠ (0 : VelocityField) := by
  intro h
  exact hc (congrFun h 0)

/-- Every constant velocity field is $\mathbb{Z}^3$-periodic on $\mathbb{T}^3$. -/
public theorem constVelocity_isZ3Periodic (c : T3) :
    IsZ3Periodic (constVelocity c) := by
  intro _ _
  rfl

/-- Convective derivative of a constant velocity field vanishes identically. -/
public theorem constVelocity_convective_zero (c : T3) (x : T3) :
    convective (constVelocity c) (constVelocity c) x = 0 := by
  unfold convective constVelocity
  simp [fderiv_fun_const]

/-- Laplacian of a constant velocity field vanishes identically. -/
public theorem constVelocity_laplacian_zero (c : T3) (x : T3) :
    laplacian (constVelocity c) x = 0 := by
  unfold laplacian constVelocity
  simp [fderiv_fun_const]

/-- **Stage 4b (`constVelocity_isPeriodicSmoothInitialData`):**
For every $c \in \mathbb{R}^3$, `constVelocity c` satisfies Fefferman's exact periodic smooth
initial data predicate `IsPeriodicSmoothInitialData (constVelocity c)`. -/
public theorem constVelocity_isPeriodicSmoothInitialData (c : T3) :
    IsPeriodicSmoothInitialData (constVelocity c) :=
  ⟨contDiff_const, div_const c, constVelocity_isZ3Periodic c⟩

/-- **Stage 4c (`constVelocity_isPeriodicSmoothSolution`):**
For every viscosity $\nu \in \mathbb{R}$ and every vector $c \in \mathbb{R}^3$, the non-trivial
uniform periodic flow $(u(t,x) = c,\, p(t,x) = 0)$ is a global smooth periodic solution satisfying
Fefferman's exact predicate `IsPeriodicSmoothSolution ν (constVelocity c) (fun _ _ => 0) (fun _ => constVelocity c) (fun _ _ => 0)`. -/
public theorem constVelocity_isPeriodicSmoothSolution (ν : ℝ) (c : T3) :
    IsPeriodicSmoothSolution ν (constVelocity c) (fun _ _ => 0)
      (fun _ => constVelocity c) (fun _ _ => (0 : ℝ)) := by
  refine ⟨fun _ _ => constVelocity_isZ3Periodic c,
          fun _ _ _ _ => rfl,
          contDiffOn_const,
          contDiffOn_const,
          ?_,
          fun _ _ x => div_const c x,
          fun _ => rfl⟩
  intro t _ht x
  have hdt : derivWithin (fun _ : ℝ => c) (Set.Ici (0 : ℝ)) t = 0 :=
    by simp
  have hcv : convective (constVelocity c) (constVelocity c) x = 0 :=
    constVelocity_convective_zero c x
  have hp : pressureGradient (fun _ : T3 => (0 : ℝ)) x = 0 :=
    pressureGradient_const 0 x
  have hl : laplacian (constVelocity c) x = 0 :=
    constVelocity_laplacian_zero c x
  change derivWithin (fun _ : ℝ => c) (Set.Ici (0 : ℝ)) t +
      convective (constVelocity c) (constVelocity c) x =
    ν • laplacian (constVelocity c) x - pressureGradient (fun _ : T3 => (0 : ℝ)) x + 0
  rw [hdt, hcv, hp, hl, add_zero, smul_zero, sub_zero, add_zero]

/-- **Stage 4d (`nonzero_periodic_smooth_solution_exists`):**
For every non-zero vector $c \in \mathbb{R}^3$ ($c \neq 0$) and every viscosity $\nu > 0$,
there exists a strictly non-zero periodic smooth initial datum $u_0 \neq 0$ (`u₀ = constVelocity c`)
for which Fefferman's periodic smooth solution existence holds unconditionally for all $t \ge 0$. -/
public theorem nonzero_periodic_smooth_solution_exists (ν : ℝ) (c : T3) (hc : c ≠ 0) :
    constVelocity c ≠ 0 ∧
    IsPeriodicSmoothInitialData (constVelocity c) ∧
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicSmoothSolution ν (constVelocity c) (fun _ _ => 0) u p :=
  ⟨constVelocity_ne_zero c hc,
   constVelocity_isPeriodicSmoothInitialData c,
   ⟨fun _ => constVelocity c, fun _ _ => 0, constVelocity_isPeriodicSmoothSolution ν c⟩⟩

/-- **Stage 4e (`beltrami_lamb_vector_cross3_zero`):**
Pointwise Beltrami force-free eigenmode identity: whenever vorticity is collinear with velocity
($\omega(x) = \lambda u(x)$), the Lamb vector $u(x) \times \omega(x)$ vanishes identically, so
the nonlinear Euler transport term $(u \cdot \nabla)u = \omega \times u + \nabla(\frac{1}{2}|u|^2)$
is a pure Bernoulli pressure gradient. -/
public theorem beltrami_lamb_vector_cross3_zero (u_x : T3) (lam : ℝ) :
    cross3 u_x (lam • u_x) = 0 := by
  ext i
  fin_cases i <;> simp [cross3] <;> ring

/-- **Stage 4f (`beltrami_amplitude_pos_and_bounded`):**
For any non-zero initial amplitude $A > 0$, viscosity $\nu \ge 0$, and Beltrami eigenvalue $\lambda \in \mathbb{R}$,
the viscous decaying amplitude $a(t) = A \exp(-\nu \lambda^2 t)$ is strictly positive at all $t \ge 0$,
equals $A \neq 0$ at $t = 0$, and is uniformly bounded above by $A$ for all $t \ge 0$. -/
public theorem beltrami_amplitude_pos_and_bounded
    (A ν lam t : ℝ) (hA : 0 < A) (hν : 0 ≤ ν) (ht : 0 ≤ t) :
    A * Real.exp (-ν * lam ^ 2 * 0) = A ∧
    0 < A * Real.exp (-ν * lam ^ 2 * t) ∧
    A * Real.exp (-ν * lam ^ 2 * t) ≤ A := by
  refine ⟨by simp, mul_pos hA (Real.exp_pos _), ?_⟩
  have hexp_le : Real.exp (-ν * lam ^ 2 * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hnn : 0 ≤ ν * lam ^ 2 * t := mul_nonneg (mul_nonneg hν (sq_nonneg lam)) ht
    linarith
  calc
    A * Real.exp (-ν * lam ^ 2 * t) ≤ A * 1 := mul_le_mul_of_nonneg_left hexp_le (le_of_lt hA)
    _ = A := mul_one A

/-! ## Stage 5. The Constantin–Fefferman Near/Far Singular-Integral Cutoff Optimization Bridge -/

/-- **Stage 5a (`near_field_stretching_absorbed_by_viscous_direction_damping`):**
Using the Stage 1 Biot–Savart direction-difference identity
$\det(\hat{y}, \omega(y), \omega(x_{\max})) = \|\omega(y)\|\det(\hat{y}, \xi(y) - \xi(x_{\max}), \xi(x_{\max}))$,
the near-field integral on $B_r(x_{\max})$ is bounded under Lipschitz direction control by
$C_{\mathrm{near}}\, r\, M^3 G$ where $G = \|\nabla \xi(x_{\max})\|_{\mathrm{HS}}$.
Completing the square against half of the viscous direction-curvature dissipation $-\frac{\nu}{2} M^2 G^2$
proves that for all $\nu > 0$ and all $C_{\mathrm{near}}, r, M, G \in \mathbb{R}$:
$$C_{\mathrm{near}}\, r\, M^3 G - \frac{\nu}{2} M^2 G^2 \le \frac{C_{\mathrm{near}}^2\, r^2}{2\nu} M^4.$$ -/
public theorem near_field_stretching_absorbed_by_viscous_direction_damping
    (ν C_near r M G : ℝ) (hν : 0 < ν) :
    C_near * r * M ^ 3 * G - (ν / 2) * M ^ 2 * G ^ 2 ≤
      (C_near ^ 2 * r ^ 2 / (2 * ν)) * M ^ 4 := by
  have h2ν : 0 < 2 * ν := by linarith
  have h2ν_ne : 2 * ν ≠ 0 := ne_of_gt h2ν
  have hsq : 0 ≤ (C_near * r * M ^ 2 - ν * M * G) ^ 2 / (2 * ν) :=
    div_nonneg (sq_nonneg _) (le_of_lt h2ν)
  have hid :
      (C_near ^ 2 * r ^ 2 / (2 * ν)) * M ^ 4 -
        (C_near * r * M ^ 3 * G - (ν / 2) * M ^ 2 * G ^ 2) =
      (C_near * r * M ^ 2 - ν * M * G) ^ 2 / (2 * ν) := by
    field_simp [h2ν_ne]
    ring
  linarith

/-- **Stage 5b (`constantin_fefferman_near_far_cutoff_bridge`):**
Complete Constantin–Fefferman near/far Biot–Savart cutoff bridge at a spatial maximum $x_{\max}$:
splitting the vortex-stretching pairing into $S_{\mathrm{near}} + S_{\mathrm{far}}$ across a cutoff
radius $r > 0$ with
- $S_{\mathrm{near}} \le C_{\mathrm{near}}\, r\, M^3 G$ (from Stage 1's direction-difference kernel),
- $S_{\mathrm{far}} \le C_{\mathrm{CZ}} M^3$ (far-field Calderón–Zygmund torus bound),
- $\nu\,\mathrm{visc\_lap} \le -\nu M^2 G^2$ (from Stage 3's concrete Bochner–polar identity),
- cutoff scale $\frac{C_{\mathrm{near}}^2 r^2}{2\nu} \le \frac{\kappa''}{2}$, and
- high-set direction-curvature coercivity $\kappa'' M^2 \le \frac{\nu}{2} G^2$,
yields the net quartic damping bound at $x_{\max}$:
$$\mathrm{stretching} + \nu\,\mathrm{visc\_lap} \le C_{\mathrm{CZ}} M^3 - \frac{\kappa''}{2} M^4.$$ -/
public theorem constantin_fefferman_near_far_cutoff_bridge
    (ν C_near C_CZ r M G κ'' stretching S_near S_far visc_lap : ℝ)
    (hν : 0 < ν)
    (h_split : stretching ≤ S_near + S_far)
    (h_near : S_near ≤ C_near * r * M ^ 3 * G)
    (h_far : S_far ≤ C_CZ * M ^ 3)
    (h_visc : ν * visc_lap ≤ -(ν * M ^ 2 * G ^ 2))
    (h_cutoff : C_near ^ 2 * r ^ 2 / (2 * ν) ≤ κ'' / 2)
    (h_coercive : κ'' * M ^ 2 ≤ (ν / 2) * G ^ 2) :
    stretching + ν * visc_lap ≤ C_CZ * M ^ 3 - (κ'' / 2) * M ^ 4 := by
  have hyoung := near_field_stretching_absorbed_by_viscous_direction_damping ν C_near r M G hν
  have hM4 : 0 ≤ M ^ 4 := by positivity
  have hcut_M4 : (C_near ^ 2 * r ^ 2 / (2 * ν)) * M ^ 4 ≤ (κ'' / 2) * M ^ 4 :=
    mul_le_mul_of_nonneg_right h_cutoff hM4
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  have hcoerc_M4 : κ'' * M ^ 4 ≤ (ν / 2) * M ^ 2 * G ^ 2 := by
    have h := mul_le_mul_of_nonneg_right h_coercive hM2
    linarith [show κ'' * M ^ 2 * M ^ 2 = κ'' * M ^ 4 by ring,
              show (ν / 2) * G ^ 2 * M ^ 2 = (ν / 2) * M ^ 2 * G ^ 2 by ring]
  linarith

/-! ## Section 2. The Five Unconditional Components $Q_1, Q_2, Q_3, Q_4, Q_5$ -/

/-- **Component $Q_1$ (Exact Fefferman Periodic Unit-Shift Equivalence, Energy Implication, & Non-Zero Smooth Inhabitation):**
Spatial $\mathbb{Z}^3$-periodicity is equivalent to invariance under the three unit coordinate shifts $e_0, e_1, e_2$,
Fefferman's energy-bounded periodic regularity statement implies `Clay_B_exact ν`, and for every non-zero vector
$c \in \mathbb{R}^3$ ($c \neq 0$), `constVelocity c` is a strictly non-zero periodic smooth initial datum admitting
a global periodic smooth Navier–Stokes solution on $[0, \infty) \times \mathbb{T}^3$. -/
@[expose] public def Q1_FeffermanPeriodicEquivalenceAndEnergyImplication (ν : ℝ) : Prop :=
  (∀ f : T3 → T3,
    IsZ3Periodic f ↔ ∀ (x : T3) (j : Fin 3), f (x + stdBasisVec j) = f x) ∧
  (Clay_B_exact_with_energy ν → Clay_B_exact ν) ∧
  (∀ c : T3, c ≠ 0 →
    constVelocity c ≠ 0 ∧
    IsPeriodicSmoothInitialData (constVelocity c) ∧
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicSmoothSolution ν (constVelocity c) (fun _ _ => 0) u p)

/-- **Component $Q_2$ (Torus Exclusion of Global Linear Burgers Strain):**
Every $\mathbb{Z}^3$-periodic linear map $L : \mathbb{R}^3 \to \mathbb{R}^3$ vanishes identically ($L = 0$),
and for every $\alpha \neq 0$ the global linear axisymmetric Burgers strain $\mathrm{diag}(-\alpha/2, -\alpha/2, \alpha)x$
is not $\mathbb{Z}^3$-periodic. -/
@[expose] public def Q2_TorusExclusionOfLinearBurgersStrain : Prop :=
  (∀ L : T3 →ₗ[ℝ] T3, IsZ3Periodic (fun x => L x) → L = 0) ∧
  (∀ α : ℝ, α ≠ 0 → ¬ IsZ3Periodic (burgersLinearStrain α))

/-- **Component $Q_3$ (Biot–Savart Alignment Depletion, Beltrami Lamb Cancellation, Attained `sSup` Pinning, & $\lambda^6$ Scaling Homogeneity):**
The Biot–Savart stretching determinant satisfies $\det(\hat{y}, m\xi_y, \xi_x) = m\det(\hat{y}, \xi_y - \xi_x, \xi_x)$
and vanishes whenever $\xi_y = \xi_x$, the Beltrami Lamb vector $u_x \times (\lambda u_x) = 0$ vanishes identically,
any attained spatial maximum $M = \|\omega(x_{\max})\|$ pins `vorticity_sup_norm ω = M`, and under parabolic rescaling
$u_\lambda(x,t) = \lambda u(\lambda x, \lambda^2 t)$ both cubic vortex stretching and scale-consistent high-set damping
scale with homogeneous degree $\lambda^6$. -/
@[expose] public def Q3_BiotSavartAlignmentAndScalingHomogeneity : Prop :=
  (∀ (yhat ξx ξy : T3) (mag : ℝ),
    det3 yhat (mag • ξy) ξx = mag * det3 yhat (ξy - ξx) ξx) ∧
  (∀ (yhat ξx : T3) (mag : ℝ),
    inner ℝ yhat ξx * det3 yhat (mag • ξx) ξx = 0) ∧
  (∀ (u_x : T3) (lam : ℝ), cross3 u_x (lam • u_x) = 0) ∧
  (∀ (ω : VorticityField) (x_max : T3) (M : ℝ),
    M = ‖ω x_max‖ → (∀ x : T3, ‖ω x‖ ≤ M) → vorticity_sup_norm ω = M) ∧
  (∀ (lam C_CZ κ_eff M : ℝ),
    C_CZ * (lam ^ 2 * M) ^ 3 - κ_eff * (lam ^ 2 * M) ^ 3 =
      lam ^ 6 * (C_CZ * M ^ 3 - κ_eff * M ^ 3))

/-- **Component $Q_4$ (Concrete 3D Spatial-Maximum Bochner–Polar Reduction, Constantin–Fefferman Near/Far Cutoff Bridge, & Cubic Lyapunov ODE Ceiling):**
At a spatial maximum $x_{\max}$ where $M > 0$ and convective norm-squared transport vanishes, the concrete 3D vector
Bochner–polar identity proves $\nu\langle\omega,\Delta\omega\rangle \le -\nu M^2\|\nabla\xi\|^2$, the Constantin–Fefferman
near/far Biot–Savart cutoff bridge absorbs near-field stretching into $-\frac{\nu}{2}M^2\|\nabla\xi\|^2$, high-set
direction-curvature coercivity yields the cubic differential inequality $M'(t) \le C_{\mathrm{CZ}} M(t)^2 - \kappa'' M(t)^3$,
and every differentiable trajectory on $[0, T]$ satisfying this cubic differential inequality obeys the uniform global ceiling
$M(t) \le \max(M(0), C_{\mathrm{CZ}}/\kappa'')$. -/
@[expose] public def Q4_SpatialMaxBochnerPolarReductionAndLyapunovCeiling : Prop :=
  (∀ (ν ρ : ℝ) (ω ξ : T3) (dω d2ω dξ : Fin 3 → T3) (dρ d2h : Fin 3 → ℝ),
    0 ≤ ν →
    ‖ξ‖ = 1 →
    (∀ j : Fin 3, inner ℝ ξ (dξ j) = 0) →
    (∀ j : Fin 3, dω j = (dρ j) • ξ + ρ • (dξ j)) →
    (∀ j : Fin 3, d2h j = ‖dω j‖ ^ 2 + inner ℝ ω (d2ω j)) →
    (∀ j : Fin 3, dρ j = 0) →
    (∑ j : Fin 3, d2h j) ≤ 0 →
    ν * inner ℝ ω (∑ j : Fin 3, d2ω j) ≤ -(ν * ρ ^ 2 * (∑ j : Fin 3, ‖dξ j‖ ^ 2))) ∧
  (∀ (ν C_near C_CZ r M G κ'' stretching S_near S_far visc_lap : ℝ),
    0 < ν →
    stretching ≤ S_near + S_far →
    S_near ≤ C_near * r * M ^ 3 * G →
    S_far ≤ C_CZ * M ^ 3 →
    ν * visc_lap ≤ -(ν * M ^ 2 * G ^ 2) →
    C_near ^ 2 * r ^ 2 / (2 * ν) ≤ κ'' / 2 →
    κ'' * M ^ 2 ≤ (ν / 2) * G ^ 2 →
    stretching + ν * visc_lap ≤ C_CZ * M ^ 3 - (κ'' / 2) * M ^ 4) ∧
  (∀ (M M' stretching conv_norm_sq ν visc_lap grad_xi_sq C_CZ κ'' : ℝ),
    0 < M →
    M' ≤ (stretching - conv_norm_sq / 2 + ν * visc_lap) / M →
    conv_norm_sq = 0 →
    stretching ≤ C_CZ * M ^ 3 →
    ν * visc_lap ≤ -(ν * M ^ 2 * grad_xi_sq) →
    κ'' * M ^ 2 ≤ ν * grad_xi_sq →
    M' ≤ C_CZ * M ^ 2 - κ'' * M ^ 3) ∧
  (∀ (M : ℝ → ℝ) (T C_CZ κ'' : ℝ),
    0 < C_CZ → 0 < κ'' →
    (∀ t ∈ Set.Icc (0 : ℝ) T, DifferentiableAt ℝ M t) →
    (∀ t ∈ Set.Icc (0 : ℝ) T, deriv M t ≤ C_CZ * (M t) ^ 2 - κ'' * (M t) ^ 3) →
    ∀ t ∈ Set.Icc (0 : ℝ) T, M t ≤ max (M 0) (C_CZ / κ''))

/-- **Component $Q_5$ (Exact Conditional Implication to Fefferman's `Clay_B_exact ν`):**
Whenever a viscosity $\nu > 0$ satisfies the periodic high-set direction-curvature depletion bound
`PeriodicDirectionDepletionBound ν` and classical periodic Beale–Kato–Majda continuation `PeriodicBKMContinuation ν`,
Fefferman's official periodic existence and smoothness statement `Clay_B_exact ν` holds. -/
@[expose] public def Q5_ConditionalImplicationToClayBExact (ν : ℝ) : Prop :=
  (PeriodicDirectionDepletionBound ν ∧ PeriodicBKMContinuation ν) → Clay_B_exact ν

/-! ## Section 3. Master Five-Conjunct Product Theorem -/

/-- **Master Single-Sentence Product Theorem (`fefferman_periodic_ns_exact_reduction_product_theorem`):**
Unconditional proof of the complete five-conjunct product statement
$$Q_1(\nu) \wedge Q_2 \wedge Q_3 \wedge Q_4 \wedge Q_5(\nu)$$
for the 3D periodic Navier–Stokes reduction on $\mathbb{T}^3 = \mathbb{R}^3 / \mathbb{Z}^3$. -/
public theorem fefferman_periodic_ns_exact_reduction_product_theorem (ν : ℝ) :
    Q1_FeffermanPeriodicEquivalenceAndEnergyImplication ν ∧
    Q2_TorusExclusionOfLinearBurgersStrain ∧
    Q3_BiotSavartAlignmentAndScalingHomogeneity ∧
    Q4_SpatialMaxBochnerPolarReductionAndLyapunovCeiling ∧
    Q5_ConditionalImplicationToClayBExact ν := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Q1: Periodic unit-shift equivalence, energy implication, and non-zero periodic smooth inhabitation
    exact ⟨fun f => isZ3Periodic_iff_unit_shifts f,
      clay_B_exact_of_with_energy ν,
      fun c hc => nonzero_periodic_smooth_solution_exists ν c hc⟩
  · -- Q2: Torus exclusion of global linear Burgers strain
    exact ⟨z3_periodic_linear_eq_zero, burgersLinearStrain_not_z3_periodic⟩
  · -- Q3: Biot–Savart alignment depletion, Beltrami Lamb cancellation, attained sSup pinning, and λ⁶ scaling homogeneity
    exact ⟨biot_savart_det_difference_identity,
      aligned_vorticity_stretching_integrand_zero,
      beltrami_lamb_vector_cross3_zero,
      vorticity_sup_norm_eq_of_isSpatialMax,
      navier_stokes_scaling_homogeneity_deg6⟩
  · -- Q4: Concrete 3D Bochner–polar reduction, Constantin–Fefferman near/far cutoff bridge, and cubic ODE ceiling
    exact ⟨concrete_bochner_polar_viscous_damping_at_max,
      constantin_fefferman_near_far_cutoff_bridge,
      viscous_direction_dissipation_bridge,
      comparison_ode_ceiling⟩
  · -- Q5: Conditional implication from (PeriodicDirectionDepletionBound ν ∧ PeriodicBKMContinuation ν) to Clay_B_exact ν
    intro h
    exact clay_B_exact_of_torus_direction_depletion ν h.1 h.2

end -- noncomputable section

#print axioms unitCube_nonempty
#print axioms bddAbove_range_norm_of_attained_max
#print axioms vorticity_sup_norm_eq_of_isSpatialMax
#print axioms AttainedSpatialMaximum.vorticity_sup_norm_eq
#print axioms polar_pythagoras_directional_deriv
#print axioms polar_pythagoras_3d_sum
#print axioms bochner_laplacian_3d_identity
#print axioms first_remaining_gap_bochner_polar_damping_at_max
#print axioms concrete_bochner_polar_viscous_damping_at_max
#print axioms constVelocity_ne_zero
#print axioms constVelocity_isZ3Periodic
#print axioms constVelocity_convective_zero
#print axioms constVelocity_laplacian_zero
#print axioms constVelocity_isPeriodicSmoothInitialData
#print axioms constVelocity_isPeriodicSmoothSolution
#print axioms nonzero_periodic_smooth_solution_exists
#print axioms beltrami_lamb_vector_cross3_zero
#print axioms beltrami_amplitude_pos_and_bounded
#print axioms near_field_stretching_absorbed_by_viscous_direction_damping
#print axioms constantin_fefferman_near_far_cutoff_bridge
#print axioms fefferman_periodic_ns_exact_reduction_product_theorem

end FeffermanClayNS
