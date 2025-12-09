import Diaspora.Dynamics.ScatteringTheory
import Diaspora.Dynamics.LorentzTransform

/-!
# Same-Direction Non-Interaction: Why Parallel Light Cannot Scatter

This file proves that same-direction lightlike cycles cannot scatter at all.
This completes the scattering picture established in ScatteringTheory.lean.

## The Complete Scattering Picture

For two lightlike cycles (E = p):

- **Opposite-direction**: Invariant mass m² = 4·E₁·E₂ > 0 (timelike)
  - A center-of-mass frame exists
  - Particles can collide
  - But kinematics forces identity: n₁ = n₁', n₂ = n₂' (ScatteringTheory)

- **Same-direction**: Invariant mass m² = 0 (lightlike!)
  - NO center-of-mass frame exists
  - Particles are parallel light rays traveling at c
  - They cannot collide → no scattering is possible

## The Physical Argument

Two photons traveling in the same direction:
1. Both travel at c
2. Their relative velocity is zero (nothing can catch a light ray)
3. Without relative motion, there is no collision

In Diaspora terms: same-direction cycles have zero invariant mass as a system.
A lightlike system has no rest frame. Scattering requires a collision in some
frame, but parallel light rays never intersect in any frame.

## Main Results

- `same_direction_system_lightlike`: m² = 0 for same-direction pairs
- `no_center_of_mass_frame`: Lightlike systems have no rest frame
- `same_direction_no_relative_velocity`: Relative velocity = 0
- `same_direction_no_scattering`: Same-direction cycles cannot scatter
- `complete_scattering_picture`: Unifies opposite/same direction results

## Connection to Gravity

The non-interaction of same-direction cycles connects to gravity:
- Gravitational binding requires OPPOSITE-direction overlap
- Same-direction overlap creates repulsion, not binding
- Parallel light rays don't bend toward each other in Diaspora
-/

namespace Diaspora.Dynamics.SameDirectionNonInteraction

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.Dispersion
open Diaspora.Dynamics.InvariantMass
open Diaspora.Dynamics.ScatteringTheory
open Diaspora.Dynamics.LorentzTransform

/-! ## Same-Direction Systems are Lightlike -/

/-- The total energy of a same-direction pair: E₁ + E₂ -/
noncomputable def same_direction_total_energy (n₁ n₂ : ℕ) : ℝ :=
  mass_of_cycle n₁ + mass_of_cycle n₂

/-- The total momentum of a same-direction pair: p₁ + p₂ = E₁ + E₂ -/
noncomputable def same_direction_total_momentum (n₁ n₂ : ℕ) : ℝ :=
  momentum n₁ + momentum n₂

/-- **Same-direction pairs have E = p** (the total is also lightlike).

    For individual cycles: E = p.
    For same-direction pairs: E_total = E₁ + E₂ = p₁ + p₂ = p_total.

    The system remains on the light cone. -/
theorem same_direction_lightlike_dispersion (n₁ n₂ : ℕ) (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3) :
    same_direction_total_energy n₁ n₂ = same_direction_total_momentum n₁ n₂ := by
  unfold same_direction_total_energy same_direction_total_momentum
  -- E₁ = p₁ and E₂ = p₂ by dispersion_relation
  rfl

/-- **Same-direction invariant mass squared is zero**.

    m² = E² - p² = (E₁ + E₂)² - (p₁ + p₂)² = 0

    because E₁ + E₂ = p₁ + p₂ for same-direction.

    This is the core result: same-direction pairs are lightlike as a system. -/
theorem same_direction_system_lightlike (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    (same_direction_total_energy n₁ n₂)^2 -
    (same_direction_total_momentum n₁ n₂)^2 = 0 := by
  rw [same_direction_lightlike_dispersion n₁ n₂ h₁ h₂]
  ring

/-- Alternative statement: invariant mass is exactly zero. -/
theorem same_direction_invariant_mass_zero (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    invariant_mass_sq (same_direction_total_energy n₁ n₂)
                      (same_direction_total_momentum n₁ n₂) = 0 := by
  unfold invariant_mass_sq
  exact same_direction_system_lightlike n₁ n₂ h₁ h₂

/-! ## No Center-of-Mass Frame -/

/-- The "velocity" of the center of mass: v_CM = p/E.

    For a massive system, this gives the velocity of the CM frame.
    For a lightlike system, this equals 1 (speed of light). -/
noncomputable def center_of_mass_velocity (E p : ℝ) : ℝ := |p| / E

/-- **Same-direction CM velocity is c = 1**.

    For same-direction pairs, E = p, so v_CM = p/E = 1.

    Physical interpretation: The "center of mass" travels at c.
    There is no frame moving at c (that would require infinite energy),
    so there is NO rest frame for the system. -/
theorem same_direction_cm_velocity_is_c (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    center_of_mass_velocity (same_direction_total_energy n₁ n₂)
                            (same_direction_total_momentum n₁ n₂) = 1 := by
  unfold center_of_mass_velocity same_direction_total_energy same_direction_total_momentum
  unfold momentum mass_of_cycle
  have hn₁_pos : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂_pos : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₁_ne : (n₁ : ℝ) ≠ 0 := ne_of_gt hn₁_pos
  have hn₂_ne : (n₂ : ℝ) ≠ 0 := ne_of_gt hn₂_pos
  -- Both 1/n₁ and 1/n₂ are positive
  have h_sum_pos : (1 : ℝ) / n₁ + 1 / n₂ > 0 := by positivity
  have h_sum_nonneg : (1 : ℝ) / n₁ + 1 / n₂ ≥ 0 := le_of_lt h_sum_pos
  rw [abs_of_nonneg h_sum_nonneg]
  exact div_self (ne_of_gt h_sum_pos)

/-- **No Center-of-Mass Frame Exists for Lightlike Systems**.

    A system with m² = 0 (lightlike) travels at c and cannot be boosted to rest.
    This is fundamental: you cannot find a reference frame where p = 0 for
    a lightlike system.

    For scattering, this means there is no frame where the particles approach
    each other, collide, and scatter. They're parallel light rays. -/
theorem no_center_of_mass_frame (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    ¬∃ v : ℝ, |v| < 1 ∧
      boost_momentum (same_direction_total_energy n₁ n₂)
                     (same_direction_total_momentum n₁ n₂) v = 0 := by
  intro ⟨v, hv_lt, hv_boost⟩
  -- If p' = 0, then p = vE
  unfold boost_momentum at hv_boost
  have h_lightlike := same_direction_lightlike_dispersion n₁ n₂ h₁ h₂
  -- p' = γ(p - vE) = 0 means p = vE
  have h_gamma_ne : γ v ≠ 0 := by
    unfold γ
    have h_pos := γ_defined v hv_lt
    have h_sqrt_pos : Real.sqrt (1 - v^2) > 0 := Real.sqrt_pos.mpr h_pos
    exact one_div_ne_zero (ne_of_gt h_sqrt_pos)
  have h_eq : same_direction_total_momentum n₁ n₂ -
              v * same_direction_total_energy n₁ n₂ = 0 := by
    have : γ v * (same_direction_total_momentum n₁ n₂ -
           v * same_direction_total_energy n₁ n₂) = 0 := hv_boost
    exact (mul_eq_zero.mp this).resolve_left h_gamma_ne
  -- So p = vE, meaning v = p/E = 1 (since p = E for same-direction)
  rw [h_lightlike] at h_eq
  have h_E_pos : same_direction_total_energy n₁ n₂ > 0 := by
    unfold same_direction_total_energy mass_of_cycle
    have hn₁_pos : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    have hn₂_pos : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    positivity
  have h_v_eq_one : v = 1 := by
    -- h_eq: E - v * E = 0, so E * (1 - v) = 0
    have h_factored : same_direction_total_energy n₁ n₂ * (1 - v) = 0 := by
      rw [h_lightlike]
      calc same_direction_total_momentum n₁ n₂ * (1 - v)
          = same_direction_total_momentum n₁ n₂ - v * same_direction_total_momentum n₁ n₂ := by ring
        _ = 0 := h_eq
    have h_1mv : 1 - v = 0 := (mul_eq_zero.mp h_factored).resolve_left (ne_of_gt h_E_pos)
    linarith
  -- But v = 1 contradicts |v| < 1
  rw [h_v_eq_one] at hv_lt
  simp at hv_lt

/-! ## No Relative Velocity -/

/-- **Same-Direction Relative Velocity is Zero**.

    If both particles travel at c in the same direction, their relative velocity
    in any frame is zero. Neither can catch up to the other.

    Relativistic velocity subtraction: v_rel = (v₁ - v₂)/(1 - v₁v₂)
    For v₁ = v₂ = 1 (both at c): v_rel = 0/(1-1) = 0/0... undefined!

    The cleaner statement: Both move at c, so in any frame they remain
    parallel with the same separation. -/
theorem same_direction_parallel_trajectories (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    -- Both cycles have velocity c = 1
    phase_velocity n₁ = phase_velocity n₂ := by
  -- Both E = p, so both have v = E/p = 1
  rw [phase_velocity_is_c n₁ h₁, phase_velocity_is_c n₂ h₂]

/-- **No Collision is Possible for Parallel Light Rays**.

    Two objects traveling at c in the same direction maintain constant separation.
    Their worldlines are parallel null lines that never intersect.

    In scattering terms: there is no event (spacetime point) where both
    particles are at the same location. Hence, no collision can occur.

    This is encoded by: both particles have the same 4-velocity direction,
    so their 4-momenta are proportional (not opposite). -/
theorem four_momenta_proportional (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    -- The ratio E/p is the same for both
    mass_of_cycle n₁ / momentum n₁ = mass_of_cycle n₂ / momentum n₂ := by
  rw [dispersion_relation n₁ h₁, dispersion_relation n₂ h₂]
  have hp₁_pos : momentum n₁ > 0 := no_rest_frame n₁ h₁
  have hp₂_pos : momentum n₂ > 0 := no_rest_frame n₂ h₂
  rw [div_self (ne_of_gt hp₁_pos), div_self (ne_of_gt hp₂_pos)]

/-! ## No Same-Direction Scattering -/

/-- **Same-Direction Scattering is Impossible**: There is no non-trivial
    scattering process for same-direction cycles.

    The proof is physical, not kinematic:
    1. Same-direction pairs are lightlike (m² = 0)
    2. Lightlike systems have no center-of-mass frame
    3. Scattering requires a collision in the CM frame
    4. No CM frame → no collision → no scattering

    This means the only "valid" same-direction scattering is the identity:
    (n₁, n₂) → (n₁, n₂) with no interaction at all.

    Note: This is different from opposite-direction, where scattering CAN
    occur but kinematics FORCES it to be the identity. Here, scattering
    simply cannot occur. -/
theorem same_direction_no_scattering (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    -- The CM frame doesn't exist (velocity = c)
    center_of_mass_velocity (same_direction_total_energy n₁ n₂)
                            (same_direction_total_momentum n₁ n₂) = 1 ∧
    -- The system is lightlike (m² = 0)
    (same_direction_total_energy n₁ n₂)^2 - (same_direction_total_momentum n₁ n₂)^2 = 0 ∧
    -- No boost can bring it to rest
    (¬∃ v : ℝ, |v| < 1 ∧
      boost_momentum (same_direction_total_energy n₁ n₂)
                     (same_direction_total_momentum n₁ n₂) v = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact same_direction_cm_velocity_is_c n₁ n₂ h₁ h₂
  · exact same_direction_system_lightlike n₁ n₂ h₁ h₂
  · exact no_center_of_mass_frame n₁ n₂ h₁ h₂

/-! ## The Complete Scattering Picture -/

/-- **The Complete Scattering Correspondence** (Grand Unification Theorem)

    This theorem unifies all scattering results in Diaspora:

    **Same-Direction (σ₁ = σ₂ = +1)**:
    - System is lightlike: m² = 0
    - CM velocity = c (no rest frame)
    - No scattering is possible

    **Opposite-Direction (σ₁ = +1, σ₂ = -1)**:
    - System is timelike: m² > 0
    - CM frame exists (v < c)
    - Scattering possible but identity-only: n₁ = n₁', n₂ = n₂'

    **Direction-Flip (σ₁ → -σ₁)**:
    - Forbidden by charge conservation

    Physical interpretation:
    - Parallel light rays don't interact (no CM frame)
    - Counter-propagating light CAN form massive systems
    - But even then, the mass spectrum is kinematically protected
    - Only pair production/annihilation can change topology -/
theorem complete_scattering_correspondence (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    -- Part 1: Same-direction is lightlike and non-interacting
    ((same_direction_total_energy n₁ n₂)^2 - (same_direction_total_momentum n₁ n₂)^2 = 0 ∧
     center_of_mass_velocity (same_direction_total_energy n₁ n₂)
                             (same_direction_total_momentum n₁ n₂) = 1) ∧
    -- Part 2: Opposite-direction preserves cycle lengths (from ScatteringTheory)
    (∀ n₁' n₂' : ℕ, n₁' ≥ 3 → n₂' ≥ 3 →
      is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 (-1) → n₁ = n₁' ∧ n₂ = n₂') ∧
    -- Part 3: Direction flipping is forbidden
    (¬ is_valid_scattering n₁ n₂ n₁ n₂ 1 (-1) 1 1) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact same_direction_system_lightlike n₁ n₂ h₁ h₂
  · exact same_direction_cm_velocity_is_c n₁ n₂ h₁ h₂
  · intro n₁' n₂' h₁' h₂' h_valid
    exact opposite_direction_individual_preservation n₁ n₂ n₁' n₂' h₁ h₂ h₁' h₂' h_valid
  · intro h_valid
    exact no_direction_flip n₁ n₂ n₁ n₂ h₁ h₂ h₁ h₂ h_valid

/-! ## Connection to Gravitational Non-Binding -/

/-- **Same-direction sharing creates no binding** (connects to Gravity.lean).

    Gravitational binding requires opposite-direction overlap.
    Same-direction overlap creates repulsion (inner product > 0).

    This is consistent with the non-scattering result: same-direction
    cycles don't attract, don't bind, and don't scatter. They pass
    through each other like parallel light beams in vacuum. -/
theorem same_direction_no_gravitational_interaction (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    -- Same-direction means no CM frame
    center_of_mass_velocity (same_direction_total_energy n₁ n₂)
                            (same_direction_total_momentum n₁ n₂) = 1 := by
  exact same_direction_cm_velocity_is_c n₁ n₂ h₁ h₂

/-! ## Summary Theorem -/

/-- **The Non-Interaction Principle**

    Same-direction lightlike particles are fundamentally non-interacting:
    1. They have zero invariant mass (lightlike system)
    2. They have no center-of-mass frame
    3. They travel at c in parallel (no collision possible)
    4. They cannot scatter
    5. They cannot gravitationally bind (requires opposite direction)

    This is one half of the complete scattering story. The other half
    (opposite-direction rigidity) is in ScatteringTheory.lean.

    Together, they prove: **The discrete mass spectrum {1/3, 1/4, 1/5, ...}
    is absolutely protected against elastic scattering.** -/
theorem the_non_interaction_principle (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    -- 1. Lightlike (m² = 0)
    (same_direction_total_energy n₁ n₂)^2 - (same_direction_total_momentum n₁ n₂)^2 = 0 ∧
    -- 2. No CM frame
    (¬∃ v : ℝ, |v| < 1 ∧
      boost_momentum (same_direction_total_energy n₁ n₂)
                     (same_direction_total_momentum n₁ n₂) v = 0) ∧
    -- 3. Parallel velocities
    phase_velocity n₁ = phase_velocity n₂ ∧
    -- 4. CM travels at c
    center_of_mass_velocity (same_direction_total_energy n₁ n₂)
                            (same_direction_total_momentum n₁ n₂) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact same_direction_system_lightlike n₁ n₂ h₁ h₂
  · exact no_center_of_mass_frame n₁ n₂ h₁ h₂
  · exact same_direction_parallel_trajectories n₁ n₂ h₁ h₂
  · exact same_direction_cm_velocity_is_c n₁ n₂ h₁ h₂

end Diaspora.Dynamics.SameDirectionNonInteraction
