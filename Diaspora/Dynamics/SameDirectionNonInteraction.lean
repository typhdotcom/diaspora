import Diaspora.Dynamics.ScatteringTheory
import Diaspora.Dynamics.LorentzTransform

/-!
# Same-Direction Non-Interaction

Same-direction lightlike cycles have m² = 0, no CM frame, and cannot scatter.
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

/-- Same-direction pairs have E = p (the total is also lightlike). -/
theorem same_direction_lightlike_dispersion (n₁ n₂ : ℕ) (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3) :
    same_direction_total_energy n₁ n₂ = same_direction_total_momentum n₁ n₂ := by
  unfold same_direction_total_energy same_direction_total_momentum
  rfl

/-- Same-direction invariant mass squared is zero. -/
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

/-- Center of mass velocity: v_CM = |p|/E. -/
noncomputable def center_of_mass_velocity (E p : ℝ) : ℝ := |p| / E

/-- Same-direction CM velocity is c = 1. -/
theorem same_direction_cm_velocity_is_c (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    center_of_mass_velocity (same_direction_total_energy n₁ n₂)
                            (same_direction_total_momentum n₁ n₂) = 1 := by
  unfold center_of_mass_velocity same_direction_total_energy same_direction_total_momentum
  unfold momentum mass_of_cycle
  have hn₁_pos : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂_pos : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_sum_pos : (1 : ℝ) / n₁ + 1 / n₂ > 0 := by positivity
  have h_sum_nonneg : (1 : ℝ) / n₁ + 1 / n₂ ≥ 0 := le_of_lt h_sum_pos
  rw [abs_of_nonneg h_sum_nonneg]
  exact div_self (ne_of_gt h_sum_pos)

/-- No center-of-mass frame exists for lightlike systems. -/
theorem no_center_of_mass_frame (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    ¬∃ v : ℝ, |v| < 1 ∧
      boost_momentum (same_direction_total_energy n₁ n₂)
                     (same_direction_total_momentum n₁ n₂) v = 0 := by
  intro ⟨v, hv_lt, hv_boost⟩
  unfold boost_momentum at hv_boost
  have h_lightlike := same_direction_lightlike_dispersion n₁ n₂ h₁ h₂
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
  rw [h_lightlike] at h_eq
  have h_E_pos : same_direction_total_energy n₁ n₂ > 0 := by
    unfold same_direction_total_energy mass_of_cycle
    have hn₁_pos : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    have hn₂_pos : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    positivity
  have h_v_eq_one : v = 1 := by
    have h_factored : same_direction_total_energy n₁ n₂ * (1 - v) = 0 := by
      rw [h_lightlike]
      calc same_direction_total_momentum n₁ n₂ * (1 - v)
          = same_direction_total_momentum n₁ n₂ - v * same_direction_total_momentum n₁ n₂ := by ring
        _ = 0 := h_eq
    have h_1mv : 1 - v = 0 := (mul_eq_zero.mp h_factored).resolve_left (ne_of_gt h_E_pos)
    linarith
  rw [h_v_eq_one] at hv_lt
  simp at hv_lt

/-! ## No Relative Velocity -/

/-- Same-direction cycles have identical phase velocities (both c). -/
theorem same_direction_parallel_trajectories (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    phase_velocity n₁ = phase_velocity n₂ := by
  rw [phase_velocity_is_c n₁ h₁, phase_velocity_is_c n₂ h₂]

/-- Four-momenta are proportional (same 4-velocity direction, no collision possible). -/
theorem four_momenta_proportional (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    mass_of_cycle n₁ / momentum n₁ = mass_of_cycle n₂ / momentum n₂ := by
  rw [dispersion_relation n₁ h₁, dispersion_relation n₂ h₂]
  have hp₁_pos : momentum n₁ > 0 := no_rest_frame n₁ h₁
  have hp₂_pos : momentum n₂ > 0 := no_rest_frame n₂ h₂
  rw [div_self (ne_of_gt hp₁_pos), div_self (ne_of_gt hp₂_pos)]

/-! ## No Same-Direction Scattering -/

/-- Same-direction scattering is impossible (no CM frame). -/
theorem same_direction_no_scattering (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    center_of_mass_velocity (same_direction_total_energy n₁ n₂)
                            (same_direction_total_momentum n₁ n₂) = 1 ∧
    (same_direction_total_energy n₁ n₂)^2 - (same_direction_total_momentum n₁ n₂)^2 = 0 ∧
    (¬∃ v : ℝ, |v| < 1 ∧
      boost_momentum (same_direction_total_energy n₁ n₂)
                     (same_direction_total_momentum n₁ n₂) v = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact same_direction_cm_velocity_is_c n₁ n₂ h₁ h₂
  · exact same_direction_system_lightlike n₁ n₂ h₁ h₂
  · exact no_center_of_mass_frame n₁ n₂ h₁ h₂

/-! ## The Complete Scattering Picture -/

/-- Complete scattering correspondence: same-direction non-interacting,
    opposite-direction preserves n, direction-flip forbidden. -/
theorem complete_scattering_correspondence (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    ((same_direction_total_energy n₁ n₂)^2 - (same_direction_total_momentum n₁ n₂)^2 = 0 ∧
     center_of_mass_velocity (same_direction_total_energy n₁ n₂)
                             (same_direction_total_momentum n₁ n₂) = 1) ∧
    (∀ n₁' n₂' : ℕ, n₁' ≥ 3 → n₂' ≥ 3 →
      is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 (-1) → n₁ = n₁' ∧ n₂ = n₂') ∧
    (¬ is_valid_scattering n₁ n₂ n₁ n₂ 1 (-1) 1 1) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact same_direction_system_lightlike n₁ n₂ h₁ h₂
  · exact same_direction_cm_velocity_is_c n₁ n₂ h₁ h₂
  · intro n₁' n₂' h₁' h₂' h_valid
    exact opposite_direction_individual_preservation n₁ n₂ n₁' n₂' h₁ h₂ h₁' h₂' h_valid
  · intro h_valid
    exact no_direction_flip n₁ n₂ n₁ n₂ h₁ h₂ h₁ h₂ h_valid

/-! ## Connection to Gravitational Non-Binding -/

/-- Same-direction creates no gravitational binding (no CM frame, v_CM = c). -/
theorem same_direction_no_gravitational_interaction (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    center_of_mass_velocity (same_direction_total_energy n₁ n₂)
                            (same_direction_total_momentum n₁ n₂) = 1 := by
  exact same_direction_cm_velocity_is_c n₁ n₂ h₁ h₂

/-! ## Summary Theorem -/

/-- Non-interaction principle: m² = 0, no CM frame, parallel velocities, v_CM = c. -/
theorem the_non_interaction_principle (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    (same_direction_total_energy n₁ n₂)^2 - (same_direction_total_momentum n₁ n₂)^2 = 0 ∧
    (¬∃ v : ℝ, |v| < 1 ∧
      boost_momentum (same_direction_total_energy n₁ n₂)
                     (same_direction_total_momentum n₁ n₂) v = 0) ∧
    phase_velocity n₁ = phase_velocity n₂ ∧
    center_of_mass_velocity (same_direction_total_energy n₁ n₂)
                            (same_direction_total_momentum n₁ n₂) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact same_direction_system_lightlike n₁ n₂ h₁ h₂
  · exact no_center_of_mass_frame n₁ n₂ h₁ h₂
  · exact same_direction_parallel_trajectories n₁ n₂ h₁ h₂
  · exact same_direction_cm_velocity_is_c n₁ n₂ h₁ h₂

end Diaspora.Dynamics.SameDirectionNonInteraction
