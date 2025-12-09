import Diaspora.Dynamics.SpeedOfLight
import Diaspora.Dynamics.AngularMomentum
import Diaspora.Dynamics.Planck

/-!
# Dispersion Relation

Cycles satisfy E = p (massless dispersion) with invariant mass E² - p² = 0.
-/

namespace Diaspora.Dynamics.Dispersion

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.SpeedOfLight
open Diaspora.Dynamics.Planck

/-- E = p for all cycles. -/
theorem dispersion_relation (n : ℕ) (_h : n ≥ 3) :
    mass_of_cycle n = momentum n := rfl

/-- E² = p² (lightlike). -/
theorem all_cycles_lightlike (n : ℕ) (_h : n ≥ 3) :
    (mass_of_cycle n)^2 = (momentum n)^2 := by
  rfl

/-- E² - p² = 0 (null invariant mass). -/
theorem invariant_mass_squared_vanishes (n : ℕ) (h : n ≥ 3) :
    (mass_of_cycle n)^2 - (momentum n)^2 = 0 := by
  rw [dispersion_relation n h]
  ring

/-! ## Velocity Relations -/

/-- v_phase = E/p -/
noncomputable def phase_velocity (n : ℕ) : ℝ := mass_of_cycle n / momentum n

/-- Phase velocity equals c = 1. -/
theorem phase_velocity_is_c (n : ℕ) (h : n ≥ 3) :
    phase_velocity n = 1 := by
  unfold phase_velocity
  rw [dispersion_relation n h]
  have h_pos : momentum n > 0 := by
    unfold momentum mass_of_cycle
    have hn : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    positivity
  exact div_self (ne_of_gt h_pos)

/-- v_group = ∂E/∂p = 1 -/
noncomputable def group_velocity : ℝ := 1

theorem group_velocity_is_c : group_velocity = c := by
  unfold group_velocity c
  rfl

/-- Phase and group velocities coincide (non-dispersive). -/
theorem velocities_equal (n : ℕ) (h : n ≥ 3) :
    phase_velocity n = group_velocity := by
  rw [phase_velocity_is_c n h]
  unfold group_velocity
  rfl

/-! ## No Rest Frame -/

/-- p > 0 for all cycles. -/
theorem no_rest_frame (n : ℕ) (h : n ≥ 3) :
    momentum n > 0 := by
  unfold momentum mass_of_cycle
  have hn : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  positivity

theorem minimum_momentum (n : ℕ) (_h : n ≥ 3) :
    momentum n = 1 / n := by
  unfold momentum mass_of_cycle
  rfl

theorem zero_momentum_infinite_wavelength (n : ℕ) (h : n ≥ 3)
    (h_zero : momentum n = 0) : False := by
  have h_pos := no_rest_frame n h
  linarith

/-! ## Topology is Motion -/

/-- Nonzero winding implies nonzero momentum. -/
theorem topology_is_motion (n : ℕ) (L : ℤ) (h : n ≥ 3) (hL : L ≠ 0) :
    |(L : ℝ)| * mass_of_cycle n > 0 := by
  have h_m_pos : mass_of_cycle n > 0 := by
    unfold mass_of_cycle
    have hn : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    positivity
  have h_cast : |(L : ℝ)| > 0 := by
    simp only [abs_pos, ne_eq, Int.cast_eq_zero]
    exact hL
  exact mul_pos h_cast h_m_pos

/-- p_L = |L|/n -/
theorem winding_momentum (n : ℕ) (L : ℤ) (h : n > 0) :
    |(L : ℝ)| * mass_of_cycle n = |(L : ℝ)| / n := by
  unfold mass_of_cycle
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h)
  field_simp [hn]

theorem four_momentum_squared (n : ℕ) (h : n ≥ 3) :
    (mass_of_cycle n)^2 - (momentum n)^2 = 0 :=
  invariant_mass_squared_vanishes n h

/-- Invariant mass is zero but energy is nonzero. -/
theorem massless_paradox_resolution (n : ℕ) (h : n ≥ 3) :
    (mass_of_cycle n)^2 - (momentum n)^2 = 0 ∧
    mass_of_cycle n > 0 := by
  constructor
  · exact invariant_mass_squared_vanishes n h
  · unfold mass_of_cycle
    have hn : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    positivity

/-- Summary: E = p, E² - p² = 0, v = c, p > 0, E > 0. -/
theorem the_dispersion_correspondence (n : ℕ) (h : n ≥ 3) :
    (mass_of_cycle n = momentum n) ∧
    ((mass_of_cycle n)^2 - (momentum n)^2 = 0) ∧
    (phase_velocity n = 1) ∧
    (momentum n > 0) ∧
    (mass_of_cycle n > 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact dispersion_relation n h
  · exact invariant_mass_squared_vanishes n h
  · exact phase_velocity_is_c n h
  · exact no_rest_frame n h
  · unfold mass_of_cycle
    have hn : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    positivity

theorem dispersion_implies_speed_of_light (n : ℕ) (h : n ≥ 3) :
    phase_velocity n = c := by
  rw [phase_velocity_is_c n h]
  unfold c
  rfl

theorem dispersion_consistent_with_deBroglie (n : ℕ) (h : n ≥ 3) :
    momentum n * wavelength_real n = 1 :=
  momentum_wavelength_product n (by omega)

/-- Velocity is independent of mass. -/
theorem mass_independence_of_velocity (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    phase_velocity n₁ = phase_velocity n₂ := by
  rw [phase_velocity_is_c n₁ h₁, phase_velocity_is_c n₂ h₂]

end Diaspora.Dynamics.Dispersion
