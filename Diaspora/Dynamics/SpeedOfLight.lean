import Diaspora.Dynamics.EnergyTime

/-!
# The Speed of Light

c = λ/T = n/n = 1 for all cycles. All defects propagate at the same speed,
regardless of mass or wavelength.
-/

namespace Diaspora.Dynamics.SpeedOfLight

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.EnergyTime

/-! ## The Speed of Light -/

/-- c = λ / T -/
noncomputable def speed_of_light (n : ℕ) : ℝ := wavelength_real n / period n

/-- c = λ/T = n/n = 1 -/
theorem speed_of_light_eq_one (n : ℕ) (h : n > 0) : speed_of_light n = 1 := by
  unfold speed_of_light
  rw [period_eq_n n h]
  unfold wavelength_real
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h)
  field_simp [hn]

theorem speed_is_mass_independent (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    speed_of_light n₁ = speed_of_light n₂ := by
  rw [speed_of_light_eq_one n₁ (by omega), speed_of_light_eq_one n₂ (by omega)]

theorem speed_eq_wavelength_times_frequency (n : ℕ) (h : n > 0) :
    speed_of_light n = wavelength_real n * frequency n := by
  unfold speed_of_light
  rw [period_eq_n n h]
  unfold wavelength_real frequency mass_of_cycle
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h)
  field_simp [hn]

theorem wave_equation (n : ℕ) (h : n > 0) :
    frequency n * wavelength_real n = speed_of_light n := by
  rw [speed_of_light_eq_one n h]
  exact frequency_wavelength_product n h

/-! ## Relativistic Relations -/

/-- E = mc² = m when c = 1 -/
theorem rest_energy_equals_mass (n : ℕ) (h : n ≥ 3) :
    mass_of_cycle n = mass_of_cycle n * (speed_of_light n)^2 := by
  rw [speed_of_light_eq_one n (by omega)]
  ring

theorem energy_momentum_ratio (n : ℕ) (h : n ≥ 3) :
    mass_of_cycle n / momentum n = speed_of_light n := by
  unfold momentum
  have h_pos : mass_of_cycle n > 0 := by
    unfold mass_of_cycle
    have hn : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega : n > 0)
    positivity
  rw [div_self (ne_of_gt h_pos), speed_of_light_eq_one n (by omega)]

/-- E² = p² + m² in rest frame (p = 0) gives E = m -/
theorem relativistic_dispersion_rest_frame (n : ℕ) (h : n ≥ 3) :
    (mass_of_cycle n)^2 = 0^2 + (mass_of_cycle n * speed_of_light n^2)^2 := by
  rw [speed_of_light_eq_one n (by omega)]
  ring

/-! ## Consequences of c = 1 -/

theorem spacetime_symmetry (n : ℕ) (h : n > 0) :
    period n = wavelength_real n := period_equals_wavelength n h

theorem causality_bound (n : ℕ) (h : n > 0) :
    speed_of_light n ≤ 1 := by
  rw [speed_of_light_eq_one n h]

theorem no_superluminal (n : ℕ) (h : n > 0) :
    speed_of_light n = 1 := speed_of_light_eq_one n h

/-! ## The Unity of Constants -/

/-- c = ℏ = 1 in natural units -/
theorem natural_units (n : ℕ) (h : n ≥ 3) :
    speed_of_light n = 1 ∧
    position_uncertainty n * momentum_uncertainty n = 1 ∧
    mass_of_cycle n = mass_of_cycle n ∧
    energy_uncertainty n * time_uncertainty n = 1 := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · exact speed_of_light_eq_one n (by omega)
  · exact heisenberg_uncertainty n (by omega)
  · exact energy_time_uncertainty n (by omega)

/-- Summary: c = 1, f × λ = 1, T = λ -/
theorem the_speed_of_light_correspondence (n : ℕ) (h : n ≥ 3) :
    speed_of_light n = 1 ∧
    frequency n * wavelength_real n = 1 ∧
    period n = wavelength_real n ∧
    (∀ m : ℕ, m ≥ 3 → speed_of_light m = speed_of_light n) ∧
    frequency n * period n = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact speed_of_light_eq_one n (by omega)
  · exact frequency_wavelength_product n (by omega)
  · exact spacetime_symmetry n (by omega)
  · intro m hm; exact speed_is_mass_independent m n hm h
  · exact frequency_period_product n (by omega)

end Diaspora.Dynamics.SpeedOfLight
