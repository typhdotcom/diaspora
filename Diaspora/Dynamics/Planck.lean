import Diaspora.Dynamics.AngularMomentum

/-!
# Planck Units and the Discrete Cutoff

Derives Planck scale from c = 1, ℏ = 1, G = 2 and shows the discrete structure
provides a sub-Planckian cutoff: m_max = 1/3 < m_P = 1/√2.
-/

namespace Diaspora.Dynamics.Planck

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.Action
open Diaspora.Dynamics.SpeedOfLight
open Diaspora.Dynamics.EnergyTime
open Diaspora.Dynamics.DeBroglie

/-! ## Fundamental Constants -/

/-- Speed of light: c = 1 -/
noncomputable def c : ℝ := 1

/-- Reduced Planck constant: ℏ = 1 -/
noncomputable def hbar : ℝ := 1

/-- Gravitational constant: G = 2 (from F = 2m₁m₂) -/
noncomputable def G : ℝ := 2

theorem c_eq_one : c = 1 := rfl

theorem hbar_eq_one : hbar = planck_constant := by
  rw [planck_constant_eq_one]
  rfl

theorem G_eq_two : G = 2 := rfl

/-! ## Planck Units -/

/-- Planck mass: m_P = √(ℏc/G) = √(1/2) -/
noncomputable def planck_mass : ℝ := Real.sqrt (hbar * c / G)

/-- Planck length: l_P = √(ℏG/c³) = √2 -/
noncomputable def planck_length : ℝ := Real.sqrt (hbar * G / c^3)

/-- Planck time: t_P = √(ℏG/c⁵) = √2 -/
noncomputable def planck_time : ℝ := Real.sqrt (hbar * G / c^5)

/-- Planck energy: E_P = √(ℏc⁵/G) = √(1/2) -/
noncomputable def planck_energy : ℝ := Real.sqrt (hbar * c^5 / G)

/-! ## Explicit Values -/

theorem planck_mass_sq : planck_mass ^ 2 = 1 / 2 := by
  unfold planck_mass hbar c G
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 * 1 / 2)]
  ring

theorem planck_length_sq : planck_length ^ 2 = 2 := by
  unfold planck_length hbar c G
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 * 2 / 1 ^ 3)]
  ring

theorem planck_length_value : planck_length = Real.sqrt 2 := by
  unfold planck_length hbar c G
  simp only [one_mul, one_pow, div_one]

theorem planck_time_value : planck_time = Real.sqrt 2 := by
  unfold planck_time hbar c G
  simp only [one_mul, one_pow, div_one]

theorem planck_time_eq_length : planck_time = planck_length := by
  rw [planck_time_value, planck_length_value]

/-! ## Dimensional Relations -/

theorem planck_mass_length_sq_product : planck_mass^2 * planck_length^2 = hbar^2 / c^2 := by
  rw [planck_mass_sq, planck_length_sq]
  unfold hbar c
  ring

theorem planck_energy_time_sq_product : planck_energy^2 * planck_time^2 = hbar^2 := by
  unfold planck_energy planck_time hbar c G
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 * 1 ^ 5 / 2)]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 * 2 / 1 ^ 5)]
  ring

/-! ## The Discrete Cutoff -/

def min_cycle_length : ℕ := 3

theorem max_mass_is_triangle : mass_of_cycle min_cycle_length = 1/3 := by
  unfold mass_of_cycle min_cycle_length
  norm_num

noncomputable def max_mass : ℝ := mass_of_cycle min_cycle_length

theorem max_mass_value : max_mass = 1/3 := max_mass_is_triangle

theorem min_wavelength_is_three : DeBroglie.wavelength min_cycle_length = 3 := rfl

theorem min_period_is_three :
    EnergyTime.period min_cycle_length = 3 := by
  rw [period_eq_n min_cycle_length (by decide : min_cycle_length > 0)]
  rfl

/-! ## The Sub-Planckian Bound -/

/-- (m_max / m_P)² = 2/9 -/
theorem mass_ratio_sq : max_mass^2 / planck_mass^2 = 2/9 := by
  rw [max_mass_value, planck_mass_sq]
  ring

theorem sub_planckian_bound_sq : max_mass^2 < planck_mass^2 := by
  rw [max_mass_value, planck_mass_sq]
  norm_num

/-- m_max = 1/3 < m_P = 1/√2 -/
theorem sub_planckian_bound : max_mass < planck_mass := by
  have h_max_pos : max_mass > 0 := by rw [max_mass_value]; norm_num
  have h_planck_pos : planck_mass > 0 := by
    unfold planck_mass hbar c G
    exact Real.sqrt_pos.mpr (by norm_num)
  have h_sq := sub_planckian_bound_sq
  rw [sq_lt_sq] at h_sq
  rw [abs_of_pos h_max_pos, abs_of_pos h_planck_pos] at h_sq
  exact h_sq

/-- λ_min = 3 > l_P = √2 -/
theorem wavelength_exceeds_planck : (min_cycle_length : ℝ) > planck_length := by
  rw [planck_length_value]
  have h : (Real.sqrt 2)^2 < (min_cycle_length : ℝ)^2 := by
    simp only [min_cycle_length, Nat.cast_ofNat, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h_sqrt_pos : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
  have h_min_pos : (min_cycle_length : ℝ) > 0 := by simp [min_cycle_length]
  rw [sq_lt_sq] at h
  rw [abs_of_pos h_sqrt_pos, abs_of_pos h_min_pos] at h
  exact h

/-! ## The Planck Correspondence -/

/-- Summary: c = 1, ℏ = 1, G = 2, m_max < m_P, λ_min > l_P -/
theorem the_planck_correspondence :
    c = 1 ∧ hbar = 1 ∧ G = 2 ∧
    planck_mass ^ 2 = 1 / 2 ∧ planck_length ^ 2 = 2 ∧
    max_mass = 1/3 ∧ max_mass < planck_mass ∧
    (min_cycle_length : ℝ) > planck_length := by
  exact ⟨rfl, rfl, rfl, planck_mass_sq, planck_length_sq, max_mass_value,
         sub_planckian_bound, wavelength_exceeds_planck⟩

/-! ## Density Bounds -/

theorem planck_density_sq : planck_mass^2 / planck_length^6 = 1/16 := by
  have h_mass : planck_mass^2 = 1/2 := planck_mass_sq
  have h_len : planck_length^2 = 2 := planck_length_sq
  have h_len6 : planck_length^6 = (planck_length^2)^3 := by ring
  rw [h_len6, h_len, h_mass]
  norm_num

theorem max_density_sq : max_mass^2 / (min_cycle_length : ℝ)^6 = 1/6561 := by
  rw [max_mass_value]
  simp [min_cycle_length]
  ring

theorem density_bound : max_mass^2 / (min_cycle_length : ℝ)^6 < planck_mass^2 / planck_length^6 := by
  rw [max_density_sq, planck_density_sq]
  norm_num

/-! ## The Triangle as Fundamental Scale -/

theorem triangle_sets_all_bounds :
    mass_of_cycle 3 = 1/3 ∧
    DeBroglie.wavelength 3 = 3 ∧
    EnergyTime.period 3 = 3 ∧
    DeBroglie.frequency 3 = 1/3 := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · unfold mass_of_cycle; norm_num
  · rw [period_eq_n 3 (by decide : (3 : ℕ) > 0)]; rfl
  · unfold DeBroglie.frequency mass_of_cycle; norm_num

theorem fine_structure_of_diaspora : max_mass^2 / planck_mass^2 = 2/9 :=
  mass_ratio_sq

end Diaspora.Dynamics.Planck
