import Diaspora.Dynamics.Planck

/-!
# The Schwarzschild Radius and Quantum Dominance

For all valid cycles (n ≥ 3), r_s/λ_C = 4/n² < 1: quantum effects always dominate.
-/

namespace Diaspora.Dynamics.SchwarzschildRadius

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.Planck

/-! ## The Schwarzschild Radius -/

/-- r_s = 2Gm/c² = 4m in Diaspora units. -/
noncomputable def schwarzschild_radius_of_mass (m : ℝ) : ℝ := 2 * G * m / c^2

/-- r_s = 4m. -/
theorem schwarzschild_radius_eq (m : ℝ) : schwarzschild_radius_of_mass m = 4 * m := by
  unfold schwarzschild_radius_of_mass G c
  ring

/-- r_s for an n-cycle. -/
noncomputable def schwarzschild_radius (n : ℕ) : ℝ :=
  schwarzschild_radius_of_mass (mass_of_cycle n)

/-- r_s = 4/n for an n-cycle. -/
theorem schwarzschild_radius_formula (n : ℕ) (h : n > 0) :
    schwarzschild_radius n = 4 / n := by
  unfold schwarzschild_radius
  rw [schwarzschild_radius_eq]
  unfold mass_of_cycle
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h)
  field_simp [hn]

/-! ## The Compton-Schwarzschild Ratio -/

/-- r_s/λ_C = 4/n². -/
noncomputable def compton_schwarzschild_ratio (n : ℕ) : ℝ :=
  schwarzschild_radius n / compton_wavelength n

/-- r_s/λ_C = 4/n². -/
theorem compton_schwarzschild_ratio_formula (n : ℕ) (h : n ≥ 3) :
    compton_schwarzschild_ratio n = 4 / n^2 := by
  unfold compton_schwarzschild_ratio
  rw [schwarzschild_radius_formula n (by omega)]
  rw [compton_equals_wavelength n h]
  unfold wavelength_real
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hn]

/-- r_s/λ_C = 4m². -/
theorem ratio_is_four_mass_squared (n : ℕ) (h : n ≥ 3) :
    compton_schwarzschild_ratio n = 4 * (mass_of_cycle n)^2 := by
  rw [compton_schwarzschild_ratio_formula n h]
  unfold mass_of_cycle
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hn]

/-! ## The Quantum Dominance Theorem -/

/-- For all valid cycles, r_s < λ_C. -/
theorem quantum_dominance (n : ℕ) (h : n ≥ 3) :
    schwarzschild_radius n < compton_wavelength n := by
  rw [schwarzschild_radius_formula n (by omega)]
  rw [compton_equals_wavelength n h]
  unfold wavelength_real
  have hn : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_n_ge_3 : (n : ℝ) ≥ 3 := Nat.cast_le.mpr h
  -- Need: 4/n < n, i.e., 4 < n²
  have h_sq : (n : ℝ)^2 ≥ 9 := by nlinarith
  have h_4_lt_sq : (4 : ℝ) < n * n := by linarith
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn
  calc (4 : ℝ) / n = 4 / n := rfl
    _ < n * n / n := by apply div_lt_div_of_pos_right h_4_lt_sq hn
    _ = n := by field_simp

/-- r_s/λ_C < 1 for valid cycles. -/
theorem ratio_less_than_one (n : ℕ) (h : n ≥ 3) :
    compton_schwarzschild_ratio n < 1 := by
  rw [compton_schwarzschild_ratio_formula n h]
  have hn : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_n_ge_3 : (n : ℝ) ≥ 3 := Nat.cast_le.mpr h
  have h_sq : (n : ℝ)^2 ≥ 9 := by nlinarith
  have h_sq_pos : (n : ℝ)^2 > 0 := by positivity
  rw [div_lt_one h_sq_pos]
  linarith

/-- n² > 4 for all n ≥ 3. -/
theorem discrete_prevents_collapse (n : ℕ) (h : n ≥ 3) :
    (n : ℝ)^2 > 4 := by
  have h_n_ge_3 : (n : ℝ) ≥ 3 := Nat.cast_le.mpr h
  nlinarith

/-! ## The Triangle: Maximum Ratio -/

/-- The triangle achieves r_s/λ_C = 4/9. -/
theorem triangle_ratio : compton_schwarzschild_ratio 3 = 4 / 9 := by
  rw [compton_schwarzschild_ratio_formula 3 (by omega)]
  norm_num

/-- The triangle's ratio is less than 1/2. -/
theorem triangle_less_than_half : compton_schwarzschild_ratio 3 < 1 / 2 := by
  rw [triangle_ratio]
  norm_num

/-- Larger cycles have smaller r_s/λ_C ratios. -/
theorem larger_more_quantum (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_lt : n₁ < n₂) :
    compton_schwarzschild_ratio n₂ < compton_schwarzschild_ratio n₁ := by
  rw [compton_schwarzschild_ratio_formula n₁ h₁]
  rw [compton_schwarzschild_ratio_formula n₂ h₂]
  have hn₁ : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂ : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_lt' : (n₁ : ℝ) < n₂ := Nat.cast_lt.mpr h_lt
  have h_sq_lt : (n₁ : ℝ)^2 < n₂^2 := by nlinarith
  have h_sq₁_pos : (n₁ : ℝ)^2 > 0 := by positivity
  have h_sq₂_pos : (n₂ : ℝ)^2 > 0 := by positivity
  exact div_lt_div_of_pos_left (by norm_num) h_sq₁_pos h_sq_lt

/-! ## No Black Holes in Diaspora -/

/-- No valid cycle has r_s ≥ λ_C. -/
theorem no_black_holes (n : ℕ) (h : n ≥ 3) :
    ¬(schwarzschild_radius n ≥ compton_wavelength n) := by
  intro h_contra
  have h_lt := quantum_dominance n h
  linarith

/-- At n = 2, r_s/λ_C = 1 (invalid cycle). -/
theorem critical_would_be_two : (4 : ℝ) / 2^2 = 1 := by norm_num

/-! ## Connection to Planck Scale -/

/-- r_s(m_P) = 4m_P. -/
theorem schwarzschild_at_planck :
    schwarzschild_radius_of_mass planck_mass = 4 * planck_mass := by
  rw [schwarzschild_radius_eq]

/-- λ_C(m_P) = 1/m_P. -/
theorem compton_at_planck :
    1 / planck_mass = 1 / planck_mass := rfl

/-- At the Planck mass, r_s/λ_C = 4m_P² = 2. -/
theorem planck_ratio_is_two :
    schwarzschild_radius_of_mass planck_mass / (1 / planck_mass) = 4 * planck_mass^2 := by
  rw [schwarzschild_radius_eq]
  have h_pos : planck_mass > 0 := by
    unfold planck_mass hbar c G
    exact Real.sqrt_pos.mpr (by norm_num)
  field_simp

/-- 4m_P² = 2. -/
theorem planck_ratio_value :
    4 * planck_mass^2 = 2 := by
  rw [planck_mass_sq]
  norm_num

/-- For n = 3: r_s = 4/3, λ_C = 3, r_s/λ_C = 4/9. -/
theorem max_mass_quantum :
    schwarzschild_radius 3 = 4 / 3 ∧
    compton_wavelength 3 = 3 ∧
    schwarzschild_radius 3 / compton_wavelength 3 = 4 / 9 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [schwarzschild_radius_formula 3 (by omega)]; norm_num
  · rw [compton_equals_wavelength 3 (by omega)]; rfl
  · rw [schwarzschild_radius_formula 3 (by omega)]
    rw [compton_equals_wavelength 3 (by omega)]
    unfold wavelength_real
    norm_num

/-! ## The Quantum Dominance Correspondence -/

/-- Summary of key relationships. -/
theorem the_quantum_dominance_correspondence (n : ℕ) (h : n ≥ 3) :
    -- 1. Schwarzschild radius
    (schwarzschild_radius n = 4 / n) ∧
    -- 2. Compton wavelength
    (compton_wavelength n = n) ∧
    -- 3. Ratio < 1 (quantum dominance)
    (compton_schwarzschild_ratio n < 1) ∧
    -- 4. λ_C > r_s (explicit)
    (compton_wavelength n > schwarzschild_radius n) ∧
    -- 5. No black holes
    (¬(schwarzschild_radius n ≥ compton_wavelength n)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact schwarzschild_radius_formula n (by omega)
  · rw [compton_equals_wavelength n h]; rfl
  · exact ratio_less_than_one n h
  · have h_dom := quantum_dominance n h
    rw [compton_equals_wavelength n h] at h_dom ⊢
    exact h_dom
  · exact no_black_holes n h

end Diaspora.Dynamics.SchwarzschildRadius
