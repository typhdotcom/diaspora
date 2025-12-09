import Diaspora.Dynamics.DeBroglie
import Diaspora.Dynamics.EnergyTime
import Diaspora.Dynamics.BoundStates

/-!
# Gravitational Time Dilation

Binding reduces effective mass, which increases period: bound systems tick slower.
-/

namespace Diaspora.Dynamics.TimeDilation

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.EnergyTime

/-! ## Effective Period of Bound Systems -/

/-- T_eff = 1/m_eff for bound systems. -/
noncomputable def effective_period_bound (n₁ n₂ k : ℕ) : ℝ :=
  1 / effective_mass_bound n₁ n₂ k

/-- T_eff = λ_eff since c = 1. -/
theorem effective_period_eq_wavelength (n₁ n₂ k : ℕ) :
    effective_period_bound n₁ n₂ k = effective_wavelength_bound n₁ n₂ k := rfl

/-- T_ref = 1/(m₁ + m₂), the period without binding. -/
noncomputable def reference_period (n₁ n₂ : ℕ) : ℝ :=
  1 / (mass_of_cycle n₁ + mass_of_cycle n₂)

/-- The reference period when k = 0 (no binding). -/
theorem reference_period_at_zero (n₁ n₂ : ℕ) :
    effective_period_bound n₁ n₂ 0 = reference_period n₁ n₂ := by
  unfold effective_period_bound effective_mass_bound reference_period
  unfold sharing_energy_reduction
  simp

/-! ## Binding Slows Clocks -/

/-- Stronger binding increases the effective period: k₁ < k₂ → T_eff(k₁) < T_eff(k₂). -/
theorem binding_slows_clocks (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    ∀ k₁ k₂ : ℕ,
      k₁ < k₂ →
      (h_mass₁ : effective_mass_bound n₁ n₂ k₁ > 0) →
      (h_mass₂ : effective_mass_bound n₁ n₂ k₂ > 0) →
      effective_period_bound n₁ n₂ k₁ < effective_period_bound n₁ n₂ k₂ := by
  intro k₁ k₂ h_lt h_mass₁ h_mass₂
  -- Use the fact that effective_period = effective_wavelength
  rw [effective_period_eq_wavelength, effective_period_eq_wavelength]
  exact binding_increases_wavelength n₁ n₂ h₁ h₂ k₁ k₂ h_lt h_mass₁ h_mass₂

/-! ## Time Dilation Factor -/

/-- γ = T_eff / T_ref. -/
noncomputable def time_dilation_factor (n₁ n₂ k : ℕ) : ℝ :=
  effective_period_bound n₁ n₂ k / reference_period n₁ n₂

/-- The time dilation factor equals the mass ratio. -/
theorem time_dilation_is_mass_ratio (n₁ n₂ k : ℕ)
    (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3)
    (h_mass : effective_mass_bound n₁ n₂ k > 0)
    (h_ref : mass_of_cycle n₁ + mass_of_cycle n₂ > 0) :
    time_dilation_factor n₁ n₂ k =
      (mass_of_cycle n₁ + mass_of_cycle n₂) / effective_mass_bound n₁ n₂ k := by
  unfold time_dilation_factor effective_period_bound reference_period
  have h_mass' : effective_mass_bound n₁ n₂ k ≠ 0 := ne_of_gt h_mass
  have h_ref' : mass_of_cycle n₁ + mass_of_cycle n₂ ≠ 0 := ne_of_gt h_ref
  field_simp [h_mass', h_ref']

/-- When k = 0, the time dilation factor is 1. -/
theorem no_dilation_at_zero (n₁ n₂ : ℕ) (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3)
    (h_ref : mass_of_cycle n₁ + mass_of_cycle n₂ > 0) :
    time_dilation_factor n₁ n₂ 0 = 1 := by
  unfold time_dilation_factor
  rw [reference_period_at_zero]
  have h_ref' : reference_period n₁ n₂ ≠ 0 := by
    unfold reference_period
    exact one_div_ne_zero (ne_of_gt h_ref)
  field_simp [h_ref']

/-- More binding → larger dilation factor. -/
theorem dilation_increases_with_binding (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3)
    (h_ref : mass_of_cycle n₁ + mass_of_cycle n₂ > 0) :
    ∀ k₁ k₂ : ℕ,
      k₁ < k₂ →
      (h_mass₁ : effective_mass_bound n₁ n₂ k₁ > 0) →
      (h_mass₂ : effective_mass_bound n₁ n₂ k₂ > 0) →
      time_dilation_factor n₁ n₂ k₁ < time_dilation_factor n₁ n₂ k₂ := by
  intro k₁ k₂ h_lt h_mass₁ h_mass₂
  unfold time_dilation_factor
  have h_period_lt := binding_slows_clocks n₁ n₂ h₁ h₂ k₁ k₂ h_lt h_mass₁ h_mass₂
  have h_ref' : reference_period n₁ n₂ > 0 := by
    unfold reference_period
    exact one_div_pos.mpr h_ref
  exact div_lt_div_of_pos_right h_period_lt h_ref'

/-! ## Gravitational Redshift -/

/-- f_eff = m_eff. -/
noncomputable def effective_frequency_bound (n₁ n₂ k : ℕ) : ℝ :=
  effective_mass_bound n₁ n₂ k

/-- f_ref = m₁ + m₂. -/
noncomputable def reference_frequency (n₁ n₂ : ℕ) : ℝ :=
  mass_of_cycle n₁ + mass_of_cycle n₂

/-- z = f_eff / f_ref. -/
noncomputable def redshift_factor (n₁ n₂ k : ℕ) : ℝ :=
  effective_frequency_bound n₁ n₂ k / reference_frequency n₁ n₂

/-- Redshift factor is the reciprocal of time dilation factor. -/
theorem redshift_times_dilation (n₁ n₂ k : ℕ)
    (h_mass : effective_mass_bound n₁ n₂ k > 0)
    (h_ref : mass_of_cycle n₁ + mass_of_cycle n₂ > 0) :
    redshift_factor n₁ n₂ k * time_dilation_factor n₁ n₂ k = 1 := by
  unfold redshift_factor time_dilation_factor effective_frequency_bound
  unfold effective_period_bound reference_period reference_frequency
  have h_mass' : effective_mass_bound n₁ n₂ k ≠ 0 := ne_of_gt h_mass
  have h_ref' : mass_of_cycle n₁ + mass_of_cycle n₂ ≠ 0 := ne_of_gt h_ref
  field_simp [h_mass', h_ref']

/-- When k = 0, the redshift factor is 1. -/
theorem no_redshift_at_zero (n₁ n₂ : ℕ) (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3)
    (h_ref : mass_of_cycle n₁ + mass_of_cycle n₂ > 0) :
    redshift_factor n₁ n₂ 0 = 1 := by
  unfold redshift_factor effective_frequency_bound effective_mass_bound
  unfold reference_frequency sharing_energy_reduction
  simp
  have h_ref' : mass_of_cycle n₁ + mass_of_cycle n₂ ≠ 0 := ne_of_gt h_ref
  field_simp [h_ref']

/-- More binding → smaller redshift factor. -/
theorem redshift_increases_with_binding (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3)
    (h_ref : mass_of_cycle n₁ + mass_of_cycle n₂ > 0) :
    ∀ k₁ k₂ : ℕ,
      k₁ < k₂ →
      redshift_factor n₁ n₂ k₂ < redshift_factor n₁ n₂ k₁ := by
  intro k₁ k₂ h_lt
  unfold redshift_factor effective_frequency_bound effective_mass_bound
  unfold reference_frequency sharing_energy_reduction
  have h_n₁ : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_n₂ : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_prod : (n₁ : ℝ) * n₂ > 0 := mul_pos h_n₁ h_n₂
  have h_k_lt : (k₁ : ℝ) < k₂ := Nat.cast_lt.mpr h_lt
  -- Higher k means more binding means lower effective mass
  have h_reduction_lt : 2 * (k₁ : ℝ) / (n₁ * n₂) < 2 * (k₂ : ℝ) / (n₁ * n₂) := by
    apply div_lt_div_of_pos_right _ h_prod
    linarith
  have h_ref' : mass_of_cycle n₁ + mass_of_cycle n₂ ≠ 0 := ne_of_gt h_ref
  apply div_lt_div_of_pos_right _ h_ref
  -- m₁ + m₂ - (2k₂/(n₁n₂)) < m₁ + m₂ - (2k₁/(n₁n₂))
  linarith

/-! ## The Schwarzschild Limit -/

/-- At complete overlap (k = n), effective mass is zero. -/
theorem schwarzschild_time_freeze (n : ℕ) (h : n ≥ 3) :
    effective_mass_bound n n n = 0 :=
  annihilation_infinite_wavelength n h

/-- At the Schwarzschild limit, the redshift factor is zero. -/
theorem schwarzschild_infinite_redshift (n : ℕ) (h : n ≥ 3) :
    redshift_factor n n n = 0 := by
  unfold redshift_factor effective_frequency_bound
  rw [schwarzschild_time_freeze n h]
  simp

/-! ## The Time Dilation Correspondence -/

/-- Summary of key relationships. -/
theorem the_time_dilation_correspondence (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    -- 1. No binding → no dilation
    (mass_of_cycle n₁ + mass_of_cycle n₂ > 0 →
      time_dilation_factor n₁ n₂ 0 = 1) ∧
    -- 2. No binding → no redshift
    (mass_of_cycle n₁ + mass_of_cycle n₂ > 0 →
      redshift_factor n₁ n₂ 0 = 1) ∧
    -- 3. Period equals wavelength (spacetime symmetry)
    (∀ k : ℕ, effective_period_bound n₁ n₂ k = effective_wavelength_bound n₁ n₂ k) ∧
    -- 4. Schwarzschild freeze for equal masses
    (n₁ = n₂ → effective_mass_bound n₁ n₂ n₁ = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact no_dilation_at_zero n₁ n₂ h₁ h₂
  · exact no_redshift_at_zero n₁ n₂ h₁ h₂
  · intro k; exact effective_period_eq_wavelength n₁ n₂ k
  · intro h_eq
    rw [h_eq]
    exact schwarzschild_time_freeze n₂ h₂

/-! ## Potential Form -/

/-- γ = 1 / (1 - binding/m_ref). -/
theorem time_dilation_potential_form (n₁ n₂ k : ℕ)
    (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3)
    (h_ref : mass_of_cycle n₁ + mass_of_cycle n₂ > 0)
    (h_mass : effective_mass_bound n₁ n₂ k > 0) :
    time_dilation_factor n₁ n₂ k =
      1 / (1 - sharing_energy_reduction n₁ n₂ k / (mass_of_cycle n₁ + mass_of_cycle n₂)) := by
  rw [time_dilation_is_mass_ratio n₁ n₂ k h₁ h₂ h_mass h_ref]
  unfold effective_mass_bound
  have h_ref' : mass_of_cycle n₁ + mass_of_cycle n₂ ≠ 0 := ne_of_gt h_ref
  field_simp [h_ref']

/-- At k = 0, γ = 1; for k > 0, γ > 1. -/
theorem weak_field_dilation (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    time_dilation_factor n₁ n₂ 0 = 1 ∧
    ∀ k : ℕ, k > 0 →
      effective_mass_bound n₁ n₂ k > 0 →
      mass_of_cycle n₁ + mass_of_cycle n₂ > 0 →
      time_dilation_factor n₁ n₂ k > 1 := by
  constructor
  · have h_ref : mass_of_cycle n₁ + mass_of_cycle n₂ > 0 := by
      unfold mass_of_cycle
      have h_n₁ : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
      have h_n₂ : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
      positivity
    exact no_dilation_at_zero n₁ n₂ h₁ h₂ h_ref
  · intro k hk h_mass h_ref
    rw [time_dilation_is_mass_ratio n₁ n₂ k h₁ h₂ h_mass h_ref]
    -- γ = m_ref / m_eff > 1 when m_eff < m_ref
    have h_eff_lt : effective_mass_bound n₁ n₂ k < mass_of_cycle n₁ + mass_of_cycle n₂ := by
      unfold effective_mass_bound sharing_energy_reduction
      have h_n₁ : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
      have h_n₂ : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
      have h_prod : (n₁ : ℝ) * n₂ > 0 := mul_pos h_n₁ h_n₂
      have h_k_pos : (k : ℝ) > 0 := Nat.cast_pos.mpr hk
      have h_reduction_pos : 2 * (k : ℝ) / (n₁ * n₂) > 0 := by positivity
      linarith
    exact (one_lt_div h_mass).mpr h_eff_lt

end Diaspora.Dynamics.TimeDilation
