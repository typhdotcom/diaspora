import Diaspora.Dynamics.InvariantMass

/-!
# Velocity of Bound States: From Light to Matter

Opposite-direction cycle pairs have v = |n₂ - n₁|/(n₂ + n₁) < 1.
Equal masses give v = 0; the Lorentz factor satisfies γ² = 1/(1 - v²).
-/

namespace Diaspora.Dynamics.Velocity

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.Dispersion
open Diaspora.Dynamics.InvariantMass

/-! ## Opposite-Direction Pair Velocity -/

/-- v = |n₂ - n₁|/(n₂ + n₁). -/
noncomputable def opposite_pair_velocity (n₁ n₂ : ℕ) : ℝ :=
  |(n₂ : ℝ) - n₁| / (n₂ + n₁)

/-! ## The Subluminal Theorem -/

/-- Opposite-direction pairs have v < 1. -/
theorem opposite_direction_subluminal (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    opposite_pair_velocity n₁ n₂ < 1 := by
  unfold opposite_pair_velocity
  have hn₁_pos : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂_pos : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_sum_pos : (n₂ : ℝ) + n₁ > 0 := by linarith
  have h_abs_lt : |(n₂ : ℝ) - n₁| < n₂ + n₁ := by
    rw [abs_sub_lt_iff]
    constructor <;> linarith
  rw [div_lt_one h_sum_pos]
  exact h_abs_lt

/-- Velocity is non-negative for opposite-direction pairs. -/
theorem opposite_direction_velocity_nonneg (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    opposite_pair_velocity n₁ n₂ ≥ 0 := by
  unfold opposite_pair_velocity
  have hn₁_pos : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂_pos : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  apply div_nonneg (abs_nonneg _)
  linarith

/-! ## Equal Masses: The Rest Frame -/

/-- When n₁ = n₂, v = 0. -/
theorem equal_masses_at_rest (n : ℕ) (_h : n ≥ 3) :
    opposite_pair_velocity n n = 0 := by
  unfold opposite_pair_velocity
  simp [sub_self, abs_zero, zero_div]

/-- Only equal masses give zero velocity. -/
theorem zero_velocity_iff_equal (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    opposite_pair_velocity n₁ n₂ = 0 ↔ n₁ = n₂ := by
  unfold opposite_pair_velocity
  have hn₁_pos : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂_pos : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_sum_pos : (n₂ : ℝ) + n₁ > 0 := by linarith
  rw [div_eq_zero_iff]
  constructor
  · intro h
    cases h with
    | inl h_abs =>
      rw [abs_eq_zero, sub_eq_zero] at h_abs
      exact Nat.cast_injective h_abs.symm
    | inr h_sum =>
      linarith
  · intro h_eq
    left
    rw [h_eq, sub_self, abs_zero]

/-! ## Velocity Symmetry -/

/-- Velocity is symmetric in the cycle lengths. -/
theorem opposite_pair_velocity_symm (n₁ n₂ : ℕ) :
    opposite_pair_velocity n₁ n₂ = opposite_pair_velocity n₂ n₁ := by
  unfold opposite_pair_velocity
  rw [abs_sub_comm]
  ring_nf

/-! ## The Lorentz Factor -/

/-- γ = (n₁ + n₂) / (2√(n₁n₂)). -/
noncomputable def lorentz_factor (n₁ n₂ : ℕ) : ℝ :=
  (n₁ + n₂ : ℝ) / (2 * Real.sqrt (n₁ * n₂))

/-- Equal masses have γ = 1 (at rest). -/
theorem lorentz_factor_equal_masses (n : ℕ) (h : n ≥ 3) :
    lorentz_factor n n = 1 := by
  unfold lorentz_factor
  have hn_pos : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_nn : (n : ℝ) * n = n^2 := by ring
  rw [h_nn, Real.sqrt_sq (le_of_lt hn_pos)]
  have h_ne : (n : ℝ) + n ≠ 0 := by linarith
  field_simp [h_ne]
  ring

/-- The Lorentz factor is at least 1 (by AM-GM). -/
theorem lorentz_factor_ge_one (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    lorentz_factor n₁ n₂ ≥ 1 := by
  unfold lorentz_factor
  have hn₁_pos : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂_pos : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_prod_pos : (n₁ : ℝ) * n₂ > 0 := mul_pos hn₁_pos hn₂_pos
  have h_sqrt_pos : Real.sqrt (n₁ * n₂) > 0 := Real.sqrt_pos.mpr h_prod_pos
  have h_denom_pos : 2 * Real.sqrt (n₁ * n₂) > 0 := by linarith
  have h_sqrt_n₁ : Real.sqrt n₁ ^ 2 = n₁ := Real.sq_sqrt (le_of_lt hn₁_pos)
  have h_sqrt_n₂ : Real.sqrt n₂ ^ 2 = n₂ := Real.sq_sqrt (le_of_lt hn₂_pos)
  have h_sqrt_prod : Real.sqrt (n₁ * n₂) = Real.sqrt n₁ * Real.sqrt n₂ :=
    Real.sqrt_mul (le_of_lt hn₁_pos) n₂
  have h_am_gm : (n₁ : ℝ) + n₂ ≥ 2 * Real.sqrt (n₁ * n₂) := by
    have h_sq_nonneg : (Real.sqrt n₁ - Real.sqrt n₂) ^ 2 ≥ 0 := sq_nonneg _
    calc (n₁ : ℝ) + n₂
        = Real.sqrt n₁ ^ 2 + Real.sqrt n₂ ^ 2 := by rw [h_sqrt_n₁, h_sqrt_n₂]
      _ = (Real.sqrt n₁ - Real.sqrt n₂) ^ 2 + 2 * (Real.sqrt n₁ * Real.sqrt n₂) := by ring
      _ ≥ 0 + 2 * (Real.sqrt n₁ * Real.sqrt n₂) := by linarith
      _ = 2 * Real.sqrt (n₁ * n₂) := by rw [zero_add, h_sqrt_prod]
  rw [ge_iff_le, one_le_div h_denom_pos]
  exact h_am_gm

/-- γ² = 1/(1 - v²). -/
theorem relativistic_identity (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    (lorentz_factor n₁ n₂)^2 = 1 / (1 - (opposite_pair_velocity n₁ n₂)^2) := by
  unfold opposite_pair_velocity lorentz_factor
  have hn₁_pos : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂_pos : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_sum_pos : (n₂ : ℝ) + n₁ > 0 := by linarith
  have h_prod_pos : (n₁ : ℝ) * n₂ > 0 := mul_pos hn₁_pos hn₂_pos
  have h_sqrt_pos : Real.sqrt (n₁ * n₂) > 0 := Real.sqrt_pos.mpr h_prod_pos
  have h_v_sq : (|(n₂ : ℝ) - n₁| / (n₂ + n₁))^2 = (n₂ - n₁)^2 / (n₂ + n₁)^2 := by
    rw [div_pow, sq_abs]
  rw [h_v_sq]
  have h_1_minus_v_sq : 1 - (n₂ - n₁ : ℝ)^2 / (n₂ + n₁)^2 = 4 * n₁ * n₂ / (n₂ + n₁)^2 := by
    have h_sum_sq_ne : (n₂ + n₁ : ℝ)^2 ≠ 0 := by positivity
    field_simp [h_sum_sq_ne]
    ring
  rw [h_1_minus_v_sq]
  have h_gamma_sq : ((n₁ + n₂ : ℝ) / (2 * Real.sqrt (n₁ * n₂)))^2 =
      (n₁ + n₂)^2 / (4 * n₁ * n₂) := by
    rw [div_pow, mul_pow]
    have h_sqrt_sq : Real.sqrt (n₁ * n₂)^2 = n₁ * n₂ :=
      Real.sq_sqrt (le_of_lt h_prod_pos)
    rw [h_sqrt_sq]
    ring
  rw [h_gamma_sq]
  rw [one_div, inv_div]
  congr 1
  ring

/-! ## Velocity from Energy and Momentum -/

/-- The velocity equals |p|/E using the two_cycle definitions. -/
theorem velocity_from_energy_momentum (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    let E := two_cycle_energy n₁ n₂ 0
    let p := two_cycle_momentum n₁ n₂ 1 (-1)
    opposite_pair_velocity n₁ n₂ = |p| / E := by
  simp only
  unfold opposite_pair_velocity two_cycle_energy two_cycle_momentum
  unfold signed_momentum momentum mass_of_cycle
  have hn₁ : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn₂ : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn₁_pos : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂_pos : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_sum_ne : (n₁ : ℝ) + n₂ ≠ 0 := by linarith
  have h_sum_pos : (n₂ : ℝ) + n₁ > 0 := by linarith
  simp only [sub_zero, Int.cast_one, Int.cast_neg, one_mul, neg_mul, one_div]
  have h_rhs_num : ((n₁ : ℝ)⁻¹ + -(n₂ : ℝ)⁻¹) = (n₂ - n₁) / (n₁ * n₂) := by
    field_simp [hn₁, hn₂]; ring
  have h_rhs_denom : ((n₁ : ℝ)⁻¹ + (n₂ : ℝ)⁻¹) = (n₁ + n₂) / (n₁ * n₂) := by
    field_simp [hn₁, hn₂]; ring
  rw [h_rhs_num, h_rhs_denom]
  have h_prod_pos : (n₁ : ℝ) * n₂ > 0 := mul_pos hn₁_pos hn₂_pos
  have h_prod_ne : (n₁ : ℝ) * n₂ ≠ 0 := ne_of_gt h_prod_pos
  rw [abs_div, abs_of_pos h_prod_pos]
  have h_simplify : |(n₂ : ℝ) - n₁| / (n₁ * n₂) / ((n₁ + n₂) / (n₁ * n₂)) =
      |(n₂ : ℝ) - n₁| / (n₁ + n₂) := by
    field_simp [h_prod_ne, h_sum_ne]
  rw [h_simplify]
  congr 1; ring

/-! ## The Velocity Correspondence -/

/-- Collects the key velocity results for equal-mass pairs. -/
theorem the_velocity_correspondence (n : ℕ) (h : n ≥ 3) :
    (opposite_pair_velocity n n < 1) ∧
    (opposite_pair_velocity n n = 0) ∧
    (lorentz_factor n n = 1) ∧
    ((lorentz_factor n n)^2 = 1 / (1 - (opposite_pair_velocity n n)^2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact opposite_direction_subluminal n n h h
  · exact equal_masses_at_rest n h
  · exact lorentz_factor_equal_masses n h
  · exact relativistic_identity n n h h

end Diaspora.Dynamics.Velocity
