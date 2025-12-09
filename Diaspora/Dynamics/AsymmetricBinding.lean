import Diaspora.Dynamics.GravitationalInteraction

/-!
# Asymmetric Binding: Unequal Masses and Schwarzschild Limits

Bounds on gravitational binding for cycles of unequal size.

## Main Results

- `max_opposite_edges_bound`: For cycles n₁ ≤ n₂, at most n₁ edges shared
- `max_binding_unequal`: Maximum binding = 2/n₂
- `unequal_no_schwarzschild`: Unequal cycles cannot reach Schwarzschild limit
- `binding_efficiency_formula`: Efficiency = 2n₁/(n₁+n₂)
- `equal_optimal_for_schwarzschild`: Only equal-size cycles achieve efficiency = 1
-/

namespace Diaspora.Dynamics.AsymmetricBinding

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics

variable {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]

/-! ## Maximum Shared Edges for Unequal Cycles -/

omit [Fintype (Fin n)] [NeZero n] in
/-- Maximum opposite-direction shared edges is bounded by cycle length. -/
theorem max_opposite_edges_bound (c₁ c₂ : GeneralCycle n) :
    c₁.oppositeDirectionEdges c₂ ≤ c₁.len := by
  have h := GravitationalInteraction.max_shared_edges c₁ c₂
  omega

/-- Maximum binding energy for cycles of length n₁, n₂. -/
noncomputable def max_binding_energy (n₁ n₂ : ℕ) : ℝ :=
  sharing_energy_reduction n₁ n₂ (min n₁ n₂)

/-- Maximum binding for unequal cycles is 2/n₂. -/
theorem max_binding_unequal (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_le : n₁ ≤ n₂) :
    max_binding_energy n₁ n₂ = 2 / n₂ := by
  unfold max_binding_energy sharing_energy_reduction
  have hn₁ : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : n₁ ≠ 0)
  have hn₂ : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : n₂ ≠ 0)
  have hn₂_pos : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  rw [Nat.min_eq_left h_le]
  field_simp

/-- Maximum binding equals 2 × mass of the lighter cycle. -/
theorem max_binding_is_twice_smaller_mass (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_le : n₁ ≤ n₂) :
    max_binding_energy n₁ n₂ = 2 * mass_of_cycle n₂ := by
  rw [max_binding_unequal n₁ n₂ h₁ h₂ h_le]
  unfold mass_of_cycle
  ring

/-! ## Schwarzschild Impossibility for Unequal Masses -/

/-- Unequal masses cannot reach Schwarzschild limit. -/
theorem unequal_no_schwarzschild (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_lt : n₁ < n₂) :
    max_binding_energy n₁ n₂ < GravitationalStability.total_rest_mass n₁ n₂ := by
  rw [max_binding_unequal n₁ n₂ h₁ h₂ (le_of_lt h_lt)]
  unfold GravitationalStability.total_rest_mass mass_of_cycle
  have hn₁ : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂ : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_lt' : (n₁ : ℝ) < n₂ := Nat.cast_lt.mpr h_lt
  have h_inv : 1 / (n₂ : ℝ) < 1 / n₁ := (one_div_lt_one_div hn₂ hn₁).mpr h_lt'
  have h1 : 2 / (n₂ : ℝ) = 1 / n₂ + 1 / n₂ := by ring
  rw [h1]
  linarith

/-- Schwarzschild deficit: rest_mass - max_binding. -/
noncomputable def schwarzschild_deficit (n₁ n₂ : ℕ) : ℝ :=
  GravitationalStability.total_rest_mass n₁ n₂ - max_binding_energy n₁ n₂

/-- Schwarzschild deficit equals mass difference. -/
theorem schwarzschild_deficit_is_mass_difference (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_le : n₁ ≤ n₂) :
    schwarzschild_deficit n₁ n₂ = mass_of_cycle n₁ - mass_of_cycle n₂ := by
  unfold schwarzschild_deficit GravitationalStability.total_rest_mass
  rw [max_binding_unequal n₁ n₂ h₁ h₂ h_le]
  unfold mass_of_cycle
  ring

/-- Deficit is zero iff masses are equal. -/
theorem schwarzschild_deficit_zero_iff_equal (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_le : n₁ ≤ n₂) :
    schwarzschild_deficit n₁ n₂ = 0 ↔ n₁ = n₂ := by
  rw [schwarzschild_deficit_is_mass_difference n₁ n₂ h₁ h₂ h_le]
  unfold mass_of_cycle
  have hn₁ : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂ : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  constructor
  · intro h
    have h_eq : 1 / (n₁ : ℝ) = 1 / n₂ := by linarith
    have h_eq' : (n₁ : ℝ) = n₂ := eq_of_one_div_eq_one_div h_eq
    exact Nat.cast_injective h_eq'
  · intro h
    rw [h]
    ring

/-! ## Binding Efficiency -/

/-- Binding efficiency: fraction of rest mass convertible to binding. -/
noncomputable def binding_efficiency (n₁ n₂ : ℕ) : ℝ :=
  max_binding_energy n₁ n₂ / GravitationalStability.total_rest_mass n₁ n₂

/-- Efficiency = 2n₁/(n₁+n₂). -/
theorem binding_efficiency_formula (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_le : n₁ ≤ n₂) :
    binding_efficiency n₁ n₂ = 2 * n₁ / (n₁ + n₂) := by
  unfold binding_efficiency
  rw [max_binding_unequal n₁ n₂ h₁ h₂ h_le]
  unfold GravitationalStability.total_rest_mass mass_of_cycle
  have hn₁ : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn₂ : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h_sum : (n₁ : ℝ) + n₂ ≠ 0 := by positivity
  field_simp
  ring

/-- Equal masses achieve perfect efficiency (ratio = 1). -/
theorem equal_mass_perfect_efficiency (m : ℕ) (h : m ≥ 3) :
    binding_efficiency m m = 1 := by
  rw [binding_efficiency_formula m m h h (le_refl m)]
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  ring

/-- Unequal masses have efficiency < 1. -/
theorem unequal_mass_imperfect_efficiency (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_lt : n₁ < n₂) :
    binding_efficiency n₁ n₂ < 1 := by
  rw [binding_efficiency_formula n₁ n₂ h₁ h₂ (le_of_lt h_lt)]
  have hn₁ : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂ : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_lt' : (n₁ : ℝ) < n₂ := Nat.cast_lt.mpr h_lt
  have h_sum_pos : (n₁ : ℝ) + n₂ > 0 := by linarith
  -- Goal: 2n₁/(n₁+n₂) < 1
  -- Equivalent: 2n₁ < n₁ + n₂
  -- Equivalent: n₁ < n₂ ✓
  rw [div_lt_one h_sum_pos]
  linarith

/-- Efficiency is symmetric in n₁, n₂. -/
theorem binding_efficiency_symm (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    binding_efficiency n₁ n₂ = binding_efficiency n₂ n₁ := by
  unfold binding_efficiency max_binding_energy GravitationalStability.total_rest_mass
  unfold sharing_energy_reduction mass_of_cycle
  have hn₁ : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn₂ : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Nat.min_comm]
  have h_prod : (n₁ : ℝ) * n₂ = n₂ * n₁ := mul_comm _ _
  have h_sum : 1 / (n₁ : ℝ) + 1 / n₂ = 1 / n₂ + 1 / n₁ := add_comm _ _
  rw [h_prod, h_sum]

/-! ## Asymmetry Effects -/

/-- Efficiency decreases as mass ratio increases. -/
theorem efficiency_decreases_with_asymmetry (n₁ n₂ n₂' : ℕ)
    (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h₂' : n₂' ≥ 3)
    (h_le : n₁ ≤ n₂) (h_le' : n₁ ≤ n₂') (h_lt : n₂ < n₂') :
    binding_efficiency n₁ n₂ > binding_efficiency n₁ n₂' := by
  rw [binding_efficiency_formula n₁ n₂ h₁ h₂ h_le]
  rw [binding_efficiency_formula n₁ n₂' h₁ h₂' h_le']
  have hn₁ : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂ : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂' : (n₂' : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_lt' : (n₂ : ℝ) < n₂' := Nat.cast_lt.mpr h_lt
  have h_sum : (n₁ : ℝ) + n₂ > 0 := by linarith
  have h_sum' : (n₁ : ℝ) + n₂' > 0 := by linarith
  have h_denom_lt : (n₁ : ℝ) + n₂ < n₁ + n₂' := by linarith
  have h_inv : 1 / ((n₁ : ℝ) + n₂') < 1 / (n₁ + n₂) := (one_div_lt_one_div h_sum' h_sum).mpr h_denom_lt
  have h_2n₁_pos : 2 * (n₁ : ℝ) > 0 := by linarith
  calc 2 * (n₁ : ℝ) / (n₁ + n₂)
      = 2 * n₁ * (1 / (n₁ + n₂)) := by ring
    _ > 2 * n₁ * (1 / (n₁ + n₂')) := by nlinarith
    _ = 2 * n₁ / (n₁ + n₂') := by ring

/-- Residual mass after maximum binding. -/
noncomputable def residual_mass_after_binding (n₁ n₂ : ℕ) : ℝ :=
  GravitationalStability.total_rest_mass n₁ n₂ - max_binding_energy n₁ n₂

/-- Residual mass formula. -/
theorem residual_mass_formula (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_le : n₁ ≤ n₂) :
    residual_mass_after_binding n₁ n₂ = mass_of_cycle n₁ - mass_of_cycle n₂ := by
  unfold residual_mass_after_binding
  exact schwarzschild_deficit_is_mass_difference n₁ n₂ h₁ h₂ h_le

/-- For equal masses, residual is zero (complete annihilation possible). -/
theorem equal_mass_zero_residual (m : ℕ) (h : m ≥ 3) :
    residual_mass_after_binding m m = 0 := by
  rw [residual_mass_formula m m h h (le_refl m)]
  unfold mass_of_cycle
  ring

/-- For unequal masses, residual is positive (complete annihilation impossible). -/
theorem unequal_mass_positive_residual (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_lt : n₁ < n₂) :
    residual_mass_after_binding n₁ n₂ > 0 := by
  rw [residual_mass_formula n₁ n₂ h₁ h₂ (le_of_lt h_lt)]
  unfold mass_of_cycle
  have hn₁ : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂ : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_lt' : (n₁ : ℝ) < n₂ := Nat.cast_lt.mpr h_lt
  have h_inv : 1 / (n₂ : ℝ) < 1 / n₁ := (one_div_lt_one_div hn₂ hn₁).mpr h_lt'
  linarith

/-- Efficiency = 1 iff equal masses. -/
theorem equal_optimal_for_schwarzschild (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    binding_efficiency n₁ n₂ = 1 ↔ n₁ = n₂ := by
  constructor
  · intro h_eff
    by_contra h_ne
    cases Nat.lt_or_gt_of_ne h_ne with
    | inl h_lt =>
      have := unequal_mass_imperfect_efficiency n₁ n₂ h₁ h₂ h_lt
      linarith
    | inr h_gt =>
      have h_symm := binding_efficiency_symm n₁ n₂ h₁ h₂
      rw [h_symm] at h_eff
      have := unequal_mass_imperfect_efficiency n₂ n₁ h₂ h₁ h_gt
      linarith
  · intro h_eq
    rw [h_eq]
    exact equal_mass_perfect_efficiency n₂ h₂

/-- Residual mass equals mass difference. -/
theorem heavy_particle_dominates_residual (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_lt : n₁ < n₂) :
    residual_mass_after_binding n₁ n₂ = mass_of_cycle n₁ - mass_of_cycle n₂ ∧
    mass_of_cycle n₁ > mass_of_cycle n₂ := by
  constructor
  · exact residual_mass_formula n₁ n₂ h₁ h₂ (le_of_lt h_lt)
  · exact mass_decreases_with_length n₁ n₂ (by omega) (by omega) h_lt

end Diaspora.Dynamics.AsymmetricBinding
