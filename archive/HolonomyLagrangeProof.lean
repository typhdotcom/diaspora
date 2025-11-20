/-
# Core Holonomy Proof via Lagrange Multipliers

Proves V_int ≥ K²/n for any n-cycle via constrained optimization.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open BigOperators

namespace HolonomyProof

/-! ## Constrained Optimization

Minimize Σ(v_i - c_i)² subject to Σv_i = 0
-/

/-! ## Triangle Case -/

/-- For a triangle with constraints c₀, c₁, c₂, the minimum V_int is K²/3 -/
theorem triangle_holonomy (c₀ c₁ c₂ : ℝ) :
    let K := c₀ + c₁ + c₂  -- Holonomy defect
    let v₀ := c₀ - K/3     -- Optimal edge value 0
    let v₁ := c₁ - K/3     -- Optimal edge value 1
    let v₂ := c₂ - K/3     -- Optimal edge value 2
    -- These satisfy the constraint
    v₀ + v₁ + v₂ = 0 ∧
    -- And achieve minimum V_int = K²/3
    (v₀ - c₀)^2 + (v₁ - c₁)^2 + (v₂ - c₂)^2 = K^2 / 3 := by
  intro K v₀ v₁ v₂
  constructor

  -- Part 1: Constraint satisfaction
  · calc v₀ + v₁ + v₂
        = (c₀ - K/3) + (c₁ - K/3) + (c₂ - K/3) := by rfl
      _ = c₀ + c₁ + c₂ - 3*(K/3) := by ring
      _ = K - K := by ring
      _ = 0 := by ring

  -- Part 2: Minimum value
  · calc (v₀ - c₀)^2 + (v₁ - c₁)^2 + (v₂ - c₂)^2
        = ((c₀ - K/3) - c₀)^2 + ((c₁ - K/3) - c₁)^2 + ((c₂ - K/3) - c₂)^2 := by rfl
      _ = (-K/3)^2 + (-K/3)^2 + (-K/3)^2 := by ring
      _ = 3 * (K/3)^2 := by ring
      _ = 3 * (K^2 / 9) := by ring
      _ = K^2 / 3 := by ring

/-- If K ≠ 0, then minimum V_int > 0 -/
theorem triangle_holonomy_positive (c₀ c₁ c₂ : ℝ) (h : c₀ + c₁ + c₂ ≠ 0) :
    0 < (c₀ + c₁ + c₂)^2 / 3 := by
  have h_sq : 0 < (c₀ + c₁ + c₂)^2 := by
    rw [sq_pos_iff]
    exact h
  exact div_pos h_sq (by norm_num : (0:ℝ) < 3)

/-! ## Optimality -/

/-- Any constrained values have V_int ≥ K²/3 -/
theorem triangle_optimal (c₀ c₁ c₂ : ℝ) (v₀ v₁ v₂ : ℝ) (h_constraint : v₀ + v₁ + v₂ = 0) :
    let K := c₀ + c₁ + c₂
    K^2 / 3 ≤ (v₀ - c₀)^2 + (v₁ - c₁)^2 + (v₂ - c₂)^2 := by
  intro K
  let v₀_opt := c₀ - K/3
  let v₁_opt := c₁ - K/3
  let v₂_opt := c₂ - K/3
  let d₀ := v₀ - v₀_opt
  let d₁ := v₁ - v₁_opt
  let d₂ := v₂ - v₂_opt

  -- Deviations sum to zero
  have h_dev : d₀ + d₁ + d₂ = 0 := by
    have h_opt_sum : v₀_opt + v₁_opt + v₂_opt = 0 := by
      calc v₀_opt + v₁_opt + v₂_opt
          = (c₀ - K/3) + (c₁ - K/3) + (c₂ - K/3) := rfl
        _ = c₀ + c₁ + c₂ - K := by ring
        _ = K - K := rfl
        _ = 0 := by ring
    calc d₀ + d₁ + d₂
        = (v₀ - v₀_opt) + (v₁ - v₁_opt) + (v₂ - v₂_opt) := rfl
      _ = (v₀ + v₁ + v₂) - (v₀_opt + v₁_opt + v₂_opt) := by ring
      _ = 0 - 0 := by rw [h_constraint, h_opt_sum]
      _ = 0 := by ring

  -- Key observation: v_i - c_i = -K/3 + d_i
  have h_v0 : v₀ - c₀ = -K/3 + d₀ := by
    calc v₀ - c₀ = v₀ - c₀ := rfl
      _ = (v₀_opt + d₀) - c₀ := by ring
      _ = ((c₀ - K/3) + d₀) - c₀ := rfl
      _ = -K/3 + d₀ := by ring

  have h_v1 : v₁ - c₁ = -K/3 + d₁ := by
    calc v₁ - c₁ = (v₁_opt + d₁) - c₁ := by ring
      _ = ((c₁ - K/3) + d₁) - c₁ := rfl
      _ = -K/3 + d₁ := by ring

  have h_v2 : v₂ - c₂ = -K/3 + d₂ := by
    calc v₂ - c₂ = (v₂_opt + d₂) - c₂ := by ring
      _ = ((c₂ - K/3) + d₂) - c₂ := rfl
      _ = -K/3 + d₂ := by ring

  -- Expand the squares
  calc (v₀ - c₀)^2 + (v₁ - c₁)^2 + (v₂ - c₂)^2
      = (-K/3 + d₀)^2 + (-K/3 + d₁)^2 + (-K/3 + d₂)^2 := by rw [h_v0, h_v1, h_v2]
    _ = ((K/3)^2 - 2*(K/3)*d₀ + d₀^2) + ((K/3)^2 - 2*(K/3)*d₁ + d₁^2) + ((K/3)^2 - 2*(K/3)*d₂ + d₂^2) := by
        congr 1 <;> (congr 1 <;> ring)
    _ = 3*(K/3)^2 - 2*(K/3)*(d₀ + d₁ + d₂) + (d₀^2 + d₁^2 + d₂^2) := by ring
    _ = 3*(K/3)^2 - 2*(K/3)*0 + (d₀^2 + d₁^2 + d₂^2) := by rw [h_dev]
    _ = K^2/3 + (d₀^2 + d₁^2 + d₂^2) := by ring
    _ ≥ K^2/3 := by linarith [sq_nonneg d₀, sq_nonneg d₁, sq_nonneg d₂]

/-! ## General n-Cycle -/

/-- For general n-cycle: V_int_min = K²/n where K = Σc_i -/
theorem general_cycle_holonomy (n : ℕ) (h_n : 3 ≤ n) (c : Fin n → ℝ) :
    let K := ∑ i : Fin n, c i
    let v_opt : Fin n → ℝ := fun i => c i - K / n
    -- Constraint satisfied
    (∑ i : Fin n, v_opt i = 0) ∧
    -- Minimum V_int achieved
    (∑ i : Fin n, (v_opt i - c i)^2 = K^2 / n) := by
  intro K v_opt
  constructor

  -- Constraint: ∑v_opt i = ∑(c i - K/n) = K - K = 0
  · simp only [v_opt]
    have h1 : ∑ i : Fin n, (K / n) = (n : ℝ) * (K / n) := by
      calc ∑ i : Fin n, (K / n)
          = Finset.card Finset.univ • (K / n) := Finset.sum_const _
        _ = (n : ℕ) • (K / n) := by rw [Finset.card_fin]
        _ = (n : ℝ) * (K / n) := by simp [nsmul_eq_mul]
    calc ∑ i : Fin n, (c i - K / n)
        = ∑ i : Fin n, c i - ∑ i : Fin n, (K / n) := by
          simp only [Finset.sum_sub_distrib]
      _ = K - (n : ℝ) * (K / n) := by rw [h1]
      _ = 0 := by field_simp; ring

  -- Minimum value: ∑(v_opt i - c i)² = ∑(-K/n)² = K²/n
  · simp only [v_opt]
    have h2 : ∑ i : Fin n, (K / n)^2 = (n : ℝ) * (K / n)^2 := by
      calc ∑ i : Fin n, (K / n)^2
          = Finset.card Finset.univ • (K / n)^2 := Finset.sum_const _
        _ = (n : ℕ) • (K / n)^2 := by rw [Finset.card_fin]
        _ = (n : ℝ) * (K / n)^2 := by simp [nsmul_eq_mul]
    calc ∑ i : Fin n, (c i - K / n - c i)^2
        = ∑ i : Fin n, (-K / n)^2 := by
          congr 1; funext i; ring
      _ = ∑ i : Fin n, (K / n)^2 := by
          congr 1; funext i; ring
      _ = (n : ℝ) * (K / n)^2 := h2
      _ = K^2 / n := by field_simp

/-! ## Main Result -/

/-- Cycles force holonomy: minimum V_int = K²/n where K = Σc_i -/

theorem general_cycle_optimal (n : ℕ) (h_n : 3 ≤ n) (c : Fin n → ℝ) (v : Fin n → ℝ)
    (h_constraint : ∑ i : Fin n, v i = 0) :
    let K := ∑ i : Fin n, c i
    K^2 / n ≤ ∑ i : Fin n, (v i - c i)^2 := by
  intro K
  let v_opt : Fin n → ℝ := fun i => c i - K / n
  let d : Fin n → ℝ := fun i => v i - v_opt i

  -- First establish that v_opt sums to 0
  have h_vopt_sum : ∑ i : Fin n, v_opt i = 0 := by
    have h1 := general_cycle_holonomy n h_n c
    exact h1.1

  -- Deviations sum to zero
  have h_dev : ∑ i : Fin n, d i = 0 := by
    simp only [d]
    calc ∑ i : Fin n, (v i - v_opt i)
        = ∑ i : Fin n, v i - ∑ i : Fin n, v_opt i := by
          simp only [Finset.sum_sub_distrib]
      _ = 0 - 0 := by rw [h_constraint, h_vopt_sum]
      _ = 0 := by ring

  -- v_i - c_i = -K/n + d_i
  have h_decomp : ∀ i, v i - c i = -K/n + d i := by
    intro i
    simp only [d, v_opt]
    ring

  -- Expand: (v_i - c_i)² = (-K/n + d_i)² = (K/n)² - 2(K/n)d_i + d_i²
  -- Sum over i: cross terms vanish because ∑d_i = 0
  have h_sum_sq : ∑ i : Fin n, (K/n)^2 = (n : ℝ) * (K/n)^2 := by
    calc ∑ i : Fin n, (K/n)^2
        = Finset.card Finset.univ • (K/n)^2 := Finset.sum_const _
      _ = (n : ℕ) • (K/n)^2 := by rw [Finset.card_fin]
      _ = (n : ℝ) * (K/n)^2 := by simp [nsmul_eq_mul]

  calc ∑ i : Fin n, (v i - c i)^2
      = ∑ i : Fin n, (-K/n + d i)^2 := by
        congr 1; funext i; rw [h_decomp]
    _ = ∑ i : Fin n, ((K/n)^2 - 2*(K/n)*(d i) + (d i)^2) := by
        congr 1; funext i; ring
    _ = ∑ i : Fin n, ((K/n)^2 + (d i)^2 - 2*(K/n)*(d i)) := by
        congr 1; funext i; ring
    _ = (∑ i : Fin n, (K/n)^2) + (∑ i : Fin n, (d i)^2) - (∑ i : Fin n, 2*(K/n)*(d i)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (∑ i : Fin n, (K/n)^2) + (∑ i : Fin n, (d i)^2) - 2*(K/n)*(∑ i : Fin n, d i) := by
        rw [← Finset.mul_sum]
    _ = (∑ i : Fin n, (K/n)^2) + (∑ i : Fin n, (d i)^2) - 2*(K/n)*0 := by
        rw [h_dev]
    _ = (n : ℝ)*(K/n)^2 + (∑ i : Fin n, (d i)^2) := by
        rw [h_sum_sq]; ring
    _ = K^2/n + (∑ i : Fin n, (d i)^2) := by
        field_simp
    _ ≥ K^2/n := by
        have : 0 ≤ ∑ i : Fin n, (d i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
        linarith

theorem holonomy_is_inevitable (n : ℕ) (h_n : 3 ≤ n) (c : Fin n → ℝ)
    (h_nontrivial : ∑ i : Fin n, c i ≠ 0) :
    ∃ (ε : ℝ), 0 < ε ∧
    ∀ (v : Fin n → ℝ), (∑ i : Fin n, v i = 0) →
    ε ≤ ∑ i : Fin n, (v i - c i)^2 := by
  use (∑ i : Fin n, c i)^2 / n
  constructor
  · -- ε > 0
    have h_sq : 0 < (∑ i : Fin n, c i)^2 := by
      rw [sq_pos_iff]
      exact h_nontrivial
    have h_n_pos : (0 : ℝ) < n := by
      have : 0 < 3 := by norm_num
      exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le this h_n)
    exact div_pos h_sq h_n_pos
  · -- Lower bound holds for all constrained v
    intro v h_constraint
    exact general_cycle_optimal n h_n c v h_constraint

end HolonomyProof
