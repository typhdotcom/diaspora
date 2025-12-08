import Diaspora.Dynamics.InvariantMass
import Diaspora.Dynamics.Velocity

/-!
# Bound State Kinematics: Full Relativistic Treatment

This file extends the velocity and invariant mass results to bound states with
arbitrary binding energy. The key insight: binding affects energy but NOT momentum,
leading to surprising kinematic consequences.

## The Core Formula

For two cycles of length n₁, n₂ with k shared opposite-direction edges:
- E = (n₁ + n₂ - 2k)/(n₁·n₂)     (binding reduces energy)
- p = (n₂ - n₁)/(n₁·n₂)          (momentum unchanged!)
- m² = 4(n₁ - k)(n₂ - k)/(n₁·n₂)² (elegant factored form)

## Main Results

- `bound_invariant_mass_sq`: m² = 4(n₁ - k)(n₂ - k)/(n₁n₂)² for bound pairs
- `bound_velocity`: v = |n₂ - n₁|/(n₁ + n₂ - 2k) for bound pairs
- `binding_increases_velocity`: For unequal masses, more binding → faster motion
- `bound_relativistic_identity`: γ² = 1/(1 - v²) for bound states
- `max_binding_returns_lightlike`: At k = min(n₁, n₂), m² = 0 (back to lightlike)

## Physical Interpretation

Binding changes energy without changing momentum. Since v = p/E:
- For equal masses (n₁ = n₂): p = 0, so v = 0 regardless of binding
- For unequal masses: binding reduces E, increasing v = p/E

At maximum binding (k = min(n₁, n₂)), the smaller cycle is fully absorbed.
The system becomes lightlike again (v = c), with energy equal to the mass
difference. This is "partial annihilation": the lighter particle disappears,
leaving behind only the excess mass of the heavier one.
-/

namespace Diaspora.Dynamics.BoundStateKinematics

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.Dispersion
open Diaspora.Dynamics.InvariantMass
open Diaspora.Dynamics.Velocity

/-! ## Bound State Energy and Momentum -/

/-- Total energy of a bound opposite-direction pair. -/
noncomputable def bound_total_energy (n₁ n₂ k : ℕ) : ℝ :=
  mass_of_cycle n₁ + mass_of_cycle n₂ - sharing_energy_reduction n₁ n₂ k

/-- Total momentum of a bound opposite-direction pair (independent of binding!). -/
noncomputable def bound_total_momentum (n₁ n₂ : ℕ) : ℝ :=
  mass_of_cycle n₁ - mass_of_cycle n₂

/-- The bound energy simplifies to (n₁ + n₂ - 2k)/(n₁·n₂). -/
theorem bound_energy_formula (n₁ n₂ k : ℕ) (h₁ : n₁ > 0) (h₂ : n₂ > 0) :
    bound_total_energy n₁ n₂ k = (n₁ + n₂ - 2 * k : ℝ) / (n₁ * n₂) := by
  unfold bound_total_energy mass_of_cycle sharing_energy_reduction
  have hn₁ : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h₁)
  have hn₂ : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h₂)
  field_simp [hn₁, hn₂]
  ring

/-- The bound momentum simplifies to (n₂ - n₁)/(n₁·n₂). -/
theorem bound_momentum_formula (n₁ n₂ : ℕ) (h₁ : n₁ > 0) (h₂ : n₂ > 0) :
    bound_total_momentum n₁ n₂ = (n₂ - n₁ : ℝ) / (n₁ * n₂) := by
  unfold bound_total_momentum mass_of_cycle
  have hn₁ : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h₁)
  have hn₂ : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h₂)
  field_simp [hn₁, hn₂]

/-! ## Bound State Invariant Mass -/

/-- **The Bound Invariant Mass Squared Formula**

    m² = 4(n₁ - k)(n₂ - k) / (n₁·n₂)²

    Key special cases:
    - k = 0: m² = 4/(n₁·n₂) = 4·m₁·m₂ (unbound)
    - k = n₁ (with n₁ ≤ n₂): m² = 0 (returns to lightlike!)
    - n₁ = n₂ = n, k = n: m² = 0 (complete annihilation) -/
noncomputable def bound_invariant_mass_sq (n₁ n₂ k : ℕ) : ℝ :=
  4 * (n₁ - k : ℝ) * (n₂ - k) / ((n₁ : ℝ) * n₂)^2

/-- The bound invariant mass formula agrees with E² - p². -/
theorem bound_invariant_mass_sq_correct (n₁ n₂ k : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3)
    (_hk : k ≤ min n₁ n₂) :
    bound_invariant_mass_sq n₁ n₂ k =
      (bound_total_energy n₁ n₂ k)^2 - (bound_total_momentum n₁ n₂)^2 := by
  have hn₁ : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn₂ : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [bound_energy_formula n₁ n₂ k (by omega) (by omega)]
  rw [bound_momentum_formula n₁ n₂ (by omega) (by omega)]
  unfold bound_invariant_mass_sq
  have h_prod_ne : (n₁ : ℝ) * n₂ ≠ 0 := mul_ne_zero hn₁ hn₂
  -- (E² - p²) = [(n₁+n₂-2k)² - (n₂-n₁)²] / (n₁n₂)²
  -- numerator = (2n₂ - 2k)(2n₁ - 2k) = 4(n₁-k)(n₂-k)
  field_simp [h_prod_ne]
  ring

/-- At k = 0, the bound formula reduces to the unbound case. -/
theorem bound_mass_sq_at_zero (n₁ n₂ : ℕ) (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3) :
    bound_invariant_mass_sq n₁ n₂ 0 = 4 * mass_of_cycle n₁ * mass_of_cycle n₂ := by
  unfold bound_invariant_mass_sq mass_of_cycle
  have hn₁ : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn₂ : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [Nat.cast_zero, sub_zero]
  field_simp [hn₁, hn₂]

/-- **Maximum Binding Returns to Lightlike**: When k = min(n₁, n₂), m² = 0. -/
theorem max_binding_returns_lightlike (n₁ n₂ : ℕ) (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3)
    (_h_le : n₁ ≤ n₂) :
    bound_invariant_mass_sq n₁ n₂ n₁ = 0 := by
  unfold bound_invariant_mass_sq
  simp only [sub_self, mul_zero, zero_mul, zero_div]

/-- For equal masses at complete binding, m² = 0 (complete annihilation). -/
theorem equal_mass_annihilation (n : ℕ) (_h : n ≥ 3) :
    bound_invariant_mass_sq n n n = 0 := by
  unfold bound_invariant_mass_sq
  simp only [sub_self, mul_zero, zero_div]

/-! ## Bound State Velocity -/

/-- **Velocity of a bound opposite-direction pair**.

    v = |p|/E = |n₂ - n₁|/(n₁ + n₂ - 2k)

    Key insight: binding appears only in the denominator!
    - At k = 0: v = |n₂ - n₁|/(n₁ + n₂) (matches unbound formula)
    - For k > 0: denominator shrinks, so v increases
    - At k = n₁ (with n₁ < n₂): v = 1 (returns to lightlike!) -/
noncomputable def bound_velocity (n₁ n₂ k : ℕ) : ℝ :=
  |(n₂ : ℝ) - n₁| / (n₁ + n₂ - 2 * k)

/-- At k = 0, the bound velocity matches the unbound formula. -/
theorem bound_velocity_at_zero (n₁ n₂ : ℕ) :
    bound_velocity n₁ n₂ 0 = opposite_pair_velocity n₁ n₂ := by
  unfold bound_velocity opposite_pair_velocity
  simp only [Nat.cast_zero, mul_zero, sub_zero]
  congr 1
  ring

/-- **Binding Increases Velocity** for unequal masses.

    When n₁ ≠ n₂ and k > 0, the bound velocity exceeds the unbound velocity. -/
theorem binding_increases_velocity (n₁ n₂ k : ℕ) (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3)
    (h_ne : n₁ ≠ n₂) (hk_pos : k > 0) (hk_bound : 2 * k < n₁ + n₂) :
    bound_velocity n₁ n₂ k > opposite_pair_velocity n₁ n₂ := by
  unfold bound_velocity opposite_pair_velocity
  have hn₁_pos : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂_pos : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_sum_pos : (n₁ : ℝ) + n₂ > 0 := by linarith
  have h_denom_pos : (n₁ : ℝ) + n₂ - 2 * k > 0 := by
    have h1 : (2 * k : ℕ) < n₁ + n₂ := hk_bound
    have h2 : ((2 * k : ℕ) : ℝ) < ((n₁ + n₂ : ℕ) : ℝ) := Nat.cast_lt.mpr h1
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add] at h2
    linarith
  have h_abs_pos : |(n₂ : ℝ) - n₁| > 0 := by
    simp only [abs_pos, ne_eq, sub_eq_zero]
    intro h_eq
    exact h_ne.symm (Nat.cast_injective h_eq)
  have h_denom_lt : (n₁ : ℝ) + n₂ - 2 * k < n₁ + n₂ := by
    have hk' : (k : ℝ) > 0 := Nat.cast_pos.mpr hk_pos
    linarith
  -- |n₂ - n₁| / (n₁ + n₂ - 2k) > |n₂ - n₁| / (n₁ + n₂)
  -- because smaller denominator with positive numerator
  rw [gt_iff_lt, ← sub_pos]
  have h_diff : |(n₂ : ℝ) - n₁| / (n₁ + n₂ - 2 * k) - |(n₂ : ℝ) - n₁| / (n₂ + n₁) =
      |(n₂ : ℝ) - n₁| * (2 * k) / ((n₁ + n₂ - 2 * k) * (n₂ + n₁)) := by
    have h_ne1 : (n₁ : ℝ) + n₂ - 2 * k ≠ 0 := ne_of_gt h_denom_pos
    have h_ne2 : (n₂ : ℝ) + n₁ ≠ 0 := by linarith
    field_simp [h_ne1, h_ne2]
    ring
  rw [h_diff]
  have hk' : (k : ℝ) > 0 := Nat.cast_pos.mpr hk_pos
  have h_sum_pos' : (n₂ : ℝ) + n₁ > 0 := by linarith
  positivity

/-- Equal masses always have zero velocity, regardless of binding. -/
theorem equal_mass_always_at_rest (n k : ℕ) (_h : n ≥ 3) (_hk : 2 * k < 2 * n) :
    bound_velocity n n k = 0 := by
  unfold bound_velocity
  simp only [sub_self, abs_zero, zero_div]

/-- **At Maximum Binding, Velocity Equals c** (for unequal masses). -/
theorem max_binding_velocity_is_c (n₁ n₂ : ℕ) (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3)
    (h_lt : n₁ < n₂) :
    bound_velocity n₁ n₂ n₁ = 1 := by
  unfold bound_velocity
  have h_num : |(n₂ : ℝ) - n₁| = n₂ - n₁ := by
    rw [abs_of_pos]
    have : (n₁ : ℝ) < n₂ := Nat.cast_lt.mpr h_lt
    linarith
  have h_denom : (n₁ : ℝ) + n₂ - 2 * n₁ = n₂ - n₁ := by ring
  rw [h_num, h_denom]
  have h_ne : (n₂ : ℝ) - n₁ ≠ 0 := by
    have : (n₁ : ℝ) < n₂ := Nat.cast_lt.mpr h_lt
    linarith
  exact div_self h_ne

/-! ## Relativistic Identity for Bound States -/

/-- **The Bound Lorentz Factor**: γ = E/m for bound states. -/
noncomputable def bound_lorentz_factor (n₁ n₂ k : ℕ) : ℝ :=
  (n₁ + n₂ - 2 * k : ℝ) / (2 * Real.sqrt ((n₁ - k : ℝ) * (n₂ - k)))

/-- At k = 0, the bound Lorentz factor matches the unbound one. -/
theorem bound_lorentz_at_zero (n₁ n₂ : ℕ) :
    bound_lorentz_factor n₁ n₂ 0 = lorentz_factor n₁ n₂ := by
  unfold bound_lorentz_factor lorentz_factor
  simp only [Nat.cast_zero, sub_zero, mul_zero]

/-- **The Relativistic Identity for Bound States**: γ² = 1/(1 - v²). -/
theorem bound_relativistic_identity (n₁ n₂ k : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3)
    (hk : k < min n₁ n₂) :
    (bound_lorentz_factor n₁ n₂ k)^2 = 1 / (1 - (bound_velocity n₁ n₂ k)^2) := by
  unfold bound_velocity bound_lorentz_factor
  have hn₁_pos : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂_pos : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hk_n₁ : k < n₁ := Nat.lt_of_lt_of_le hk (min_le_left n₁ n₂)
  have hk_n₂ : k < n₂ := Nat.lt_of_lt_of_le hk (min_le_right n₁ n₂)
  have h_n₁_k_pos : (n₁ : ℝ) - k > 0 := by
    have : (k : ℝ) < n₁ := Nat.cast_lt.mpr hk_n₁
    linarith
  have h_n₂_k_pos : (n₂ : ℝ) - k > 0 := by
    have : (k : ℝ) < n₂ := Nat.cast_lt.mpr hk_n₂
    linarith
  have h_prod_pos : ((n₁ : ℝ) - k) * (n₂ - k) > 0 := mul_pos h_n₁_k_pos h_n₂_k_pos
  have h_sqrt_pos : Real.sqrt (((n₁ : ℝ) - k) * (n₂ - k)) > 0 := Real.sqrt_pos.mpr h_prod_pos
  have h_sum_2k_pos : (n₁ : ℝ) + n₂ - 2 * k > 0 := by linarith
  have h_v_sq : (|(n₂ : ℝ) - n₁| / (n₁ + n₂ - 2 * k))^2 =
      (n₂ - n₁)^2 / (n₁ + n₂ - 2 * k)^2 := by
    rw [div_pow, sq_abs]
  rw [h_v_sq]
  have h_1_minus_v_sq : 1 - (n₂ - n₁ : ℝ)^2 / (n₁ + n₂ - 2 * k)^2 =
      4 * (n₁ - k) * (n₂ - k) / (n₁ + n₂ - 2 * k)^2 := by
    have h_ne : (n₁ + n₂ - 2 * k : ℝ)^2 ≠ 0 := by positivity
    field_simp [h_ne]
    ring
  rw [h_1_minus_v_sq]
  have h_gamma_sq : ((n₁ + n₂ - 2 * k : ℝ) / (2 * Real.sqrt ((n₁ - k) * (n₂ - k))))^2 =
      (n₁ + n₂ - 2 * k)^2 / (4 * (n₁ - k) * (n₂ - k)) := by
    rw [div_pow, mul_pow]
    have h_sqrt_sq : (Real.sqrt (((n₁ : ℝ) - k) * (n₂ - k)))^2 = (n₁ - k) * (n₂ - k) :=
      Real.sq_sqrt (le_of_lt h_prod_pos)
    rw [h_sqrt_sq]
    ring
  rw [h_gamma_sq, one_div, inv_div]

/-- The Lorentz factor is at least 1 for bound states (by AM-GM). -/
theorem bound_lorentz_ge_one (n₁ n₂ k : ℕ) (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3)
    (hk : k < min n₁ n₂) :
    bound_lorentz_factor n₁ n₂ k ≥ 1 := by
  unfold bound_lorentz_factor
  have hk_n₁ : k < n₁ := Nat.lt_of_lt_of_le hk (min_le_left n₁ n₂)
  have hk_n₂ : k < n₂ := Nat.lt_of_lt_of_le hk (min_le_right n₁ n₂)
  have h_n₁_k_pos : (n₁ : ℝ) - k > 0 := by
    have : (k : ℝ) < n₁ := Nat.cast_lt.mpr hk_n₁
    linarith
  have h_n₂_k_pos : (n₂ : ℝ) - k > 0 := by
    have : (k : ℝ) < n₂ := Nat.cast_lt.mpr hk_n₂
    linarith
  have h_prod_pos : ((n₁ : ℝ) - k) * (n₂ - k) > 0 := mul_pos h_n₁_k_pos h_n₂_k_pos
  have h_sqrt_pos : Real.sqrt (((n₁ : ℝ) - k) * (n₂ - k)) > 0 := Real.sqrt_pos.mpr h_prod_pos
  have h_denom_pos : 2 * Real.sqrt (((n₁ : ℝ) - k) * (n₂ - k)) > 0 := by linarith
  -- AM-GM: (n₁ - k) + (n₂ - k) ≥ 2√[(n₁ - k)(n₂ - k)]
  have h_sqrt_n₁k : Real.sqrt (n₁ - k : ℝ) ^ 2 = n₁ - k := Real.sq_sqrt (le_of_lt h_n₁_k_pos)
  have h_sqrt_n₂k : Real.sqrt (n₂ - k : ℝ) ^ 2 = n₂ - k := Real.sq_sqrt (le_of_lt h_n₂_k_pos)
  have h_sqrt_prod : Real.sqrt (((n₁ : ℝ) - k) * (n₂ - k)) =
      Real.sqrt (n₁ - k) * Real.sqrt (n₂ - k) :=
    Real.sqrt_mul (le_of_lt h_n₁_k_pos) (n₂ - k)
  have h_am_gm : ((n₁ : ℝ) - k) + (n₂ - k) ≥ 2 * Real.sqrt ((n₁ - k) * (n₂ - k)) := by
    have h_sq_nonneg : (Real.sqrt (n₁ - k : ℝ) - Real.sqrt (n₂ - k))^2 ≥ 0 := sq_nonneg _
    calc ((n₁ : ℝ) - k) + (n₂ - k)
        = Real.sqrt (n₁ - k : ℝ) ^ 2 + Real.sqrt (n₂ - k : ℝ) ^ 2 := by
            rw [h_sqrt_n₁k, h_sqrt_n₂k]
      _ = (Real.sqrt (n₁ - k : ℝ) - Real.sqrt (n₂ - k))^2 +
            2 * (Real.sqrt (n₁ - k : ℝ) * Real.sqrt (n₂ - k)) := by ring
      _ ≥ 0 + 2 * (Real.sqrt (n₁ - k : ℝ) * Real.sqrt (n₂ - k)) := by linarith
      _ = 2 * Real.sqrt ((n₁ - k : ℝ) * (n₂ - k)) := by rw [zero_add, h_sqrt_prod]
  have h_num : (n₁ : ℝ) + n₂ - 2 * k = (n₁ - k) + (n₂ - k) := by ring
  rw [ge_iff_le, one_le_div h_denom_pos, h_num]
  calc 2 * Real.sqrt (((n₁ : ℝ) - k) * (n₂ - k)) = 2 * Real.sqrt ((n₁ - k) * (n₂ - k)) := by rfl
    _ ≤ (n₁ - k) + (n₂ - k) := h_am_gm

/-! ## The Kinematics Correspondence -/

/-- **The Bound State Kinematics Correspondence** (Summary Theorem) -/
theorem the_bound_kinematics_correspondence (n : ℕ) (h : n ≥ 3) :
    -- 1. At k = 0, matches unbound velocity
    (bound_velocity n n 0 = opposite_pair_velocity n n) ∧
    -- 2. Equal masses at rest regardless of binding
    (∀ k, 2 * k < 2 * n → bound_velocity n n k = 0) ∧
    -- 3. Lorentz factor at zero matches unbound
    (bound_lorentz_factor n n 0 = lorentz_factor n n) := by
  refine ⟨?_, ?_, ?_⟩
  · exact bound_velocity_at_zero n n
  · intro k hk
    exact equal_mass_always_at_rest n k h hk
  · exact bound_lorentz_at_zero n n

/-- **Partial Annihilation Energy**: When k = n₁ with n₁ < n₂, E = m₁ - m₂. -/
theorem partial_annihilation_energy (n₁ n₂ : ℕ) (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3)
    (_h_lt : n₁ < n₂) :
    bound_total_energy n₁ n₂ n₁ = mass_of_cycle n₁ - mass_of_cycle n₂ := by
  unfold bound_total_energy mass_of_cycle sharing_energy_reduction
  have hn₁ : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn₂ : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hn₁, hn₂]
  ring

/-- At partial annihilation, |E| = |p| (confirming lightlike). -/
theorem partial_annihilation_lightlike (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3)
    (h_lt : n₁ < n₂) :
    |bound_total_energy n₁ n₂ n₁| = |bound_total_momentum n₁ n₂| := by
  rw [partial_annihilation_energy n₁ n₂ h₁ h₂ h_lt]
  unfold bound_total_momentum
  congr 1

end Diaspora.Dynamics.BoundStateKinematics
