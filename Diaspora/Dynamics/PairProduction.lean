import Diaspora.Dynamics.BoundStates
import Diaspora.Dynamics.Planck

/-!
# Pair Production

Energy threshold for creating cycle-anticycle pairs: 2/n for an n-cycle pair.
Genesis threshold (minimum for any matter) is 2/3.
-/

namespace Diaspora.Dynamics.PairProduction

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.Planck

/-- Energy threshold for creating an n-cycle pair: 2m = 2/n. -/
noncomputable def pair_threshold (n : ℕ) : ℝ := 2 * mass_of_cycle n

theorem pair_threshold_formula (n : ℕ) (h : n > 0) :
    pair_threshold n = 2 / n := by
  unfold pair_threshold mass_of_cycle
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h)
  field_simp [hn]

theorem pair_threshold_pos (n : ℕ) (h : n ≥ 3) : pair_threshold n > 0 := by
  unfold pair_threshold mass_of_cycle
  have hn : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  positivity

/-! ## Genesis Threshold -/

/-- Minimum energy to create any matter: 2/3 (triangle pair). -/
noncomputable def genesis_threshold : ℝ := pair_threshold 3

theorem genesis_threshold_value : genesis_threshold = 2 / 3 := by
  unfold genesis_threshold
  rw [pair_threshold_formula 3 (by omega)]
  norm_num

/-- Triangle pair (n=3) achieves the minimum threshold. -/
theorem genesis_is_minimum (n : ℕ) (h : n ≥ 3) :
    pair_threshold n ≤ genesis_threshold := by
  simp only [pair_threshold, genesis_threshold, mass_of_cycle]
  have h₃ : (3 : ℝ) > 0 := by norm_num
  have hn : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_le : (3 : ℝ) ≤ n := Nat.cast_le.mpr h
  have h1 : (1 : ℝ) / n ≤ 1 / 3 := one_div_le_one_div_of_le h₃ h_le
  linarith

theorem triangle_achieves_genesis : pair_threshold 3 = genesis_threshold := rfl

theorem production_annihilation_dual (n : ℕ) (_h : n ≥ 3) :
    pair_threshold n = 2 * mass_of_cycle n := rfl

theorem pair_threshold_is_sum_of_masses (n : ℕ) (_h : n > 0) :
    pair_threshold n = mass_of_cycle n + mass_of_cycle n := by
  unfold pair_threshold
  ring

/-! ## Threshold Hierarchy -/

/-- Smaller n means higher threshold. -/
theorem heavier_pairs_harder (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_lt : n₁ < n₂) :
    pair_threshold n₁ > pair_threshold n₂ := by
  unfold pair_threshold
  have h_mass := mass_decreases_with_length n₁ n₂ (by omega) (by omega) h_lt
  linarith

theorem lighter_pairs_easier (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_lt : n₁ < n₂) :
    pair_threshold n₂ < pair_threshold n₁ :=
  heavier_pairs_harder n₁ n₂ h₁ h₂ h_lt

/-! ## The Threshold Spectrum -/

/-- Thresholds form a discrete set: 2/3, 2/4, 2/5, ... -/
theorem threshold_spectrum (n : ℕ) (h : n ≥ 3) :
    ∃ k : ℕ, k ≥ 3 ∧ pair_threshold n = 2 / k := by
  use n, h
  exact pair_threshold_formula n (by omega)

/-- Δ(n) = 2/(n(n+1)). -/
theorem threshold_gap (n : ℕ) (h : n ≥ 3) :
    pair_threshold n - pair_threshold (n + 1) = 2 / (n * (n + 1)) := by
  unfold pair_threshold
  have h_gap := mass_gap n h
  have h_double : 2 * mass_of_cycle n - 2 * mass_of_cycle (n + 1) =
                  2 * (mass_of_cycle n - mass_of_cycle (n + 1)) := by ring
  rw [h_double, h_gap]
  ring

/-! ## Connection to Planck Scale -/

/-- 2/3 < √(1/2) ≈ 0.707. -/
theorem genesis_below_planck_energy : genesis_threshold < planck_energy := by
  rw [genesis_threshold_value]
  unfold planck_energy hbar c G
  simp only [one_mul, one_pow]
  have h_sq : (2 / 3 : ℝ)^2 < (1 / 2 : ℝ) := by norm_num
  have h_lhs_pos : (0 : ℝ) < 2 / 3 := by norm_num
  have h_sqrt_pos : (0 : ℝ) < Real.sqrt (1 / 2) := Real.sqrt_pos.mpr (by norm_num)
  rw [← Real.sqrt_sq (le_of_lt h_lhs_pos)]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) h_sq

/-- genesis / E_P = (2√2)/3 ≈ 0.943. -/
theorem genesis_planck_ratio : genesis_threshold / planck_energy = 2 * Real.sqrt 2 / 3 := by
  rw [genesis_threshold_value]
  unfold planck_energy hbar c G
  simp only [one_mul, one_pow]
  have h_sqrt : Real.sqrt (1 / 2) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  rw [h_sqrt]
  have h_sqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp [h_sqrt2_ne]

theorem energy_conservation_production (n : ℕ) (_h : n ≥ 3) :
    pair_threshold n = mass_of_cycle n + mass_of_cycle n := by
  unfold pair_threshold
  ring

/-- Summary theorem. -/
theorem the_pair_production_correspondence :
    (genesis_threshold = 2 / 3) ∧
    (∀ n : ℕ, n ≥ 3 → pair_threshold n ≤ genesis_threshold) ∧
    (pair_threshold 3 = genesis_threshold) ∧
    (genesis_threshold < planck_energy) ∧
    (genesis_threshold > 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact genesis_threshold_value
  · exact genesis_is_minimum
  · rfl
  · exact genesis_below_planck_energy
  · rw [genesis_threshold_value]; norm_num

end Diaspora.Dynamics.PairProduction
