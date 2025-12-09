import Diaspora.Dynamics.SpeedOfLight

/-!
# Action Quantization

S = E × T = (1/n) × n = 1 for all cycles. Every defect carries exactly one
quantum of action, regardless of size.
-/

namespace Diaspora.Dynamics.Action

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.EnergyTime
open Diaspora.Dynamics.SpeedOfLight

/-! ## Action Definition -/

/-- S = E × T -/
noncomputable def action (n : ℕ) : ℝ := mass_of_cycle n * period n

/-! ## The Fundamental Quantization Theorem -/

/-- S = E × T = (1/n) × n = 1 -/
theorem action_of_cycle (n : ℕ) (h : n > 0) : action n = 1 := by
  unfold action
  rw [period_eq_n n h]
  unfold mass_of_cycle
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h)
  field_simp [hn]

theorem action_is_universal (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    action n₁ = action n₂ := by
  rw [action_of_cycle n₁ (by omega), action_of_cycle n₂ (by omega)]

/-! ## Connection to Planck's Constant -/

/-- ℏ = 1 -/
noncomputable def planck_constant : ℝ := action 3

theorem planck_constant_eq_one : planck_constant = 1 :=
  action_of_cycle 3 (by omega)

theorem action_equals_planck (n : ℕ) (h : n ≥ 3) :
    action n = planck_constant := by
  rw [planck_constant_eq_one, action_of_cycle n (by omega)]

/-! ## Action as a Topological Invariant -/

theorem action_is_topological (n : ℕ) (h : n ≥ 3) :
    action n = 1 := action_of_cycle n (by omega)

theorem minimum_action : action 3 = 1 := action_of_cycle 3 (by omega)

/-! ## Action-Energy-Time Relations -/

theorem action_decomposition (n : ℕ) (h : n ≥ 3) :
    action n = mass_of_cycle n * period n ∧
    action n = momentum n * wavelength_real n := by
  constructor
  · rfl
  · rw [action_of_cycle n (by omega)]
    exact (momentum_wavelength_product n (by omega)).symm

theorem energy_from_action (n : ℕ) (h : n ≥ 3) :
    mass_of_cycle n = action n / period n := by
  rw [action_of_cycle n (by omega), period_eq_n n (by omega)]
  unfold mass_of_cycle
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hn]

theorem period_from_action (n : ℕ) (h : n ≥ 3) :
    period n = action n / mass_of_cycle n := by
  rw [action_of_cycle n (by omega)]
  unfold mass_of_cycle
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hn]
  exact period_eq_n n (by omega)

/-! ## The Correspondence Principle -/

/-- Summary: S = E × T = p × λ = ℏ = 1 -/
theorem the_action_correspondence (n : ℕ) (h : n ≥ 3) :
    action n = 1 ∧
    action n = mass_of_cycle n * period n ∧
    momentum n * wavelength_real n = 1 ∧
    action n = planck_constant ∧
    planck_constant = 1 := by
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · exact action_of_cycle n (by omega)
  · exact momentum_wavelength_product n (by omega)
  · exact action_equals_planck n h
  · exact planck_constant_eq_one

/-! ## Multiple Cycles -/

theorem additive_action (k : ℕ) :
    k * action 3 = k := by
  rw [action_of_cycle 3 (by omega)]
  ring

theorem action_exact (n : ℕ) (h : n > 0) :
    mass_of_cycle n * period n = 1 := action_of_cycle n h

theorem diaspora_action_principle (n : ℕ) (h : n ≥ 3) :
    action n = 1 ∧
    (∀ m : ℕ, m ≥ 3 → action m = action n) ∧
    action n = planck_constant := by
  refine ⟨action_of_cycle n (by omega), ?_, action_equals_planck n h⟩
  intro m hm
  exact action_is_universal m n hm h

end Diaspora.Dynamics.Action
