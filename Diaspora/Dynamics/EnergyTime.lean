import Diaspora.Dynamics.DeBroglie

/-!
# Energy-Time Uncertainty

Temporal conjugate to position-momentum uncertainty from DeBroglie.lean.

- `period`: T = 1/f = n
- `energy_time_uncertainty`: ΔE × Δt = 1
- `unified_uncertainty`: All four uncertainties related through topology
-/

namespace Diaspora.Dynamics.EnergyTime

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie

/-- Period T = 1/f = n. -/
noncomputable def period (n : ℕ) : ℝ := 1 / frequency n

theorem period_eq_n (n : ℕ) (h : n > 0) : period n = n := by
  unfold period frequency mass_of_cycle
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h)
  field_simp [hn]

theorem period_equals_wavelength (n : ℕ) (h : n > 0) :
    period n = wavelength_real n := by
  rw [period_eq_n n h]
  rfl

noncomputable def energy_uncertainty (n : ℕ) : ℝ := mass_of_cycle n

noncomputable def time_uncertainty (n : ℕ) : ℝ := period n

/-- ΔE × Δt = 1. -/
theorem energy_time_uncertainty (n : ℕ) (h : n > 0) :
    energy_uncertainty n * time_uncertainty n = 1 := by
  unfold energy_uncertainty time_uncertainty
  rw [period_eq_n n h]
  unfold mass_of_cycle
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h)
  field_simp [hn]

/-- n₁ < n₂ implies E(n₁) > E(n₂) and T(n₁) < T(n₂). -/
theorem energy_time_tradeoff (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_lt : n₁ < n₂) :
    energy_uncertainty n₁ > energy_uncertainty n₂ ∧
    time_uncertainty n₁ < time_uncertainty n₂ := by
  constructor
  · unfold energy_uncertainty
    exact mass_decreases_with_length n₁ n₂ (by omega) (by omega) h_lt
  · unfold time_uncertainty
    rw [period_eq_n n₁ (by omega), period_eq_n n₂ (by omega)]
    exact Nat.cast_lt.mpr h_lt

/-- f × T = 1. -/
theorem frequency_period_product (n : ℕ) (h : n > 0) :
    frequency n * period n = 1 := by
  unfold period
  have hf : frequency n ≠ 0 := by
    unfold frequency mass_of_cycle
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h)
    exact one_div_ne_zero hn
  field_simp [hf]

theorem higher_frequency_shorter_period (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_lt : n₁ < n₂) :
    frequency n₁ > frequency n₂ ∧ period n₁ < period n₂ := by
  unfold frequency
  constructor
  · exact mass_decreases_with_length n₁ n₂ (by omega) (by omega) h_lt
  · rw [period_eq_n n₁ (by omega), period_eq_n n₂ (by omega)]
    exact Nat.cast_lt.mpr h_lt

theorem minimum_period : period 3 = 3 := period_eq_n 3 (by omega)

theorem max_energy_min_period : energy_uncertainty 3 = 1/3 := by
  unfold energy_uncertainty mass_of_cycle
  norm_num

/-- Both conjugate pairs: Δx × Δp = 1 and ΔE × Δt = 1. -/
theorem diaspora_uncertainty_relations (n : ℕ) (h : n ≥ 3) :
    position_uncertainty n * momentum_uncertainty n = 1 ∧
    energy_uncertainty n * time_uncertainty n = 1 := by
  constructor
  · exact heisenberg_uncertainty n (by omega)
  · exact energy_time_uncertainty n (by omega)

theorem energy_equals_momentum_uncertainty (n : ℕ) :
    energy_uncertainty n = momentum_uncertainty n := by
  unfold energy_uncertainty momentum_uncertainty momentum
  rfl

theorem time_equals_position_uncertainty (n : ℕ) (h : n > 0) :
    time_uncertainty n = position_uncertainty n := by
  unfold time_uncertainty position_uncertainty
  exact period_equals_wavelength n h

/-- Δx = Δt = n and Δp = ΔE = 1/n. -/
theorem unified_uncertainty (n : ℕ) (h : n ≥ 3) :
    position_uncertainty n = time_uncertainty n ∧
    momentum_uncertainty n = energy_uncertainty n ∧
    position_uncertainty n * momentum_uncertainty n = 1 ∧
    energy_uncertainty n * time_uncertainty n = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (time_equals_position_uncertainty n (by omega)).symm
  · exact (energy_equals_momentum_uncertainty n).symm
  · exact heisenberg_uncertainty n (by omega)
  · exact energy_time_uncertainty n (by omega)

end Diaspora.Dynamics.EnergyTime
