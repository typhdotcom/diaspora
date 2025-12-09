import Diaspora.Dynamics.Transition
import Diaspora.Hodge.Twist

open BigOperators Diaspora.Core Diaspora.Hodge Diaspora.Dynamics

namespace Diaspora.Dynamics.Stability

variable {n : ℕ} [Fintype (Fin n)] [NeZero n]

/-! ## Per-Edge Strain -/

theorem dehn_twist_per_edge_strain (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3)
    (i : Fin n) :
    ((dehn_twist cycle).val i (cycle.next i))^2 = 1 / n^2 := by
  rw [dehn_twist_constant cycle h_n_ge_3 i]
  ring

theorem dehn_twist_total_strain_eq_energy (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3) :
    norm_sq (dehn_twist cycle) = 1 / n := dehn_twist_energy cycle h_n_ge_3

/-! ## Critical Cycle Length -/

noncomputable def criticalCycleLength (C_max : ℝ) : ℕ :=
  if C_max ≤ 0 then 0
  else ⌈1 / Real.sqrt C_max⌉₊

lemma criticalCycleLength_pos (C_max : ℝ) (h_pos : C_max > 0) :
    criticalCycleLength C_max = ⌈1 / Real.sqrt C_max⌉₊ := by
  unfold criticalCycleLength
  simp only [not_le.mpr h_pos, ↓reduceIte]

/-! ## Short Cycle Instability -/

theorem short_cycle_unstable (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3)
    (C_max : ℝ) (h_pos : C_max > 0)
    (h_short : n < criticalCycleLength C_max) :
    ∃ i : Fin n, ((dehn_twist cycle).val i (cycle.next i))^2 > C_max := by
  have h_strain := dehn_twist_per_edge_strain cycle h_n_ge_3
  suffices h : (1 : ℝ) / n^2 > C_max by
    use ⟨0, by omega⟩
    rw [h_strain]
    exact h
  rw [criticalCycleLength_pos C_max h_pos] at h_short
  have h_sqrt_pos : Real.sqrt C_max > 0 := Real.sqrt_pos.mpr h_pos
  have h_inv_pos : 1 / Real.sqrt C_max > 0 := by positivity
  have h_lt : (n : ℝ) < 1 / Real.sqrt C_max := by
    have := Nat.lt_ceil.mp h_short
    exact this
  have h_n_pos : (n : ℝ) > 0 := by
    have : n ≥ 3 := h_n_ge_3
    positivity
  have h_step1 : n^2 < (1 / Real.sqrt C_max)^2 := by
    apply sq_lt_sq'
    · linarith
    · exact h_lt
  have h_step2 : (1 / Real.sqrt C_max)^2 = 1 / C_max := by
    rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt h_pos)]
  rw [h_step2] at h_step1
  have h_n_sq_pos : (n : ℝ)^2 > 0 := by positivity
  calc C_max
      < 1 / (n : ℝ)^2 := by
        rw [lt_div_iff₀ h_n_sq_pos]
        calc C_max * n^2 < (1 / C_max) * C_max := by
              have : (n : ℝ)^2 < 1 / C_max := h_step1
              have hC_pos : C_max > 0 := h_pos
              nlinarith
          _ = 1 := by field_simp
    _ = 1 / n^2 := rfl

/-! ## Long Cycle Stability -/

theorem long_cycle_stable (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3)
    (C_max : ℝ) (h_pos : C_max > 0)
    (h_long : n ≥ criticalCycleLength C_max) :
    ∀ i : Fin n, ((dehn_twist cycle).val i (cycle.next i))^2 ≤ C_max := by
  intro i
  rw [dehn_twist_per_edge_strain cycle h_n_ge_3 i]
  rw [criticalCycleLength_pos C_max h_pos] at h_long
  have h_sqrt_pos : Real.sqrt C_max > 0 := Real.sqrt_pos.mpr h_pos
  have h_ge : (n : ℝ) ≥ 1 / Real.sqrt C_max := by
    have := Nat.le_ceil (1 / Real.sqrt C_max)
    calc (n : ℝ) ≥ ⌈1 / Real.sqrt C_max⌉₊ := Nat.cast_le.mpr h_long
      _ ≥ 1 / Real.sqrt C_max := this
  have h_n_pos : (n : ℝ) > 0 := by
    have : n ≥ 3 := h_n_ge_3
    positivity
  have h_step1 : (n : ℝ)^2 ≥ (1 / Real.sqrt C_max)^2 := by
    apply sq_le_sq'
    · have : 1 / Real.sqrt C_max > 0 := by positivity
      linarith
    · exact h_ge
  have h_step2 : (1 / Real.sqrt C_max)^2 = 1 / C_max := by
    rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt h_pos)]
  rw [h_step2] at h_step1
  have h_n_sq_pos : (n : ℝ)^2 > 0 := by positivity
  rw [div_le_iff₀ h_n_sq_pos]
  calc 1 = C_max * (1 / C_max) := by field_simp
    _ ≤ C_max * (n : ℝ)^2 := by
        apply mul_le_mul_of_nonneg_left h_step1 (le_of_lt h_pos)

/-! ## Threshold-Topology Correspondence -/

theorem triangle_threshold (cycle : SimpleCycle 3) (C_max : ℝ) :
    (∀ i : Fin 3, ((dehn_twist cycle).val i (cycle.next i))^2 ≤ C_max) ↔
    C_max ≥ 1 / 9 := by
  constructor
  · intro h
    have h3 : (3 : ℕ) ≥ 3 := le_refl 3
    have h_strain := dehn_twist_per_edge_strain cycle h3 ⟨0, by omega⟩
    have h_le := h ⟨0, by omega⟩
    simp only [h_strain] at h_le
    have h_eq : (1 : ℝ) / 3 ^ 2 = 1 / 9 := by norm_num
    linarith
  · intro h_ge i
    have h3 : (3 : ℕ) ≥ 3 := le_refl 3
    rw [dehn_twist_per_edge_strain cycle h3 i]
    calc (1 : ℝ) / 3^2 = 1 / 9 := by norm_num
      _ ≤ C_max := h_ge

theorem threshold_monotonicity (C₁ C₂ : ℝ) (h₁ : C₁ > 0) (h₂ : C₂ > 0) (h_lt : C₁ < C₂) :
    criticalCycleLength C₁ ≥ criticalCycleLength C₂ := by
  rw [criticalCycleLength_pos C₁ h₁, criticalCycleLength_pos C₂ h₂]
  apply Nat.ceil_mono
  have h_sqrt_lt : Real.sqrt C₁ < Real.sqrt C₂ := Real.sqrt_lt_sqrt (le_of_lt h₁) h_lt
  have h_sqrt₁_pos : Real.sqrt C₁ > 0 := Real.sqrt_pos.mpr h₁
  have h_sqrt₂_pos : Real.sqrt C₂ > 0 := Real.sqrt_pos.mpr h₂
  exact one_div_le_one_div_of_le h_sqrt₁_pos (le_of_lt h_sqrt_lt)

theorem zero_threshold_classical (N : ℕ) (h_N : N ≥ 3) :
    ∃ ε : ℝ, ε > 0 ∧ ∀ C_max : ℝ, 0 < C_max → C_max ≤ ε → criticalCycleLength C_max ≥ N := by
  have h_N_pos : (N : ℝ) > 0 := Nat.cast_pos.mpr (by omega : N > 0)
  use 1 / (N : ℝ)^2
  constructor
  · have h_N_sq_pos : (N : ℝ)^2 > 0 := by positivity
    exact one_div_pos.mpr h_N_sq_pos
  · intro C_max h_pos h_small
    rw [criticalCycleLength_pos C_max h_pos]
    have h_sqrt_bound : Real.sqrt C_max ≤ 1 / N := by
      have h1 : Real.sqrt C_max ≤ Real.sqrt (1 / (N : ℝ)^2) :=
        Real.sqrt_le_sqrt h_small
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
          Real.sqrt_sq (by linarith : (N : ℝ) ≥ 0)] at h1
      exact h1
    have h_inv_bound : 1 / Real.sqrt C_max ≥ N := by
      have h_sqrt_pos : Real.sqrt C_max > 0 := Real.sqrt_pos.mpr h_pos
      have h_inv_N_pos : 1 / (N : ℝ) > 0 := one_div_pos.mpr h_N_pos
      calc 1 / Real.sqrt C_max
          ≥ 1 / (1 / (N : ℝ)) := one_div_le_one_div_of_le h_sqrt_pos h_sqrt_bound
        _ = N := by field_simp
    have h_ceil_ge_x := Nat.le_ceil (1 / Real.sqrt C_max)
    have h_N_le_ceil : (N : ℝ) ≤ ⌈1 / Real.sqrt C_max⌉₊ :=
      le_trans h_inv_bound h_ceil_ge_x
    exact Nat.cast_le.mp h_N_le_ceil

/-! ## Minimum Paradox Principle -/

theorem triangle_is_minimum_paradox (m : ℕ) (h_m : m ≥ 3) :
    (1 : ℝ) / 3^2 ≥ 1 / m^2 := by
  have h3 : (3 : ℝ) ≥ 0 := by norm_num
  have hm : (m : ℝ) ≥ 3 := Nat.cast_le.mpr h_m
  have h_m_pos : (m : ℝ) > 0 := by linarith
  have h_sq_le : (3 : ℝ)^2 ≤ m^2 := by
    apply sq_le_sq'
    · linarith
    · linarith
  have h3_sq_pos : (3 : ℝ)^2 > 0 := by norm_num
  have hm_sq_pos : (m : ℝ)^2 > 0 := by positivity
  exact one_div_le_one_div_of_le h3_sq_pos h_sq_le

theorem long_cycle_limit (ε : ℝ) (h_ε : ε > 0) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (1 : ℝ) / n^2 < ε := by
  use ⌈1 / Real.sqrt ε⌉₊ + 1
  intro n h_n
  have h_sqrt_pos : Real.sqrt ε > 0 := Real.sqrt_pos.mpr h_ε
  have h_N_ge : (⌈1 / Real.sqrt ε⌉₊ : ℝ) ≥ 1 / Real.sqrt ε := Nat.le_ceil _
  have h_n_ge_cast : (n : ℝ) ≥ (⌈1 / Real.sqrt ε⌉₊ + 1 : ℕ) := by
    exact Nat.cast_le.mpr h_n
  have h_n_gt : (n : ℝ) > 1 / Real.sqrt ε := by
    calc (n : ℝ) ≥ (⌈1 / Real.sqrt ε⌉₊ + 1 : ℕ) := h_n_ge_cast
      _ = ⌈1 / Real.sqrt ε⌉₊ + 1 := by simp
      _ > ⌈1 / Real.sqrt ε⌉₊ := by linarith
      _ ≥ 1 / Real.sqrt ε := h_N_ge
  have h_n_pos : (n : ℝ) > 0 := by
    have : 1 / Real.sqrt ε > 0 := by positivity
    linarith
  have h_sq_gt : (n : ℝ)^2 > (1 / Real.sqrt ε)^2 := by
    apply sq_lt_sq'
    · have : 1 / Real.sqrt ε > 0 := by positivity
      linarith
    · exact h_n_gt
  have h_one_over_sqrt_sq : (1 / Real.sqrt ε)^2 = 1 / ε := by
    rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt h_ε)]
  rw [h_one_over_sqrt_sq] at h_sq_gt
  have h_n_sq_pos : (n : ℝ)^2 > 0 := by positivity
  have h_inv_ε_pos : 1 / ε > 0 := by positivity
  calc (1 : ℝ) / n^2
      < 1 / (1 / ε) := (one_div_lt_one_div h_n_sq_pos h_inv_ε_pos).mpr h_sq_gt
    _ = ε := one_div_one_div ε

end Diaspora.Dynamics.Stability
