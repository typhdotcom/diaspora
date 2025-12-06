/-
# The Threshold-Topology Correspondence

This file proves the fundamental relationship between the breaking threshold C_max
and the granularity of stable topology.

## Core Insight

The Dehn twist on an n-cycle has:
- Total energy: 1/n (proven in Twist.lean)
- Per-edge value: 1/n (n edges, each contributing equally)
- Per-edge strain: (1/n)²

For a cycle to be stable, all edges must have strain ≤ C_max. Thus:
  stable ⟺ (1/n)² ≤ C_max ⟺ n ≥ 1/√C_max

This determines a **critical cycle length**: the minimum cycle that can exist
stably for a given threshold. Cycles shorter than critical will break.

## Philosophical Interpretation

The breaking threshold C_max acts as a "resolution limit" for topology:

- **High threshold** (large C_max): Even short cycles (triangles) are stable.
  The universe supports fine-grained, localized paradox.

- **Low threshold** (small C_max): Only long cycles survive.
  Paradox must be spread over many edges to avoid breaking.

- **Zero threshold**: No cycles can exist stably.
  The universe is forced into the classical vacuum.

This is the **granularity of paradox**: the universe's tolerance for contradiction
determines the minimum scale at which topology can manifest.

As the threshold decreases, the universe coarsens - unable to sustain short cycles,
it must either distribute frustration over longer paths or resolve it entirely.
-/

import Diaspora.Dynamics.Transition
import Diaspora.Hodge.Twist

open BigOperators Diaspora.Core Diaspora.Hodge Diaspora.Dynamics

namespace Diaspora.Dynamics.Stability

variable {n : ℕ} [Fintype (Fin n)] [NeZero n]

/-! ## Per-Edge Strain of the Dehn Twist -/

/-- The per-edge strain of a Dehn twist: value² = (1/n)².

This is the strain on each edge when the optimal potential is achieved.
For harmonic forms, the optimal potential makes the exact part zero,
leaving only the harmonic contribution. -/
theorem dehn_twist_per_edge_strain (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3)
    (i : Fin n) :
    ((dehn_twist cycle).val i (cycle.next i))^2 = 1 / n^2 := by
  rw [dehn_twist_constant cycle h_n_ge_3 i]
  ring

/-- The sum of per-edge strains equals total energy 1/n.

Note: n × (1/n)² = 1/n. This follows from dehn_twist_energy,
which shows the total norm squared is 1/n. -/
theorem dehn_twist_total_strain_eq_energy (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3) :
    norm_sq (dehn_twist cycle) = 1 / n := dehn_twist_energy cycle h_n_ge_3

/-! ## The Critical Cycle Length -/

/-- The critical cycle length for a given threshold.

For the canonical Dehn twist to be stable (all per-edge strains ≤ C_max),
we need (1/n)² ≤ C_max, i.e., n ≥ 1/√C_max.

This is the minimum cycle length that CAN be stable. -/
noncomputable def criticalCycleLength (C_max : ℝ) : ℕ :=
  if C_max ≤ 0 then 0
  else ⌈1 / Real.sqrt C_max⌉₊

/-- For positive threshold, critical length is the ceiling of 1/√C_max. -/
lemma criticalCycleLength_pos (C_max : ℝ) (h_pos : C_max > 0) :
    criticalCycleLength C_max = ⌈1 / Real.sqrt C_max⌉₊ := by
  unfold criticalCycleLength
  simp only [not_le.mpr h_pos, ↓reduceIte]

/-! ## Instability of Short Cycles -/

/-- **Short Cycle Instability**: If n < critical length, the Dehn twist has
per-edge strain exceeding C_max.

Cycles shorter than the critical length cannot sustain their canonical
harmonic form - some edge will break. -/
theorem short_cycle_unstable (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3)
    (C_max : ℝ) (h_pos : C_max > 0)
    (h_short : n < criticalCycleLength C_max) :
    ∃ i : Fin n, ((dehn_twist cycle).val i (cycle.next i))^2 > C_max := by
  -- All edges have the same per-edge strain
  have h_strain := dehn_twist_per_edge_strain cycle h_n_ge_3
  -- Just need to show 1/n² > C_max, then pick any i
  suffices h : (1 : ℝ) / n^2 > C_max by
    use ⟨0, by omega⟩
    rw [h_strain]
    exact h
  -- From h_short: n < ⌈1/√C_max⌉₊
  rw [criticalCycleLength_pos C_max h_pos] at h_short
  -- n < ⌈1/√C_max⌉₊ implies n ≤ 1/√C_max - 1 + 1 = 1/√C_max (ceiling property)
  have h_sqrt_pos : Real.sqrt C_max > 0 := Real.sqrt_pos.mpr h_pos
  have h_inv_pos : 1 / Real.sqrt C_max > 0 := by positivity
  -- n < ⌈x⌉₊ means n < x or n ≤ x - 1 < x for x > 0
  have h_lt : (n : ℝ) < 1 / Real.sqrt C_max := by
    have := Nat.lt_ceil.mp h_short
    exact this
  -- Now: n < 1/√C_max implies n² < 1/C_max implies C_max < 1/n²
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
  -- n² < 1/C_max implies 1/n² > C_max
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

/-! ## Stability of Long Cycles -/

/-- **Long Cycle Stability**: If n ≥ critical length, the Dehn twist has
all per-edge strains ≤ C_max.

Cycles at or longer than the critical length CAN sustain their canonical
harmonic form without any edge breaking. -/
theorem long_cycle_stable (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3)
    (C_max : ℝ) (h_pos : C_max > 0)
    (h_long : n ≥ criticalCycleLength C_max) :
    ∀ i : Fin n, ((dehn_twist cycle).val i (cycle.next i))^2 ≤ C_max := by
  intro i
  rw [dehn_twist_per_edge_strain cycle h_n_ge_3 i]
  -- Need to show: 1/n² ≤ C_max
  rw [criticalCycleLength_pos C_max h_pos] at h_long
  -- n ≥ ⌈1/√C_max⌉₊ implies n ≥ 1/√C_max
  have h_sqrt_pos : Real.sqrt C_max > 0 := Real.sqrt_pos.mpr h_pos
  have h_ge : (n : ℝ) ≥ 1 / Real.sqrt C_max := by
    have := Nat.le_ceil (1 / Real.sqrt C_max)
    calc (n : ℝ) ≥ ⌈1 / Real.sqrt C_max⌉₊ := Nat.cast_le.mpr h_long
      _ ≥ 1 / Real.sqrt C_max := this
  -- n ≥ 1/√C_max implies n² ≥ 1/C_max implies 1/n² ≤ C_max
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
  -- n² ≥ 1/C_max implies 1/n² ≤ C_max
  have h_n_sq_pos : (n : ℝ)^2 > 0 := by positivity
  rw [div_le_iff₀ h_n_sq_pos]
  calc 1 = C_max * (1 / C_max) := by field_simp
    _ ≤ C_max * (n : ℝ)^2 := by
        apply mul_le_mul_of_nonneg_left h_step1 (le_of_lt h_pos)

/-! ## The Threshold-Topology Correspondence -/

/-- **Triangle Threshold**: Triangles (n=3) are stable iff C_max ≥ 1/9.

The triangle is the shortest possible cycle, requiring the highest threshold. -/
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

/-- **Coarsening Under Threshold Decrease**: Lower thresholds allow only longer cycles.

If C₁ < C₂, then criticalCycleLength C₁ ≥ criticalCycleLength C₂.
As tolerance decreases, the minimum stable cycle length increases. -/
theorem threshold_monotonicity (C₁ C₂ : ℝ) (h₁ : C₁ > 0) (h₂ : C₂ > 0) (h_lt : C₁ < C₂) :
    criticalCycleLength C₁ ≥ criticalCycleLength C₂ := by
  rw [criticalCycleLength_pos C₁ h₁, criticalCycleLength_pos C₂ h₂]
  apply Nat.ceil_mono
  -- 1/√C₁ ≥ 1/√C₂ when C₁ < C₂
  have h_sqrt_lt : Real.sqrt C₁ < Real.sqrt C₂ := Real.sqrt_lt_sqrt (le_of_lt h₁) h_lt
  have h_sqrt₁_pos : Real.sqrt C₁ > 0 := Real.sqrt_pos.mpr h₁
  have h_sqrt₂_pos : Real.sqrt C₂ > 0 := Real.sqrt_pos.mpr h₂
  exact one_div_le_one_div_of_le h_sqrt₁_pos (le_of_lt h_sqrt_lt)

/-- **Classical Limit**: As C_max → 0⁺, critical length → ∞.

In the limit of zero threshold, no finite cycle can be stable.
The universe is forced into the classical (tree-like) vacuum.

Formally: For any desired minimum cycle length N, there exists a threshold ε
such that any smaller threshold requires cycles longer than N. -/
theorem zero_threshold_classical (N : ℕ) (h_N : N ≥ 3) :
    ∃ ε : ℝ, ε > 0 ∧ ∀ C_max : ℝ, 0 < C_max → C_max ≤ ε → criticalCycleLength C_max ≥ N := by
  -- Choose ε = 1/N² - this is the per-edge strain threshold for an N-cycle
  have h_N_pos : (N : ℝ) > 0 := Nat.cast_pos.mpr (by omega : N > 0)
  use 1 / (N : ℝ)^2
  constructor
  · have h_N_sq_pos : (N : ℝ)^2 > 0 := by positivity
    exact one_div_pos.mpr h_N_sq_pos
  · intro C_max h_pos h_small
    rw [criticalCycleLength_pos C_max h_pos]
    -- Need to show: ⌈1/√C_max⌉₊ ≥ N
    -- From C_max ≤ 1/N², we get √C_max ≤ 1/N, so 1/√C_max ≥ N
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
    -- ⌈x⌉₊ ≥ N when x ≥ N
    have h_ceil_ge_x := Nat.le_ceil (1 / Real.sqrt C_max)
    have h_N_le_ceil : (N : ℝ) ≤ ⌈1 / Real.sqrt C_max⌉₊ :=
      le_trans h_inv_bound h_ceil_ge_x
    exact Nat.cast_le.mp h_N_le_ceil

/-! ## The Minimum Paradox Principle -/

/-- **The Minimum Paradox**: Among all cycles, the triangle requires the highest threshold.

This is the dual of "triangles have maximum per-cycle energy":
- Total energy 1/n decreases with n (longer cycles are cheaper)
- Per-edge strain (1/n)² decreases with n (longer cycles are more stable)

The triangle is the "heaviest" paradox - hardest to sustain, first to break. -/
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

/-- **Long Cycles Approach Stability**: As n → ∞, per-edge strain → 0.

In the limit, arbitrarily long cycles are stable for any positive threshold.
This is why the universe can always "spread out" its paradox to survive. -/
theorem long_cycle_limit (ε : ℝ) (h_ε : ε > 0) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (1 : ℝ) / n^2 < ε := by
  -- Choose N = ⌈1/√ε⌉₊ + 1
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
  -- n > 1/√ε implies n² > 1/ε implies 1/n² < ε
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
