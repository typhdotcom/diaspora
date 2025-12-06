/-
# The Girth-Stability Correspondence

This file extends the stability theory from simple cycles to general graphs,
proving that the **girth** (length of the shortest cycle) determines the
stability threshold.

## Core Theorem

For any connected graph G with girth g:
  G is stable under threshold C_max ⟺ C_max ≥ 1/g²

This directly connects topology (girth) to dynamics (stability threshold).

## Philosophical Interpretation

The girth is the "granularity" of a graph's paradox structure. Just as
the critical cycle length determines which cycles can exist stably,
the girth determines whether a graph can exist stably at all.

A graph with small girth (like K_n with girth 3) requires high tolerance
to sustain its structure. A graph with large girth requires less tolerance.
Trees (girth = ∞) are stable under any positive threshold.

This connects the abstract topological property (girth) to the concrete
physical property (breaking threshold) - topology determines dynamics.
-/

import Diaspora.Dynamics.Stability
import Diaspora.Logic.Classicality.Dimension

set_option linter.unusedSectionVars false

open BigOperators Classical Diaspora.Core Diaspora.Hodge Diaspora.Logic Diaspora.Dynamics

namespace Diaspora.Dynamics.GirthStability

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] [NeZero n]

/-! ## Per-Edge Strain for General Cycles -/

/-- The per-edge strain of a general cycle form: value² = (1/k)² where k is cycle length.

This extends `dehn_twist_per_edge_strain` from SimpleCycle to GeneralCycle. -/
theorem general_cycle_per_edge_strain (c : GeneralCycle n) (i : Fin c.verts.length) :
    ((general_cycle_form c).val (c.vertex i.val) (c.nextVertex i.val))^2 = 1 / c.len^2 := by
  rw [general_cycle_form_constant c i]
  ring

/-- All forward edges of a general cycle have equal per-edge strain. -/
theorem general_cycle_uniform_strain (c : GeneralCycle n) :
    ∀ i j : Fin c.verts.length,
      ((general_cycle_form c).val (c.vertex i.val) (c.nextVertex i.val))^2 =
      ((general_cycle_form c).val (c.vertex j.val) (c.nextVertex j.val))^2 := by
  intro i j
  rw [general_cycle_per_edge_strain c i, general_cycle_per_edge_strain c j]

/-! ## Stability Criterion for General Cycles -/

/-- **Short General Cycle Instability**: A k-cycle with k < critical length is unstable.

The per-edge strain (1/k)² exceeds C_max when k is too small. -/
theorem general_cycle_unstable (c : GeneralCycle n) (C_max : ℝ) (h_pos : C_max > 0)
    (h_short : c.len < Stability.criticalCycleLength C_max) :
    ∃ i : Fin c.verts.length,
      ((general_cycle_form c).val (c.vertex i.val) (c.nextVertex i.val))^2 > C_max := by
  have h_len_ge_3 := c.len_ge_3
  suffices h : (1 : ℝ) / c.len^2 > C_max by
    use ⟨0, by omega⟩
    rw [general_cycle_per_edge_strain]
    exact h
  rw [Stability.criticalCycleLength_pos C_max h_pos] at h_short
  have h_sqrt_pos : Real.sqrt C_max > 0 := Real.sqrt_pos.mpr h_pos
  have h_inv_pos : 1 / Real.sqrt C_max > 0 := by positivity
  have h_lt : (c.len : ℝ) < 1 / Real.sqrt C_max := by
    have := Nat.lt_ceil.mp h_short
    exact this
  have h_len_pos : (c.len : ℝ) > 0 := by
    simp only [GeneralCycle.len]
    have : c.verts.length ≥ 3 := h_len_ge_3
    positivity
  have h_step1 : (c.len : ℝ)^2 < (1 / Real.sqrt C_max)^2 := by
    apply sq_lt_sq'
    · linarith
    · exact h_lt
  have h_step2 : (1 / Real.sqrt C_max)^2 = 1 / C_max := by
    rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt h_pos)]
  rw [h_step2] at h_step1
  have h_len_sq_pos : (c.len : ℝ)^2 > 0 := by positivity
  calc C_max < 1 / (c.len : ℝ)^2 := by
        rw [lt_div_iff₀ h_len_sq_pos]
        calc C_max * c.len^2 < (1 / C_max) * C_max := by
              have : (c.len : ℝ)^2 < 1 / C_max := h_step1
              nlinarith
          _ = 1 := by field_simp
    _ = 1 / c.len^2 := rfl

/-- **Long General Cycle Stability**: A k-cycle with k ≥ critical length is stable.

All per-edge strains are ≤ C_max when k is large enough. -/
theorem general_cycle_stable (c : GeneralCycle n) (C_max : ℝ) (h_pos : C_max > 0)
    (h_long : c.len ≥ Stability.criticalCycleLength C_max) :
    ∀ i : Fin c.verts.length,
      ((general_cycle_form c).val (c.vertex i.val) (c.nextVertex i.val))^2 ≤ C_max := by
  intro i
  rw [general_cycle_per_edge_strain]
  have h_len_ge_3 := c.len_ge_3
  rw [Stability.criticalCycleLength_pos C_max h_pos] at h_long
  have h_sqrt_pos : Real.sqrt C_max > 0 := Real.sqrt_pos.mpr h_pos
  have h_ge : (c.len : ℝ) ≥ 1 / Real.sqrt C_max := by
    have := Nat.le_ceil (1 / Real.sqrt C_max)
    calc (c.len : ℝ) ≥ ⌈1 / Real.sqrt C_max⌉₊ := Nat.cast_le.mpr h_long
      _ ≥ 1 / Real.sqrt C_max := this
  have h_len_pos : (c.len : ℝ) > 0 := by
    simp only [GeneralCycle.len]
    have : c.verts.length ≥ 3 := h_len_ge_3
    positivity
  have h_step1 : (c.len : ℝ)^2 ≥ (1 / Real.sqrt C_max)^2 := by
    apply sq_le_sq'
    · have : 1 / Real.sqrt C_max > 0 := by positivity
      linarith
    · exact h_ge
  have h_step2 : (1 / Real.sqrt C_max)^2 = 1 / C_max := by
    rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt h_pos)]
  rw [h_step2] at h_step1
  have h_len_sq_pos : (c.len : ℝ)^2 > 0 := by positivity
  rw [div_le_iff₀ h_len_sq_pos]
  calc 1 = C_max * (1 / C_max) := by field_simp
    _ ≤ C_max * (c.len : ℝ)^2 := by apply mul_le_mul_of_nonneg_left h_step1 (le_of_lt h_pos)

/-! ## The Girth of a Graph -/

/-- The set of cycle lengths embedded in a graph. -/
def cycleLengths (G : DynamicGraph n) : Set ℕ :=
  { k | ∃ c : GeneralCycle n, c.len = k ∧ generalCycleEmbeddedIn c G }

/-- The girth of a graph is the infimum of embedded cycle lengths.
    Returns 0 if the graph has no cycles (is a forest). -/
noncomputable def girth (G : DynamicGraph n) : ℕ :=
  if h : (cycleLengths G).Nonempty then Nat.find (by
    obtain ⟨k, c, h_len, h_emb⟩ := h
    exact ⟨k, c, h_len, h_emb⟩ : ∃ k : ℕ, ∃ c : GeneralCycle n, c.len = k ∧ generalCycleEmbeddedIn c G)
  else 0

/-- A graph has girth 0 iff it has no embedded cycles (is a forest). -/
theorem girth_zero_iff_acyclic (G : DynamicGraph n) :
    girth G = 0 ↔ ¬∃ c : GeneralCycle n, generalCycleEmbeddedIn c G := by
  unfold girth
  constructor
  · intro h_zero h_exists
    obtain ⟨c, h_emb⟩ := h_exists
    have h_nonempty : (cycleLengths G).Nonempty := ⟨c.len, c, rfl, h_emb⟩
    simp only [h_nonempty, ↓reduceDIte] at h_zero
    have h_find := Nat.find_spec (⟨c.len, c, rfl, h_emb⟩ :
      ∃ k : ℕ, ∃ c : GeneralCycle n, c.len = k ∧ generalCycleEmbeddedIn c G)
    obtain ⟨c', h_len', _⟩ := h_find
    rw [h_zero] at h_len'
    have := c'.len_ge_3
    simp only [GeneralCycle.len] at h_len' this
    omega
  · intro h_not_exists
    have h_empty : ¬(cycleLengths G).Nonempty := by
      intro ⟨k, c, _, h_emb⟩
      exact h_not_exists ⟨c, h_emb⟩
    simp only [h_empty, ↓reduceDIte]

/-- A graph with embedded cycles has positive girth. -/
theorem girth_pos_of_has_cycle (G : DynamicGraph n) (c : GeneralCycle n)
    (h_embedded : generalCycleEmbeddedIn c G) :
    girth G > 0 := by
  have h_exists : ∃ c : GeneralCycle n, generalCycleEmbeddedIn c G := ⟨c, h_embedded⟩
  by_contra h_zero
  push_neg at h_zero
  have h_eq : girth G = 0 := Nat.eq_zero_of_le_zero h_zero
  rw [girth_zero_iff_acyclic] at h_eq
  exact h_eq h_exists

/-- The girth is achieved by some embedded cycle. -/
theorem girth_achieved (G : DynamicGraph n) (h_pos : girth G > 0) :
    ∃ c : GeneralCycle n, c.len = girth G ∧ generalCycleEmbeddedIn c G := by
  have h_exists : ∃ c : GeneralCycle n, generalCycleEmbeddedIn c G := by
    by_contra h_not
    have h_acyclic := girth_zero_iff_acyclic G
    have h_girth_zero := h_acyclic.mpr h_not
    omega
  have h_nonempty : (cycleLengths G).Nonempty := by
    obtain ⟨c, h_emb⟩ := h_exists
    exact ⟨c.len, c, rfl, h_emb⟩
  unfold girth at h_pos ⊢
  simp only [h_nonempty, ↓reduceDIte] at h_pos ⊢
  have h_spec := Nat.find_spec (⟨(choose h_exists).len, choose h_exists, rfl, choose_spec h_exists⟩ :
    ∃ k : ℕ, ∃ c : GeneralCycle n, c.len = k ∧ generalCycleEmbeddedIn c G)
  obtain ⟨c, h_len, h_emb⟩ := h_spec
  exact ⟨c, h_len, h_emb⟩

/-- Every embedded cycle has length ≥ girth. -/
theorem cycle_length_ge_girth (G : DynamicGraph n) (c : GeneralCycle n)
    (h_embedded : generalCycleEmbeddedIn c G) :
    c.len ≥ girth G := by
  have h_pos := girth_pos_of_has_cycle G c h_embedded
  have h_nonempty : (cycleLengths G).Nonempty := ⟨c.len, c, rfl, h_embedded⟩
  unfold girth
  simp only [h_nonempty, ↓reduceDIte]
  exact Nat.find_min' _ ⟨c, rfl, h_embedded⟩

/-- Girth is at least 3 when positive (cycles have at least 3 vertices). -/
theorem girth_ge_three (G : DynamicGraph n) (h_pos : girth G > 0) :
    girth G ≥ 3 := by
  obtain ⟨c, h_len, _⟩ := girth_achieved G h_pos
  rw [← h_len]
  exact c.len_ge_3

/-! ## The Girth-Stability Correspondence -/

/-- **The Girth-Stability Correspondence (Unstable Direction)**:
    If girth < critical length, the graph has at least one overstressed edge.

    The shortest cycle determines the minimum threshold for stability. -/
theorem girth_unstable (G : DynamicGraph n) (C_max : ℝ) (h_pos : C_max > 0)
    (h_has_cycle : girth G > 0)
    (h_girth_short : girth G < Stability.criticalCycleLength C_max) :
    ∃ (c : GeneralCycle n) (i : Fin c.verts.length),
      generalCycleEmbeddedIn c G ∧
      ((general_cycle_form c).val (c.vertex i.val) (c.nextVertex i.val))^2 > C_max := by
  obtain ⟨c, h_len, h_embedded⟩ := girth_achieved G h_has_cycle
  have h_c_short : c.len < Stability.criticalCycleLength C_max := by
    rw [h_len]; exact h_girth_short
  obtain ⟨i, h_strain⟩ := general_cycle_unstable c C_max h_pos h_c_short
  exact ⟨c, i, h_embedded, h_strain⟩

/-- **The Girth-Stability Correspondence (Stable Direction)**:
    If girth ≥ critical length, all cycle edges are within threshold.

    The shortest cycle being stable implies all cycles are stable. -/
theorem girth_stable (G : DynamicGraph n) (C_max : ℝ) (h_pos : C_max > 0)
    (h_girth_long : girth G ≥ Stability.criticalCycleLength C_max) :
    ∀ (c : GeneralCycle n), generalCycleEmbeddedIn c G →
      ∀ (i : Fin c.verts.length),
      ((general_cycle_form c).val (c.vertex i.val) (c.nextVertex i.val))^2 ≤ C_max := by
  intro c h_embedded i
  have h_c_ge_girth := cycle_length_ge_girth G c h_embedded
  have h_c_long : c.len ≥ Stability.criticalCycleLength C_max := by
    exact Nat.le_trans h_girth_long h_c_ge_girth
  exact general_cycle_stable c C_max h_pos h_c_long i

/-- **The Threshold-Girth Bound**: For a graph with girth g, the minimum threshold
    required for stability is 1/g². -/
theorem minimum_stable_threshold (G : DynamicGraph n) (h_girth_pos : girth G > 0) (C_max : ℝ) :
    (∀ (c : GeneralCycle n), generalCycleEmbeddedIn c G →
       ∀ (i : Fin c.verts.length),
       ((general_cycle_form c).val (c.vertex i.val) (c.nextVertex i.val))^2 ≤ C_max) ↔
    C_max ≥ 1 / (girth G)^2 := by
  constructor
  · intro h_stable
    obtain ⟨c, h_len, h_embedded⟩ := girth_achieved G h_girth_pos
    have h_strain := h_stable c h_embedded ⟨0, by
      have := c.len_ge_3
      omega⟩
    rw [general_cycle_per_edge_strain] at h_strain
    simp only [h_len] at h_strain
    exact h_strain
  · intro h_threshold_ok c h_embedded i
    rw [general_cycle_per_edge_strain]
    have h_c_ge_girth := cycle_length_ge_girth G c h_embedded
    have h_girth_real_pos : (girth G : ℝ) > 0 := Nat.cast_pos.mpr h_girth_pos
    have h_c_len_pos : (c.len : ℝ) > 0 := by
      have := c.len_ge_3
      simp only [GeneralCycle.len]
      positivity
    calc (1 : ℝ) / c.len^2 ≤ 1 / (girth G)^2 := by
          apply one_div_le_one_div_of_le
          · positivity
          · apply sq_le_sq'
            · linarith
            · exact Nat.cast_le.mpr h_c_ge_girth
      _ ≤ C_max := h_threshold_ok

/-! ## Corollaries -/

/-- **Classical Graphs are Stable**: Graphs with no cycles (girth = 0) are stable
    under any positive threshold. -/
theorem classical_always_stable (G : DynamicGraph n) (C_max : ℝ)
    (h_classical : girth G = 0) :
    ∀ (c : GeneralCycle n), generalCycleEmbeddedIn c G →
      ∀ (i : Fin c.verts.length),
      ((general_cycle_form c).val (c.vertex i.val) (c.nextVertex i.val))^2 ≤ C_max := by
  intro c h_embedded
  exfalso
  rw [girth_zero_iff_acyclic] at h_classical
  exact h_classical ⟨c, h_embedded⟩

/-- **Complete Graphs Require Maximum Tolerance**: K_n has girth 3 when n ≥ 3,
    so it requires C_max ≥ 1/9 to be stable. -/
theorem complete_graph_threshold (G : DynamicGraph n)
    (h_has_triangle : ∃ c : GeneralCycle n, c.len = 3 ∧ generalCycleEmbeddedIn c G)
    (C_max : ℝ) :
    (∀ (c : GeneralCycle n), generalCycleEmbeddedIn c G →
       ∀ (i : Fin c.verts.length),
       ((general_cycle_form c).val (c.vertex i.val) (c.nextVertex i.val))^2 ≤ C_max) ↔
    C_max ≥ 1 / 9 := by
  obtain ⟨c₀, h_len₀, h_emb₀⟩ := h_has_triangle
  have h_girth_pos : girth G > 0 := girth_pos_of_has_cycle G c₀ h_emb₀
  have h_girth_3 : girth G = 3 := by
    have h_ge := girth_ge_three G h_girth_pos
    have h_le := cycle_length_ge_girth G c₀ h_emb₀
    rw [h_len₀] at h_le
    omega
  rw [minimum_stable_threshold G h_girth_pos C_max, h_girth_3]
  norm_num

/-- **Shorter Girth Means Higher Threshold**: If G₁ has smaller girth than G₂,
    then G₁ requires a higher threshold to be stable. -/
theorem shorter_girth_higher_threshold (G₁ G₂ : DynamicGraph n)
    (h₁_pos : girth G₁ > 0) (h₂_pos : girth G₂ > 0)
    (h_shorter : girth G₁ < girth G₂) :
    (1 : ℝ) / (girth G₁)^2 > 1 / (girth G₂)^2 := by
  have h₁_cast : (girth G₁ : ℝ) > 0 := Nat.cast_pos.mpr h₁_pos
  have h₂_cast : (girth G₂ : ℝ) > 0 := Nat.cast_pos.mpr h₂_pos
  have h_lt_cast : (girth G₁ : ℝ) < girth G₂ := Nat.cast_lt.mpr h_shorter
  have h_sq_lt : (girth G₁ : ℝ)^2 < (girth G₂)^2 := by
    apply sq_lt_sq'
    · linarith
    · exact h_lt_cast
  exact one_div_lt_one_div_of_lt (by positivity : (girth G₁ : ℝ)^2 > 0) h_sq_lt

end Diaspora.Dynamics.GirthStability
