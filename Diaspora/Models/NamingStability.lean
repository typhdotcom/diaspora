/-
# The Mass and Stability of Meaning

This file proves the deep connection between Naming (semantic reference) and
Stability (dynamical persistence). The synthesis:

**Names require tolerance for paradox.**

## The Argument

1. Naming creates a 3-cycle (P-M-S1) — proven in Naming.lean
2. The harmonic form on this cycle has energy 1/3 — the "mass of the name"
3. For the cycle to be stable, we need C_max ≥ 1/9 — from Stability.lean
4. Therefore: **To sustain meaning, the universe must tolerate paradox.**

## Philosophical Interpretation

In a universe with low tolerance (small C_max), short cycles break. This means:
- Names with small referential loops cannot persist
- Only "diffuse" references (long cycles) survive
- In the limit C_max → 0, no names can exist (pure classical vacuum)

The **mass of a name** (1/3 for the simplest reference) is the irreducible energy
cost of creating a distinction. The **tolerance threshold** (1/9) is the minimum
"openness to contradiction" required for meaning to exist.

This connects:
- **Epistemology**: Reference requires circularity (self-grounding)
- **Physics**: Circularity has mass (trapped energy)
- **Dynamics**: Mass requires stability (tolerance for strain)
-/

import Diaspora.Models.Naming
import Diaspora.Dynamics.Stability
import Diaspora.Dynamics.GirthStability
import Diaspora.Logic.Classicality.Cycles

open BigOperators Diaspora.Core Diaspora.Hodge Diaspora.Dynamics Diaspora.Logic

namespace Diaspora.Models.NamingStability

open Naming

/-! ## The Naming Cycle -/

/-- The naming cycle: P(0) → M(1) → S1(2) → P(0).
    This is the minimal referential loop created by the naming act. -/
def naming_cycle : GeneralCycle 4 where
  verts := [P', M', S1']  -- [0, 1, 2]
  len_ge_3 := by decide
  nodup := by decide

/-- The naming cycle has length 3 (a triangle). -/
theorem naming_cycle_length : naming_cycle.len = 3 := rfl

/-- The naming cycle is embedded in G_named. -/
theorem naming_cycle_embedded : generalCycleEmbeddedIn naming_cycle G_named := by
  intro ⟨k, hk⟩
  have h_len : naming_cycle.verts.length = 3 := rfl
  simp only [h_len] at hk
  have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases this with (rfl | rfl | rfl)
  -- k = 0: edge (P', M') = (0, 1)
  · show (naming_cycle.vertex 0, naming_cycle.nextVertex 0) ∈ G_named.active_edges
    native_decide
  -- k = 1: edge (M', S1') = (1, 2)
  · show (naming_cycle.vertex 1, naming_cycle.nextVertex 1) ∈ G_named.active_edges
    native_decide
  -- k = 2: edge (S1', P') = (2, 0)
  · show (naming_cycle.vertex 2, naming_cycle.nextVertex 2) ∈ G_named.active_edges
    native_decide

/-! ## The Mass of a Name -/

/-- The harmonic form on the naming cycle — the "soul" of the name. -/
noncomputable def naming_harmonic : C1 4 := general_cycle_form naming_cycle

/-- **The Mass of a Name**: The naming harmonic form has energy exactly 1/3.

    This is the minimum irreducible energy required to create a referential distinction.
    The name "costs" exactly 1/3 of energy — this cannot be relaxed away. -/
theorem mass_of_name : norm_sq naming_harmonic = 1 / 3 := by
  unfold naming_harmonic
  rw [general_cycle_form_energy naming_cycle]
  simp only [naming_cycle, GeneralCycle.len, List.length_cons, List.length_nil]
  norm_num

/-- The per-edge strain of the naming harmonic is (1/3)² = 1/9. -/
theorem naming_per_edge_strain (k : Fin 3) :
    (naming_harmonic.val (naming_cycle.vertex k.val) (naming_cycle.nextVertex k.val))^2 = 1 / 9 := by
  unfold naming_harmonic
  have h_len : naming_cycle.verts.length = 3 := rfl
  have h_k_lt : k.val < naming_cycle.verts.length := by simp only [h_len]; exact k.isLt
  have h_const : (general_cycle_form naming_cycle).val
      (naming_cycle.vertex k.val) (naming_cycle.nextVertex k.val) = 1 / naming_cycle.len := by
    unfold general_cycle_form GeneralCycle.len
    simp only
    have h_exists : ∃ k' : Fin naming_cycle.verts.length,
        naming_cycle.vertex k'.val = naming_cycle.vertex k.val ∧
        naming_cycle.nextVertex k'.val = naming_cycle.nextVertex k.val := ⟨⟨k.val, h_k_lt⟩, rfl, rfl⟩
    simp only [h_exists, ↓reduceIte]
  rw [h_const]
  simp only [naming_cycle, GeneralCycle.len, List.length_cons, List.length_nil]
  norm_num

/-! ## The Stability of Names -/

/-- **Names are Stable iff Tolerance ≥ 1/9**:

    The naming construction creates a 3-cycle. For this cycle to persist
    (not have any edge break), the breaking threshold must satisfy C_max ≥ 1/9.

    This is the **minimum tolerance required for meaning to exist**. -/
theorem naming_stable_iff (C_max : ℝ) :
    (∀ k : Fin 3,
      (naming_harmonic.val (naming_cycle.vertex k.val) (naming_cycle.nextVertex k.val))^2 ≤ C_max) ↔
    C_max ≥ 1 / 9 := by
  constructor
  · intro h_stable
    have h_strain := naming_per_edge_strain ⟨0, by omega⟩
    have h_le := h_stable ⟨0, by omega⟩
    rw [h_strain] at h_le
    exact h_le
  · intro h_threshold k
    rw [naming_per_edge_strain k]
    exact h_threshold

/-- **Unstable Names Break**: If C_max < 1/9, the naming cycle has at least one
    overstressed edge and will eventually break. -/
theorem naming_unstable_below_threshold (C_max : ℝ) (h_below : C_max < 1 / 9) :
    ∃ k : Fin 3,
      (naming_harmonic.val (naming_cycle.vertex k.val) (naming_cycle.nextVertex k.val))^2 > C_max := by
  use ⟨0, by omega⟩
  rw [naming_per_edge_strain]
  exact h_below

/-! ## The Tolerance Hierarchy -/

/-- **Triangle Names Require Maximum Tolerance**:

    Among all possible naming structures (cycles of different lengths),
    the simplest name (3-cycle) requires the highest tolerance: 1/9.

    Longer referential chains (k-cycles with k > 3) require less tolerance: 1/k². -/
theorem shorter_names_need_more_tolerance (k : ℕ) (h_k : k ≥ 3) :
    (1 : ℝ) / 3^2 ≥ 1 / k^2 := Stability.triangle_is_minimum_paradox k h_k

/-- **The Cost-Stability Tradeoff**:

    Simpler names (shorter cycles) are:
    - More expensive (higher mass: 1/k is larger for smaller k)
    - Less stable (require higher tolerance: 1/k² is larger for smaller k)

    Complex names (longer cycles) are:
    - Cheaper (lower mass)
    - More stable (survive in harsher environments)

    This explains why "simple" concepts may be harder to sustain than complex ones. -/
theorem cost_stability_tradeoff (k₁ k₂ : ℕ) (h₁ : k₁ ≥ 3) (h₂ : k₂ ≥ 3) (h_lt : k₁ < k₂) :
    -- Shorter cycle has higher mass (more expensive)
    (1 : ℝ) / k₁ > 1 / k₂ ∧
    -- Shorter cycle needs higher tolerance (less stable)
    (1 : ℝ) / k₁^2 > 1 / k₂^2 := by
  have h_pos₁ : (k₁ : ℝ) > 0 := by positivity
  have h_pos₂ : (k₂ : ℝ) > 0 := by positivity
  have h_cast_lt : (k₁ : ℝ) < k₂ := Nat.cast_lt.mpr h_lt
  constructor
  · exact one_div_lt_one_div_of_lt h_pos₁ h_cast_lt
  · have h_sq_lt : (k₁ : ℝ)^2 < k₂^2 := by nlinarith
    exact one_div_lt_one_div_of_lt (by positivity) h_sq_lt

/-! ## The Grand Synthesis -/

/-- **The Meaning-Tolerance Correspondence**:

    In a universe with breaking threshold C_max:
    - If C_max ≥ 1/9: Triangular names (simplest references) can exist
    - If 1/16 ≤ C_max < 1/9: Only 4-cycles and longer can exist
    - If 1/k² ≤ C_max < 1/(k-1)²: Only k-cycles and longer can exist
    - If C_max → 0: No names can exist (pure classical vacuum)

    The universe's tolerance for paradox determines the **granularity of meaning**
    — how fine-grained references can be.
-/
theorem meaning_requires_tolerance (C_max : ℝ) (h_pos : C_max > 0) :
    -- The minimum cycle length that can exist stably
    let min_length := Stability.criticalCycleLength C_max
    -- If min_length > 3, triangular names cannot exist
    (min_length > 3 → C_max < 1 / 9) ∧
    -- If C_max ≥ 1/9, triangular names can exist
    (C_max ≥ 1 / 9 → min_length ≤ 3) := by
  constructor
  · intro h_min_gt_3
    by_contra h_ge
    push_neg at h_ge
    have h_min_le := Stability.criticalCycleLength_pos C_max h_pos
    rw [h_min_le] at h_min_gt_3
    have h_sqrt_pos : Real.sqrt C_max > 0 := Real.sqrt_pos.mpr h_pos
    have h_ceil_ge : ⌈1 / Real.sqrt C_max⌉₊ ≥ 1 / Real.sqrt C_max := Nat.le_ceil _
    have h_inv_le : 1 / Real.sqrt C_max ≤ 3 := by
      have h_sqrt_ge : Real.sqrt C_max ≥ Real.sqrt (1 / 9) := Real.sqrt_le_sqrt h_ge
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one] at h_sqrt_ge
      have h_sqrt_9 : Real.sqrt 9 = 3 := by
        rw [show (9 : ℝ) = 3^2 by norm_num, Real.sqrt_sq (by norm_num : (3 : ℝ) ≥ 0)]
      rw [h_sqrt_9] at h_sqrt_ge
      have : Real.sqrt C_max ≥ 1 / 3 := h_sqrt_ge
      calc 1 / Real.sqrt C_max ≤ 1 / (1 / 3) := one_div_le_one_div_of_le (by norm_num) this
        _ = 3 := by norm_num
    have h_ceil_le_3 : ⌈1 / Real.sqrt C_max⌉₊ ≤ 3 := Nat.ceil_le.mpr h_inv_le
    omega
  · intro h_ge
    rw [Stability.criticalCycleLength_pos C_max h_pos]
    have h_sqrt_pos : Real.sqrt C_max > 0 := Real.sqrt_pos.mpr h_pos
    have h_sqrt_ge : Real.sqrt C_max ≥ Real.sqrt (1 / 9) := Real.sqrt_le_sqrt h_ge
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one] at h_sqrt_ge
    have h_sqrt_9 : Real.sqrt 9 = 3 := by
      rw [show (9 : ℝ) = 3^2 by norm_num, Real.sqrt_sq (by norm_num : (3 : ℝ) ≥ 0)]
    rw [h_sqrt_9] at h_sqrt_ge
    have h_inv_le : 1 / Real.sqrt C_max ≤ 3 := by
      calc 1 / Real.sqrt C_max ≤ 1 / (1 / 3) := one_div_le_one_div_of_le (by norm_num) h_sqrt_ge
        _ = 3 := by norm_num
    exact Nat.ceil_le.mpr h_inv_le

/-- **Classical Universes Cannot Name**:

    A universe with zero tolerance (C_max = 0) cannot sustain any names.
    This connects classicality (b₁ = 0) with the inability to reference. -/
theorem classical_cannot_name :
    ∀ ε > 0, ε < 1 / 9 → ∃ C_max : ℝ, 0 < C_max ∧ C_max < ε ∧
      ∀ k : Fin 3,
        (naming_harmonic.val (naming_cycle.vertex k.val) (naming_cycle.nextVertex k.val))^2 > C_max := by
  intro ε h_ε_pos h_ε_small
  use ε / 2
  refine ⟨by linarith, by linarith, ?_⟩
  intro k
  rw [naming_per_edge_strain]
  linarith

end Diaspora.Models.NamingStability
