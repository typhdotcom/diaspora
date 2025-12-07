import Diaspora.Logic.Classicality.Orthogonality

/-!
# Gravity: Edge-Sharing as Attraction

This file formalizes the central thesis of Diaspora's interpretation of gravity:

> **Gravity is just the tendency of these loops to share edges to minimize their total N.**

Topological defects (cycles carrying harmonic forms) reduce their combined energy by sharing
edges with opposite orientation. This is the fundamental mechanism of attraction in Diaspora.

## Main Results

- `sharing_energy_reduction`: The energy saved by sharing k edges with optimal orientation
- `sharing_reduces_energy`: Opposite-direction sharing reduces combined energy below the sum
- `gravity_binding_energy`: The binding energy formula E = 2k/(n₁·n₂)
- `complete_overlap_annihilation`: Same cycle, opposite direction → complete cancellation

## Physical Interpretation

Two topological defects (matter) can exist in three configurations:
1. **Disjoint**: No shared edges → energies add independently
2. **Same direction**: Shared edges amplify strain → repulsion
3. **Opposite direction**: Shared edges cancel strain → attraction (gravity)

The "force" arises from energy minimization: systems evolve toward lower-energy states.
-/

namespace Diaspora.Dynamics

open Diaspora.Core Diaspora.Logic Diaspora.Hodge

/-- The energy reduction from sharing k edges with opposite orientation.
    This is the gravitational binding energy: 2k/(n₁·n₂) -/
noncomputable def sharing_energy_reduction (n₁ n₂ k : ℕ) : ℝ :=
  2 * (k : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))

/-- Sharing edges with optimal (opposite) orientation reduces combined energy.
    This is the core theorem: edge-sharing is attractive. -/
theorem sharing_reduces_energy {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_opp : c₁.oppositeDirectionEdges c₂ > 0)
    (h_same : c₁.sameDirectionEdges c₂ = 0) :
    norm_sq (cycle_sum c₁ c₂) < norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) := by
  apply negative_overlap_reduces_energy
  unfold GeneralCycle.signedOverlap
  simp only [h_same]
  -- Goal: 0 - opp < 0
  omega

/-- The binding energy formula: energy saved = 2k/(n₁·n₂) -/
theorem gravity_binding_energy {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_same : c₁.sameDirectionEdges c₂ = 0) :
    norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) - norm_sq (cycle_sum c₁ c₂) =
    sharing_energy_reduction c₁.len c₂.len (c₁.oppositeDirectionEdges c₂) := by
  rw [combined_cycle_energy_formula, general_cycle_form_energy, general_cycle_form_energy]
  unfold sharing_energy_reduction GeneralCycle.signedOverlap
  simp only [h_same, CharP.cast_eq_zero, zero_sub, Int.cast_neg, Int.cast_natCast]
  ring

/-- Complete overlap with opposite direction gives complete cancellation.
    If two cycles traverse exactly the same edges in opposite directions, their
    combined harmonic form is zero. -/
theorem complete_overlap_annihilation {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_same_len : c₁.len = c₂.len)
    (h_complete_opp : c₁.oppositeDirectionEdges c₂ = c₁.len)
    (h_no_same : c₁.sameDirectionEdges c₂ = 0) :
    norm_sq (cycle_sum c₁ c₂) = 0 := by
  rw [combined_cycle_energy_formula]
  unfold GeneralCycle.signedOverlap
  simp only [h_no_same, CharP.cast_eq_zero, zero_sub, h_complete_opp, Int.cast_neg, Int.cast_natCast]
  have h_len1 : (0 : ℝ) < c₁.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₁.len_ge_3)
  have h_len2 : (0 : ℝ) < c₂.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₂.len_ge_3)
  -- Goal: 1/len₁ + 1/len₂ + 2 * (-len₁) / (len₁ * len₂) = 0
  -- With len₁ = len₂: 1/len + 1/len - 2*len/(len*len) = 2/len - 2/len = 0
  rw [h_same_len]
  field_simp
  ring

/-- Disjoint cycles have additive energy: no interaction.
    This is the baseline from which gravity measures binding. -/
theorem disjoint_additive_energy {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_disjoint : c₁.signedOverlap c₂ = 0) :
    norm_sq (cycle_sum c₁ c₂) = norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) := by
  rw [combined_cycle_energy]
  rw [cycle_inner_product_formula, h_disjoint]
  simp only [Int.cast_zero, zero_div, mul_zero, add_zero]

/-- The Grand Synthesis: Gravity is edge-sharing minimization.

    This chains the full Diaspora correspondence:
    **Paradox → Topology → Mass → Gravity**

    - Paradox creates non-trivial harmonic forms (topology)
    - Harmonic forms have energy (mass = 1/n for n-cycle)
    - Overlapping forms with opposite orientation have lower energy
    - Systems evolve toward lower energy → attraction

    Matter is trapped logical inconsistency.
    Gravity is the tendency of inconsistencies to share their contradictions. -/
theorem gravity_is_edge_sharing {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n) :
    -- More shared opposite-direction edges = more energy reduction
    ∀ k : ℕ,
      (c₁.oppositeDirectionEdges c₂ = k ∧ c₁.sameDirectionEdges c₂ = 0) →
      norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) - norm_sq (cycle_sum c₁ c₂) =
      sharing_energy_reduction c₁.len c₂.len k := by
  intro k ⟨h_opp, h_same⟩
  rw [← h_opp]
  exact gravity_binding_energy c₁ c₂ h_same

end Diaspora.Dynamics
