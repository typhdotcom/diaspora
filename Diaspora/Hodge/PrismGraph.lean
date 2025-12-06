/-
# Prism Graph Betti Numbers

The prism graph (or circular ladder, n-prism) consists of two n-cycles
connected by n "rungs" matching corresponding vertices:

    Top:    0 — 1 — 2 — ... — (n-1) — 0
            |   |   |           |
    Bottom: n — n+1— n+2— ... — (2n-1)— n

The Betti number is:
  b₁(Prism_n) = n + 1

This extends the Interaction.lean "handshake theorem" to complete fusion.
Two isolated n-cycles have total b₁ = 2 (each contributes 1).
Fusing them at all n vertices creates n-1 ADDITIONAL independent cycles,
for a total of n+1.

Physical interpretation: The shared frustration grows linearly with
the interface size. Each point of contact (beyond connectivity) adds
a new channel of irreducible constraint.
-/

import Diaspora.Hodge.IndexTheorem
import Mathlib.LinearAlgebra.Dimension.Finrank

open BigOperators Diaspora.Core Diaspora.Hodge

namespace Diaspora.Hodge.PrismGraph

/-! ## Concrete Prism Graphs for small n -/

/-- The triangular prism (Prism_3) on 6 vertices.
    Top cycle: 0-1-2-0, Bottom cycle: 3-4-5-3, Rungs: 0-3, 1-4, 2-5 -/
def prism3 : DynamicGraph 6 where
  active_edges := {
    -- Top cycle
    (0, 1), (1, 0), (1, 2), (2, 1), (2, 0), (0, 2),
    -- Bottom cycle
    (3, 4), (4, 3), (4, 5), (5, 4), (5, 3), (3, 5),
    -- Rungs
    (0, 3), (3, 0), (1, 4), (4, 1), (2, 5), (5, 2)
  }
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> decide
  no_loops := by intro i; fin_cases i <;> decide

/-- Prism_3 has 18 directed edges (9 undirected: 3 top + 3 bottom + 3 rungs). -/
lemma prism3_edge_count : prism3.active_edges.card = 18 := by native_decide

/-- Prism_3 is connected: kernel dimension = 1. -/
lemma prism3_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear prism3)) = 1 := by
  -- The graph is connected (via top cycle + rungs + bottom cycle)
  let one : Fin 6 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear prism3) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G prism3 one).val.val i j = 0
    unfold d_G one
    simp only [prism3, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear prism3) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ prism3.active_edges := by simp [prism3]
        have h_zero : (d_G prism3 φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h02 : φ 2 = φ 0 := by
        have h_edge : (0, 2) ∈ prism3.active_edges := by simp [prism3]
        have h_zero : (d_G prism3 φ).val.val 0 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h03 : φ 3 = φ 0 := by
        have h_edge : (0, 3) ∈ prism3.active_edges := by simp [prism3]
        have h_zero : (d_G prism3 φ).val.val 0 3 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 3
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h34 : φ 4 = φ 3 := by
        have h_edge : (3, 4) ∈ prism3.active_edges := by simp [prism3]
        have h_zero : (d_G prism3 φ).val.val 3 4 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 3 4
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h35 : φ 5 = φ 3 := by
        have h_edge : (3, 5) ∈ prism3.active_edges := by simp [prism3]
        have h_zero : (d_G prism3 φ).val.val 3 5 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 3 5
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h02, h03, h34, h35]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- **Prism_3 Betti Number**: b₁(Prism_3) = 4

    The triangular prism has 4 independent cycles:
    - The top triangle
    - The bottom triangle
    - 2 "ladder" cycles threading both

    Two isolated triangles have total b₁ = 2.
    Fusing them at 3 vertices creates 2 additional cycles.
-/
theorem prism3_betti_four : Module.finrank ℝ (HarmonicSubspace prism3) = 4 := by
  have h_dim := harmonic_dimension_eq_cyclomatic prism3
  have h_ker := prism3_kernel_dim
  have h_edge := prism3_edge_count
  have h_edge_half : prism3.active_edges.card / 2 = 9 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

/-! ## Cube graph (Prism_4) -/

/-- The cube graph (Prism_4) on 8 vertices.
    Top square: 0-1-2-3-0, Bottom square: 4-5-6-7-4, Rungs: 0-4, 1-5, 2-6, 3-7 -/
def prism4 : DynamicGraph 8 where
  active_edges := {
    -- Top square
    (0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3),
    -- Bottom square
    (4, 5), (5, 4), (5, 6), (6, 5), (6, 7), (7, 6), (7, 4), (4, 7),
    -- Rungs
    (0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2), (3, 7), (7, 3)
  }
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> decide
  no_loops := by intro i; fin_cases i <;> decide

/-- Prism_4 has 24 directed edges (12 undirected: 4 top + 4 bottom + 4 rungs). -/
lemma prism4_edge_count : prism4.active_edges.card = 24 := by native_decide

/-- Prism_4 is connected: kernel dimension = 1. -/
lemma prism4_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear prism4)) = 1 := by
  let one : Fin 8 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear prism4) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G prism4 one).val.val i j = 0
    unfold d_G one
    simp only [prism4, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear prism4) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ prism4.active_edges := by simp [prism4]
        have h_zero : (d_G prism4 φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h12 : φ 2 = φ 1 := by
        have h_edge : (1, 2) ∈ prism4.active_edges := by simp [prism4]
        have h_zero : (d_G prism4 φ).val.val 1 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h23 : φ 3 = φ 2 := by
        have h_edge : (2, 3) ∈ prism4.active_edges := by simp [prism4]
        have h_zero : (d_G prism4 φ).val.val 2 3 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 2 3
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h04 : φ 4 = φ 0 := by
        have h_edge : (0, 4) ∈ prism4.active_edges := by simp [prism4]
        have h_zero : (d_G prism4 φ).val.val 0 4 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 4
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h45 : φ 5 = φ 4 := by
        have h_edge : (4, 5) ∈ prism4.active_edges := by simp [prism4]
        have h_zero : (d_G prism4 φ).val.val 4 5 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 4 5
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h56 : φ 6 = φ 5 := by
        have h_edge : (5, 6) ∈ prism4.active_edges := by simp [prism4]
        have h_zero : (d_G prism4 φ).val.val 5 6 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 5 6
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h67 : φ 7 = φ 6 := by
        have h_edge : (6, 7) ∈ prism4.active_edges := by simp [prism4]
        have h_zero : (d_G prism4 φ).val.val 6 7 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 6 7
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h12, h23, h04, h45, h56, h67]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- **Cube Graph Betti Number**: b₁(Prism_4) = 5

    The cube has 5 independent cycles:
    - The top square
    - The bottom square
    - 3 "ladder" cycles threading both faces

    Two isolated squares have total b₁ = 2.
    Fusing them at 4 vertices creates 3 additional cycles.
-/
theorem prism4_betti_five : Module.finrank ℝ (HarmonicSubspace prism4) = 5 := by
  have h_dim := harmonic_dimension_eq_cyclomatic prism4
  have h_ker := prism4_kernel_dim
  have h_edge := prism4_edge_count
  have h_edge_half : prism4.active_edges.card / 2 = 12 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

/-! ## Philosophical Interpretation -/

/-- Fusion creates more topology than the sum of parts.

    Two isolated triangles: total b₁ = 1 + 1 = 2
    Prism_3 (fused at all 3 vertices): b₁ = 4

    Two isolated squares: total b₁ = 1 + 1 = 2
    Prism_4 (fused at all 4 vertices): b₁ = 5

    The pattern: Prism_n has b₁ = n + 1 = 2 + (n - 1).
    Fusion creates n - 1 ADDITIONAL independent cycles.
-/
theorem fusion_amplifies_topology_3 : Module.finrank ℝ (HarmonicSubspace prism3) = 2 + (3 - 1) := by
  rw [prism3_betti_four]

theorem fusion_amplifies_topology_4 : Module.finrank ℝ (HarmonicSubspace prism4) = 2 + (4 - 1) := by
  rw [prism4_betti_five]

/-- The cost of mirroring: fusing two worlds at n points creates n-1 new cycles.

    This generalizes the Interaction.lean "handshake theorem":
    - 2 triangles + 2 bridges → 1 new cycle (from Interaction.lean)
    - 2 triangles + 3 bridges (full fusion) → 2 new cycles (Prism_3)
    - 2 squares + 4 bridges (full fusion) → 3 new cycles (Prism_4)

    The shared frustration grows linearly with the interface size.
-/
theorem mirror_world_topology_cost_3 :
    Module.finrank ℝ (HarmonicSubspace prism3) - 2 = 3 - 1 := by
  rw [prism3_betti_four]

theorem mirror_world_topology_cost_4 :
    Module.finrank ℝ (HarmonicSubspace prism4) - 2 = 4 - 1 := by
  rw [prism4_betti_five]

end Diaspora.Hodge.PrismGraph
