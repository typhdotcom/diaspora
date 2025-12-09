import Diaspora.Hodge.Decomposition
import Mathlib.LinearAlgebra.Dimension.Finrank

open BigOperators Diaspora.Core Diaspora.Hodge

namespace Diaspora.Hodge.PetersenGraph

/-- The Petersen graph on 10 vertices.

    Outer pentagon: 0-1-2-3-4-0
    Inner pentagram: 5-7-9-6-8-5 (connecting every second vertex)
    Spokes: i ↔ i+5 for i ∈ {0,1,2,3,4}
-/
def petersen : DynamicGraph 10 where
  active_edges := {
    -- Outer pentagon: 0-1-2-3-4-0
    (0, 1), (1, 0),
    (1, 2), (2, 1),
    (2, 3), (3, 2),
    (3, 4), (4, 3),
    (4, 0), (0, 4),
    -- Inner pentagram: 5-7-9-6-8-5 (skip by 2 in the inner ring)
    (5, 7), (7, 5),
    (7, 9), (9, 7),
    (9, 6), (6, 9),
    (6, 8), (8, 6),
    (8, 5), (5, 8),
    -- Spokes connecting outer to inner
    (0, 5), (5, 0),
    (1, 6), (6, 1),
    (2, 7), (7, 2),
    (3, 8), (8, 3),
    (4, 9), (9, 4)
  }
  symmetric := by decide
  no_loops := by decide

/-- The Petersen graph has 30 directed edges (15 undirected).
    - 5 outer pentagon edges
    - 5 inner pentagram edges
    - 5 spokes
    Total: 15 undirected = 30 directed
-/
lemma petersen_edge_count : petersen.active_edges.card = 30 := by native_decide

/-- Every vertex in the Petersen graph has exactly 3 neighbors (3-regular). -/
lemma petersen_is_3_regular (v : Fin 10) :
    (petersen.active_edges.filter (fun e => e.1 = v)).card = 3 := by
  fin_cases v <;> native_decide

/-- The Petersen graph is connected: kernel dimension = 1.

    The proof shows that any potential in the gradient kernel must be constant
    by tracing connectivity through the graph structure.
-/
lemma petersen_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear petersen)) = 1 := by
  let one : Fin 10 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear petersen) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G petersen one).val.val i j = 0
    unfold d_G one
    simp only [petersen]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear petersen) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      -- Trace connectivity through outer pentagon
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ petersen.active_edges := by decide
        have h_zero : (d_G petersen φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h12 : φ 2 = φ 1 := by
        have h_edge : (1, 2) ∈ petersen.active_edges := by decide
        have h_zero : (d_G petersen φ).val.val 1 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h23 : φ 3 = φ 2 := by
        have h_edge : (2, 3) ∈ petersen.active_edges := by decide
        have h_zero : (d_G petersen φ).val.val 2 3 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 2 3
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h34 : φ 4 = φ 3 := by
        have h_edge : (3, 4) ∈ petersen.active_edges := by decide
        have h_zero : (d_G petersen φ).val.val 3 4 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 3 4
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      -- Connect to inner vertices via spokes
      have h05 : φ 5 = φ 0 := by
        have h_edge : (0, 5) ∈ petersen.active_edges := by decide
        have h_zero : (d_G petersen φ).val.val 0 5 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 5
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h16 : φ 6 = φ 1 := by
        have h_edge : (1, 6) ∈ petersen.active_edges := by decide
        have h_zero : (d_G petersen φ).val.val 1 6 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 6
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h27 : φ 7 = φ 2 := by
        have h_edge : (2, 7) ∈ petersen.active_edges := by decide
        have h_zero : (d_G petersen φ).val.val 2 7 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 2 7
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h38 : φ 8 = φ 3 := by
        have h_edge : (3, 8) ∈ petersen.active_edges := by decide
        have h_zero : (d_G petersen φ).val.val 3 8 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 3 8
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h49 : φ 9 = φ 4 := by
        have h_edge : (4, 9) ∈ petersen.active_edges := by decide
        have h_zero : (d_G petersen φ).val.val 4 9 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 4 9
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h12, h23, h34, h05, h16, h27, h38, h49]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- **The Petersen Graph Betti Number**: b₁(Petersen) = 6

    The Petersen graph has 6 independent cycles.
    Since it's connected with 10 vertices and 15 edges:
      b₁ = |E| - |V| + 1 = 15 - 10 + 1 = 6

    These 6 cycles are distributed uniformly across the graph -
    no vertex or edge is more "responsible" for the topology than any other.
-/
theorem petersen_betti_six : Module.finrank ℝ (HarmonicSubspace petersen) = 6 := by
  have h_dim := harmonic_dimension_eq_cyclomatic petersen
  have h_ker := petersen_kernel_dim
  have h_edge := petersen_edge_count
  have h_edge_half : petersen.active_edges.card / 2 = 15 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

/-- The Petersen graph is non-classical: it has positive harmonic dimension. -/
theorem petersen_nonclassical : Module.finrank ℝ (HarmonicSubspace petersen) > 0 := by
  rw [petersen_betti_six]; omega

/-! ## Comparative Analysis -/

/-- Vertices in Petersen: 10 -/
lemma petersen_vertex_count : Fintype.card (Fin 10) = 10 := by rfl

/-- Edges in Petersen (undirected): 15 -/
lemma petersen_undirected_edge_count : petersen.active_edges.card / 2 = 15 := by
  rw [petersen_edge_count]

/-- Cycle efficiency: cycles per edge.
    Petersen: 6/15 = 0.4 cycles per edge
    For comparison:
    - Triangle: 1/3 ≈ 0.33
    - Complete K_5: 6/10 = 0.6
    - 10-cycle: 1/10 = 0.1
-/
theorem petersen_cycle_efficiency : (6 : ℚ) / 15 = 2 / 5 := by norm_num

/-- Vertex coverage: cycles per vertex.
    Petersen: 6/10 = 0.6 cycles per vertex -/
theorem petersen_vertex_coverage : (6 : ℚ) / 10 = 3 / 5 := by norm_num

theorem petersen_uniform_degree : ∀ v : Fin 10,
    (petersen.active_edges.filter (fun e => e.1 = v)).card = 3 :=
  petersen_is_3_regular

end Diaspora.Hodge.PetersenGraph
