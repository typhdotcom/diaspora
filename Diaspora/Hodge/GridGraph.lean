import Diaspora.Hodge.IndexTheorem
import Diaspora.Hodge.BipartiteGraph
import Diaspora.Hodge.LadderGraph
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Grid Graph Betti Numbers

G_{m,n} is an m×n rectangular lattice.

**Main result**: b₁(G_{m,n}) = (m-1)(n-1)

Coincides with K_{m,n} despite different edge structure.
-/

open BigOperators Diaspora.Core Diaspora.Hodge

namespace Diaspora.Hodge.GridGraph

/-! ## Concrete Grid Graphs -/

/-- G_{2,3}: 6 vertices in 2×3 layout. -/
def grid2x3 : DynamicGraph 6 where
  active_edges := {
    -- Row 0: horizontal edges
    (0, 1), (1, 0), (1, 2), (2, 1),
    -- Row 1: horizontal edges
    (3, 4), (4, 3), (4, 5), (5, 4),
    -- Vertical edges
    (0, 3), (3, 0), (1, 4), (4, 1), (2, 5), (5, 2)
  }
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> decide
  no_loops := by intro i; fin_cases i <;> decide

/-- G_{2,3} has 14 directed edges (7 undirected: 2+2 horizontal, 3 vertical). -/
lemma grid2x3_edge_count : grid2x3.active_edges.card = 14 := by native_decide

/-- G_{2,3} is connected: kernel dimension = 1. -/
lemma grid2x3_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear grid2x3)) = 1 := by
  let one : Fin 6 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear grid2x3) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G grid2x3 one).val.val i j = 0
    unfold d_G one
    simp only [grid2x3, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear grid2x3) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ grid2x3.active_edges := by simp [grid2x3]
        have h_zero : (d_G grid2x3 φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h12 : φ 2 = φ 1 := by
        have h_edge : (1, 2) ∈ grid2x3.active_edges := by simp [grid2x3]
        have h_zero : (d_G grid2x3 φ).val.val 1 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h03 : φ 3 = φ 0 := by
        have h_edge : (0, 3) ∈ grid2x3.active_edges := by simp [grid2x3]
        have h_zero : (d_G grid2x3 φ).val.val 0 3 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 3
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h34 : φ 4 = φ 3 := by
        have h_edge : (3, 4) ∈ grid2x3.active_edges := by simp [grid2x3]
        have h_zero : (d_G grid2x3 φ).val.val 3 4 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 3 4
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h45 : φ 5 = φ 4 := by
        have h_edge : (4, 5) ∈ grid2x3.active_edges := by simp [grid2x3]
        have h_zero : (d_G grid2x3 φ).val.val 4 5 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 4 5
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h12, h03, h34, h45]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- b₁(G_{2,3}) = 2 = (2-1)(3-1) -/
theorem grid2x3_betti_two : Module.finrank ℝ (HarmonicSubspace grid2x3) = 2 := by
  have h_dim := harmonic_dimension_eq_cyclomatic grid2x3
  have h_ker := grid2x3_kernel_dim
  have h_edge := grid2x3_edge_count
  have h_edge_half : grid2x3.active_edges.card / 2 = 7 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

/-! ## The 3×3 Grid -/

/-- G_{3,3}: 9 vertices in 3×3 layout. -/
def grid3x3 : DynamicGraph 9 where
  active_edges := {
    -- Row 0: horizontal edges
    (0, 1), (1, 0), (1, 2), (2, 1),
    -- Row 1: horizontal edges
    (3, 4), (4, 3), (4, 5), (5, 4),
    -- Row 2: horizontal edges
    (6, 7), (7, 6), (7, 8), (8, 7),
    -- Vertical edges (column 0)
    (0, 3), (3, 0), (3, 6), (6, 3),
    -- Vertical edges (column 1)
    (1, 4), (4, 1), (4, 7), (7, 4),
    -- Vertical edges (column 2)
    (2, 5), (5, 2), (5, 8), (8, 5)
  }
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> decide
  no_loops := by intro i; fin_cases i <;> decide

/-- G_{3,3} has 24 directed edges (12 undirected: 6 horizontal, 6 vertical). -/
lemma grid3x3_edge_count : grid3x3.active_edges.card = 24 := by native_decide

/-- G_{3,3} is connected: kernel dimension = 1. -/
lemma grid3x3_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear grid3x3)) = 1 := by
  let one : Fin 9 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear grid3x3) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G grid3x3 one).val.val i j = 0
    unfold d_G one
    simp only [grid3x3, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear grid3x3) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      -- Connectivity along row 0
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ grid3x3.active_edges := by simp [grid3x3]
        have h_zero : (d_G grid3x3 φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h12 : φ 2 = φ 1 := by
        have h_edge : (1, 2) ∈ grid3x3.active_edges := by simp [grid3x3]
        have h_zero : (d_G grid3x3 φ).val.val 1 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      -- Connectivity down column 0
      have h03 : φ 3 = φ 0 := by
        have h_edge : (0, 3) ∈ grid3x3.active_edges := by simp [grid3x3]
        have h_zero : (d_G grid3x3 φ).val.val 0 3 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 3
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h36 : φ 6 = φ 3 := by
        have h_edge : (3, 6) ∈ grid3x3.active_edges := by simp [grid3x3]
        have h_zero : (d_G grid3x3 φ).val.val 3 6 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 3 6
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      -- Connectivity along row 1
      have h34 : φ 4 = φ 3 := by
        have h_edge : (3, 4) ∈ grid3x3.active_edges := by simp [grid3x3]
        have h_zero : (d_G grid3x3 φ).val.val 3 4 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 3 4
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h45 : φ 5 = φ 4 := by
        have h_edge : (4, 5) ∈ grid3x3.active_edges := by simp [grid3x3]
        have h_zero : (d_G grid3x3 φ).val.val 4 5 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 4 5
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      -- Connectivity along row 2
      have h67 : φ 7 = φ 6 := by
        have h_edge : (6, 7) ∈ grid3x3.active_edges := by simp [grid3x3]
        have h_zero : (d_G grid3x3 φ).val.val 6 7 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 6 7
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h78 : φ 8 = φ 7 := by
        have h_edge : (7, 8) ∈ grid3x3.active_edges := by simp [grid3x3]
        have h_zero : (d_G grid3x3 φ).val.val 7 8 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 7 8
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h12, h03, h36, h34, h45, h67, h78]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- b₁(G_{3,3}) = 4 = (3-1)(3-1) -/
theorem grid3x3_betti_four : Module.finrank ℝ (HarmonicSubspace grid3x3) = 4 := by
  have h_dim := harmonic_dimension_eq_cyclomatic grid3x3
  have h_ker := grid3x3_kernel_dim
  have h_edge := grid3x3_edge_count
  have h_edge_half : grid3x3.active_edges.card / 2 = 12 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

/-! ## Pattern Verification -/

/-- G_{2,3} follows the pattern b₁ = (m-1)(n-1). -/
theorem grid2x3_pattern : Module.finrank ℝ (HarmonicSubspace grid2x3) = (2 - 1) * (3 - 1) := by
  rw [grid2x3_betti_two]

/-- G_{3,3} follows the pattern b₁ = (m-1)(n-1). -/
theorem grid3x3_pattern : Module.finrank ℝ (HarmonicSubspace grid3x3) = (3 - 1) * (3 - 1) := by
  rw [grid3x3_betti_four]

/-! ## The Bipartite Coincidence: b₁(G_{m,n}) = b₁(K_{m,n}) -/

/-- G_{2,3} and K_{2,3} have the same Betti number. -/
theorem grid_bipartite_coincidence_2_3 :
    Module.finrank ℝ (HarmonicSubspace grid2x3) =
    Module.finrank ℝ (HarmonicSubspace (BipartiteGraph.completeBipartite 2 3)) := by
  rw [grid2x3_betti_two]
  have h := BipartiteGraph.bipartite_betti_1 2 3
  norm_num at h ⊢
  exact h.symm

/-- G_{3,3} and K_{3,3} have the same Betti number. -/
theorem grid_bipartite_coincidence_3_3 :
    Module.finrank ℝ (HarmonicSubspace grid3x3) =
    Module.finrank ℝ (HarmonicSubspace (BipartiteGraph.completeBipartite 3 3)) := by
  rw [grid3x3_betti_four]
  have h := BipartiteGraph.bipartite_betti_1 3 3
  norm_num at h ⊢
  exact h.symm

/-! ## Edge Comparisons -/

/-- G_{3,3} has more edges than K_{3,3}. -/
theorem grid_denser_than_bipartite_3_3 :
    grid3x3.active_edges.card / 2 > (BipartiteGraph.completeBipartite 3 3).active_edges.card / 2 := by
  rw [grid3x3_edge_count, BipartiteGraph.bipartite_directed_edge_count 3 3]
  native_decide

/-- G_{2,3} has more edges than K_{2,3}. -/
theorem grid_denser_than_bipartite_2_3 :
    grid2x3.active_edges.card / 2 > (BipartiteGraph.completeBipartite 2 3).active_edges.card / 2 := by
  rw [grid2x3_edge_count, BipartiteGraph.bipartite_directed_edge_count 2 3]
  native_decide

/-! ## Connection to Ladder Graph: G_{2,n} = L_n -/

/-- G_{2,3} = L_3 in terms of Betti number. -/
theorem grid_is_ladder_2_3 :
    Module.finrank ℝ (HarmonicSubspace grid2x3) =
    Module.finrank ℝ (HarmonicSubspace LadderGraph.ladder3) := by
  rw [grid2x3_betti_two, LadderGraph.ladder3_betti_two]

end Diaspora.Hodge.GridGraph
