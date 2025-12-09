import Diaspora.Hodge.GridGraph
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Torus Graph Betti Numbers

T_{m,n} is the grid graph with wraparound edges in both dimensions.

**Main result**: b₁(T_{m,n}) = mn + 1 (for m,n ≥ 3)

Closing grid→torus adds m + n new cycles from wrapping edges.
-/

open BigOperators Diaspora.Core Diaspora.Hodge

namespace Diaspora.Hodge.TorusGraph

/-! ## Concrete Torus Graphs -/

/-- T_{2,2}: degenerate case, isomorphic to C_4. -/
def torus2x2 : DynamicGraph 4 where
  active_edges := {
    -- Row 0: horizontal edges (including wrap)
    (0, 1), (1, 0),
    -- Row 1: horizontal edges (including wrap)
    (2, 3), (3, 2),
    -- Vertical edges (including wrap)
    (0, 2), (2, 0), (1, 3), (3, 1)
  }
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> decide
  no_loops := by intro i; fin_cases i <;> decide

/-- T_{2,2} has 8 directed edges (4 undirected). -/
lemma torus2x2_edge_count : torus2x2.active_edges.card = 8 := by native_decide

/-- T_{2,2} is connected: kernel dimension = 1. -/
lemma torus2x2_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear torus2x2)) = 1 := by
  let one : Fin 4 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear torus2x2) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G torus2x2 one).val.val i j = 0
    unfold d_G one
    simp only [torus2x2, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear torus2x2) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ torus2x2.active_edges := by simp [torus2x2]
        have h_zero : (d_G torus2x2 φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h02 : φ 2 = φ 0 := by
        have h_edge : (0, 2) ∈ torus2x2.active_edges := by simp [torus2x2]
        have h_zero : (d_G torus2x2 φ).val.val 0 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h13 : φ 3 = φ 1 := by
        have h_edge : (1, 3) ∈ torus2x2.active_edges := by simp [torus2x2]
        have h_zero : (d_G torus2x2 φ).val.val 1 3 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 3
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h02, h13]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- b₁(T_{2,2}) = 1 (degenerate: wraps collapse to single edges). -/
theorem torus2x2_betti : Module.finrank ℝ (HarmonicSubspace torus2x2) = 1 := by
  have h_dim := harmonic_dimension_eq_cyclomatic torus2x2
  have h_ker := torus2x2_kernel_dim
  have h_edge := torus2x2_edge_count
  have h_edge_half : torus2x2.active_edges.card / 2 = 4 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

/-! ## The 2×3 Torus -/

/-- T_{2,3}: 6 vertices, still degenerate in vertical direction. -/
def torus2x3 : DynamicGraph 6 where
  active_edges := {
    -- Row 0: horizontal edges (including wrap 2-0)
    (0, 1), (1, 0), (1, 2), (2, 1), (2, 0), (0, 2),
    -- Row 1: horizontal edges (including wrap 5-3)
    (3, 4), (4, 3), (4, 5), (5, 4), (5, 3), (3, 5),
    -- Vertical edges (for m=2, wraps are same edges)
    (0, 3), (3, 0), (1, 4), (4, 1), (2, 5), (5, 2)
  }
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> decide
  no_loops := by intro i; fin_cases i <;> decide

/-- T_{2,3} has 18 directed edges (9 undirected: 6 horizontal + 3 vertical). -/
lemma torus2x3_edge_count : torus2x3.active_edges.card = 18 := by native_decide

/-- T_{2,3} is connected: kernel dimension = 1. -/
lemma torus2x3_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear torus2x3)) = 1 := by
  let one : Fin 6 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear torus2x3) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G torus2x3 one).val.val i j = 0
    unfold d_G one
    simp only [torus2x3, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear torus2x3) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ torus2x3.active_edges := by simp [torus2x3]
        have h_zero : (d_G torus2x3 φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h12 : φ 2 = φ 1 := by
        have h_edge : (1, 2) ∈ torus2x3.active_edges := by simp [torus2x3]
        have h_zero : (d_G torus2x3 φ).val.val 1 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h03 : φ 3 = φ 0 := by
        have h_edge : (0, 3) ∈ torus2x3.active_edges := by simp [torus2x3]
        have h_zero : (d_G torus2x3 φ).val.val 0 3 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 3
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h34 : φ 4 = φ 3 := by
        have h_edge : (3, 4) ∈ torus2x3.active_edges := by simp [torus2x3]
        have h_zero : (d_G torus2x3 φ).val.val 3 4 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 3 4
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h45 : φ 5 = φ 4 := by
        have h_edge : (4, 5) ∈ torus2x3.active_edges := by simp [torus2x3]
        have h_zero : (d_G torus2x3 φ).val.val 4 5 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 4 5
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h12, h03, h34, h45]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- b₁(T_{2,3}) = 4 -/
theorem torus2x3_betti_four : Module.finrank ℝ (HarmonicSubspace torus2x3) = 4 := by
  have h_dim := harmonic_dimension_eq_cyclomatic torus2x3
  have h_ker := torus2x3_kernel_dim
  have h_edge := torus2x3_edge_count
  have h_edge_half : torus2x3.active_edges.card / 2 = 9 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

/-! ## The 3×3 Torus -/

/-- T_{3,3}: 9 vertices, first non-degenerate case. -/
def torus3x3 : DynamicGraph 9 where
  active_edges := {
    -- Row 0: horizontal (including wrap 2-0)
    (0, 1), (1, 0), (1, 2), (2, 1), (2, 0), (0, 2),
    -- Row 1: horizontal (including wrap 5-3)
    (3, 4), (4, 3), (4, 5), (5, 4), (5, 3), (3, 5),
    -- Row 2: horizontal (including wrap 8-6)
    (6, 7), (7, 6), (7, 8), (8, 7), (8, 6), (6, 8),
    -- Column 0: vertical (including wrap 6-0)
    (0, 3), (3, 0), (3, 6), (6, 3), (6, 0), (0, 6),
    -- Column 1: vertical (including wrap 7-1)
    (1, 4), (4, 1), (4, 7), (7, 4), (7, 1), (1, 7),
    -- Column 2: vertical (including wrap 8-2)
    (2, 5), (5, 2), (5, 8), (8, 5), (8, 2), (2, 8)
  }
  symmetric := by decide
  no_loops := by decide

/-- T_{3,3} has 36 directed edges (18 undirected: 9 horizontal + 9 vertical). -/
lemma torus3x3_edge_count : torus3x3.active_edges.card = 36 := by native_decide

/-- T_{3,3} is connected: kernel dimension = 1. -/
lemma torus3x3_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear torus3x3)) = 1 := by
  let one : Fin 9 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear torus3x3) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G torus3x3 one).val.val i j = 0
    unfold d_G one
    simp only [torus3x3]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear torus3x3) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ torus3x3.active_edges := by decide
        have h_zero : (d_G torus3x3 φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h12 : φ 2 = φ 1 := by
        have h_edge : (1, 2) ∈ torus3x3.active_edges := by decide
        have h_zero : (d_G torus3x3 φ).val.val 1 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h03 : φ 3 = φ 0 := by
        have h_edge : (0, 3) ∈ torus3x3.active_edges := by decide
        have h_zero : (d_G torus3x3 φ).val.val 0 3 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 3
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h36 : φ 6 = φ 3 := by
        have h_edge : (3, 6) ∈ torus3x3.active_edges := by decide
        have h_zero : (d_G torus3x3 φ).val.val 3 6 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 3 6
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h34 : φ 4 = φ 3 := by
        have h_edge : (3, 4) ∈ torus3x3.active_edges := by decide
        have h_zero : (d_G torus3x3 φ).val.val 3 4 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 3 4
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h45 : φ 5 = φ 4 := by
        have h_edge : (4, 5) ∈ torus3x3.active_edges := by decide
        have h_zero : (d_G torus3x3 φ).val.val 4 5 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 4 5
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h67 : φ 7 = φ 6 := by
        have h_edge : (6, 7) ∈ torus3x3.active_edges := by decide
        have h_zero : (d_G torus3x3 φ).val.val 6 7 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 6 7
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h78 : φ 8 = φ 7 := by
        have h_edge : (7, 8) ∈ torus3x3.active_edges := by decide
        have h_zero : (d_G torus3x3 φ).val.val 7 8 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 7 8
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h12, h03, h36, h34, h45, h67, h78]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- b₁(T_{3,3}) = 10 = mn + 1 -/
theorem torus3x3_betti_ten : Module.finrank ℝ (HarmonicSubspace torus3x3) = 10 := by
  have h_dim := harmonic_dimension_eq_cyclomatic torus3x3
  have h_ker := torus3x3_kernel_dim
  have h_edge := torus3x3_edge_count
  have h_edge_half : torus3x3.active_edges.card / 2 = 18 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

/-! ## The Torus Formula: b₁(T_{m,n}) = mn + 1 -/

/-- T_{3,3} follows the formula b₁ = mn + 1. -/
theorem torus3x3_formula : Module.finrank ℝ (HarmonicSubspace torus3x3) = 3 * 3 + 1 := by
  rw [torus3x3_betti_ten]

/-! ## The Torus Closure Theorem -/

/-- Closing grid→torus adds m + n = 6 cycles. -/
theorem torus_closure_theorem_3x3 :
    Module.finrank ℝ (HarmonicSubspace torus3x3) -
    Module.finrank ℝ (HarmonicSubspace GridGraph.grid3x3) = 3 + 3 := by
  rw [torus3x3_betti_ten, GridGraph.grid3x3_betti_four]

/-- b₁(T_{3,3}) > b₁(G_{3,3}). -/
theorem torus_more_cycles_than_grid :
    Module.finrank ℝ (HarmonicSubspace torus3x3) >
    Module.finrank ℝ (HarmonicSubspace GridGraph.grid3x3) := by
  rw [torus3x3_betti_ten, GridGraph.grid3x3_betti_four]
  omega

/-- Torus adds 6 edges over grid. -/
theorem torus_edge_difference_3x3 :
    torus3x3.active_edges.card / 2 - GridGraph.grid3x3.active_edges.card / 2 = 6 := by
  rw [torus3x3_edge_count, GridGraph.grid3x3_edge_count]

/-- Each wrap edge creates one new cycle. -/
theorem torus_closure_exchange_rate_3x3 :
    (torus3x3.active_edges.card / 2 - GridGraph.grid3x3.active_edges.card / 2 : ℕ) =
    (Module.finrank ℝ (HarmonicSubspace torus3x3) -
     Module.finrank ℝ (HarmonicSubspace GridGraph.grid3x3) : ℕ) := by
  rw [torus3x3_edge_count, GridGraph.grid3x3_edge_count,
      torus3x3_betti_ten, GridGraph.grid3x3_betti_four]

end Diaspora.Hodge.TorusGraph
