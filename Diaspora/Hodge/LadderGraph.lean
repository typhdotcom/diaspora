import Diaspora.Hodge.IndexTheorem
import Diaspora.Hodge.PrismGraph
import Diaspora.Hodge.PathGraph
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Ladder Graph Betti Numbers

L_n is two parallel n-paths connected by n rungs.

**Main result**: b₁(L_n) = n - 1

**Closure Theorem**: b₁(Prism_n) - b₁(L_n) = 2
-/

open BigOperators Diaspora.Core Diaspora.Hodge

namespace Diaspora.Hodge.LadderGraph

/-! ## Concrete Ladder Graphs for small n -/

/-- L_3: 6 vertices (3 top + 3 bottom). -/
def ladder3 : DynamicGraph 6 where
  active_edges := {
    -- Top path (NOT a cycle - no edge from 2 to 0)
    (0, 1), (1, 0), (1, 2), (2, 1),
    -- Bottom path (NOT a cycle - no edge from 5 to 3)
    (3, 4), (4, 3), (4, 5), (5, 4),
    -- Rungs
    (0, 3), (3, 0), (1, 4), (4, 1), (2, 5), (5, 2)
  }
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> decide
  no_loops := by intro i; fin_cases i <;> decide

/-- L_3 has 14 directed edges (7 undirected: 2 top + 2 bottom + 3 rungs). -/
lemma ladder3_edge_count : ladder3.active_edges.card = 14 := by native_decide

/-- L_3 is connected: kernel dimension = 1. -/
lemma ladder3_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear ladder3)) = 1 := by
  let one : Fin 6 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear ladder3) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G ladder3 one).val.val i j = 0
    unfold d_G one
    simp only [ladder3, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear ladder3) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ ladder3.active_edges := by simp [ladder3]
        have h_zero : (d_G ladder3 φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h12 : φ 2 = φ 1 := by
        have h_edge : (1, 2) ∈ ladder3.active_edges := by simp [ladder3]
        have h_zero : (d_G ladder3 φ).val.val 1 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h03 : φ 3 = φ 0 := by
        have h_edge : (0, 3) ∈ ladder3.active_edges := by simp [ladder3]
        have h_zero : (d_G ladder3 φ).val.val 0 3 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 3
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h34 : φ 4 = φ 3 := by
        have h_edge : (3, 4) ∈ ladder3.active_edges := by simp [ladder3]
        have h_zero : (d_G ladder3 φ).val.val 3 4 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 3 4
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h45 : φ 5 = φ 4 := by
        have h_edge : (4, 5) ∈ ladder3.active_edges := by simp [ladder3]
        have h_zero : (d_G ladder3 φ).val.val 4 5 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 4 5
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h12, h03, h34, h45]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- b₁(L_3) = 2 -/
theorem ladder3_betti_two : Module.finrank ℝ (HarmonicSubspace ladder3) = 2 := by
  have h_dim := harmonic_dimension_eq_cyclomatic ladder3
  have h_ker := ladder3_kernel_dim
  have h_edge := ladder3_edge_count
  have h_edge_half : ladder3.active_edges.card / 2 = 7 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

/-! ## The 4-Ladder -/

/-- L_4: 8 vertices (4 top + 4 bottom). -/
def ladder4 : DynamicGraph 8 where
  active_edges := {
    -- Top path (NOT a cycle - no edge from 3 to 0)
    (0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2),
    -- Bottom path (NOT a cycle - no edge from 7 to 4)
    (4, 5), (5, 4), (5, 6), (6, 5), (6, 7), (7, 6),
    -- Rungs
    (0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2), (3, 7), (7, 3)
  }
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> decide
  no_loops := by intro i; fin_cases i <;> decide

/-- L_4 has 20 directed edges (10 undirected: 3 top + 3 bottom + 4 rungs). -/
lemma ladder4_edge_count : ladder4.active_edges.card = 20 := by native_decide

/-- L_4 is connected: kernel dimension = 1. -/
lemma ladder4_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear ladder4)) = 1 := by
  let one : Fin 8 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear ladder4) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G ladder4 one).val.val i j = 0
    unfold d_G one
    simp only [ladder4, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear ladder4) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ ladder4.active_edges := by simp [ladder4]
        have h_zero : (d_G ladder4 φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h12 : φ 2 = φ 1 := by
        have h_edge : (1, 2) ∈ ladder4.active_edges := by simp [ladder4]
        have h_zero : (d_G ladder4 φ).val.val 1 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h23 : φ 3 = φ 2 := by
        have h_edge : (2, 3) ∈ ladder4.active_edges := by simp [ladder4]
        have h_zero : (d_G ladder4 φ).val.val 2 3 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 2 3
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h04 : φ 4 = φ 0 := by
        have h_edge : (0, 4) ∈ ladder4.active_edges := by simp [ladder4]
        have h_zero : (d_G ladder4 φ).val.val 0 4 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 4
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h45 : φ 5 = φ 4 := by
        have h_edge : (4, 5) ∈ ladder4.active_edges := by simp [ladder4]
        have h_zero : (d_G ladder4 φ).val.val 4 5 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 4 5
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h56 : φ 6 = φ 5 := by
        have h_edge : (5, 6) ∈ ladder4.active_edges := by simp [ladder4]
        have h_zero : (d_G ladder4 φ).val.val 5 6 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 5 6
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h67 : φ 7 = φ 6 := by
        have h_edge : (6, 7) ∈ ladder4.active_edges := by simp [ladder4]
        have h_zero : (d_G ladder4 φ).val.val 6 7 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 6 7
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h12, h23, h04, h45, h56, h67]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- b₁(L_4) = 3 -/
theorem ladder4_betti_three : Module.finrank ℝ (HarmonicSubspace ladder4) = 3 := by
  have h_dim := harmonic_dimension_eq_cyclomatic ladder4
  have h_ker := ladder4_kernel_dim
  have h_edge := ladder4_edge_count
  have h_edge_half : ladder4.active_edges.card / 2 = 10 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

/-! ## The Closure Theorem: b₁(Prism_n) - b₁(L_n) = 2 -/

/-- Closing ladder into prism adds 2 cycles. -/
theorem closure_theorem_3 :
    Module.finrank ℝ (HarmonicSubspace PrismGraph.prism3) -
    Module.finrank ℝ (HarmonicSubspace ladder3) = 2 := by
  rw [PrismGraph.prism3_betti_four, ladder3_betti_two]

/-- Closure theorem for n=4. -/
theorem closure_theorem_4 :
    Module.finrank ℝ (HarmonicSubspace PrismGraph.prism4) -
    Module.finrank ℝ (HarmonicSubspace ladder4) = 2 := by
  rw [PrismGraph.prism4_betti_five, ladder4_betti_three]

/-! ## Pattern Verification: b₁(L_n) = n - 1 -/

/-- L_3 follows the pattern b₁ = n - 1. -/
theorem ladder3_pattern : Module.finrank ℝ (HarmonicSubspace ladder3) = 3 - 1 := by
  rw [ladder3_betti_two]

/-- L_4 follows the pattern b₁ = n - 1. -/
theorem ladder4_pattern : Module.finrank ℝ (HarmonicSubspace ladder4) = 4 - 1 := by
  rw [ladder4_betti_three]

/-! ## Edge Difference: Prism has 2 more edges -/

/-- Prism_3 has 2 more edges than L_3. -/
theorem closure_edge_cost_3 :
    PrismGraph.prism3.active_edges.card / 2 - ladder3.active_edges.card / 2 = 2 := by
  rw [PrismGraph.prism3_edge_count, ladder3_edge_count]

/-- Prism_4 has 2 more edges than L_4. -/
theorem closure_edge_cost_4 :
    PrismGraph.prism4.active_edges.card / 2 - ladder4.active_edges.card / 2 = 2 := by
  rw [PrismGraph.prism4_edge_count, ladder4_edge_count]

/-- Exchange rate: 2 edges → 2 cycles. -/
theorem closure_exchange_rate_3 :
    PrismGraph.prism3.active_edges.card / 2 - ladder3.active_edges.card / 2 =
    Module.finrank ℝ (HarmonicSubspace PrismGraph.prism3) -
    Module.finrank ℝ (HarmonicSubspace ladder3) := by
  rw [PrismGraph.prism3_edge_count, ladder3_edge_count,
      PrismGraph.prism3_betti_four, ladder3_betti_two]

theorem closure_exchange_rate_4 :
    PrismGraph.prism4.active_edges.card / 2 - ladder4.active_edges.card / 2 =
    Module.finrank ℝ (HarmonicSubspace PrismGraph.prism4) -
    Module.finrank ℝ (HarmonicSubspace ladder4) := by
  rw [PrismGraph.prism4_edge_count, ladder4_edge_count,
      PrismGraph.prism4_betti_five, ladder4_betti_three]

end Diaspora.Hodge.LadderGraph
