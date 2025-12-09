import Diaspora.Hodge.FriendshipGraph
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The Book Graph

B_n consists of n triangles sharing a common edge (the "spine"). b₁(B_n) = n.
-/

open BigOperators Diaspora.Core Diaspora.Hodge

namespace Diaspora.Hodge.BookGraph

/-! ## Definition: Book Graph B_n -/

/-- Book graph adjacency predicate.
    Vertices 0 and 1 are the spine endpoints.
    For k = 2..n+1, vertex k is a "page" that connects to both 0 and 1.
    - The spine edge: 0 ↔ 1
    - Each page k (for k ≥ 2) connects to both spine endpoints -/
def bookAdj (n : ℕ) (i j : Fin (n + 2)) : Prop :=
  -- The spine edge: 0 ↔ 1
  (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
  -- Page edges: page k (k ≥ 2) connects to both 0 and 1
  (i.val ≥ 2 ∧ (j.val = 0 ∨ j.val = 1)) ∨
  (j.val ≥ 2 ∧ (i.val = 0 ∨ i.val = 1))

instance bookAdjDecidable (n : ℕ) (i j : Fin (n + 2)) : Decidable (bookAdj n i j) := by
  unfold bookAdj
  infer_instance

/-- The book graph B_n on n+2 vertices.
    n triangles, each sharing the spine edge 0-1. -/
def bookGraph (n : ℕ) [NeZero n] : DynamicGraph (n + 2) where
  active_edges := Finset.filter (fun (i, j) => bookAdj n i j) Finset.univ
  symmetric := by
    intro i j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, bookAdj]
    constructor <;> intro h <;> omega
  no_loops := by
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, bookAdj]
    omega

/-! ## Concrete Examples -/

/-- B_1: A single triangle (0-1-2). The spine 0-1 with one page vertex 2. -/
def book1 : DynamicGraph 3 where
  active_edges := {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1)}
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> decide
  no_loops := by intro i; fin_cases i <;> decide

/-- B_1 has 6 directed edges (3 undirected). -/
lemma book1_edge_count : book1.active_edges.card = 6 := by native_decide

/-- B_1 is connected. -/
lemma book1_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear book1)) = 1 := by
  let one : Fin 3 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear book1) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G book1 one).val.val i j = 0
    unfold d_G one
    simp only [book1, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear book1) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ book1.active_edges := by decide
        have h_zero : (d_G book1 φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h02 : φ 2 = φ 0 := by
        have h_edge : (0, 2) ∈ book1.active_edges := by decide
        have h_zero : (d_G book1 φ).val.val 0 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h02]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- **B_1 Betti Number**: b₁(B_1) = 1 (a single triangle). -/
theorem book1_betti_one : Module.finrank ℝ (HarmonicSubspace book1) = 1 := by
  have h_dim := harmonic_dimension_eq_cyclomatic book1
  have h_ker := book1_kernel_dim
  have h_edge := book1_edge_count
  have h_edge_half : book1.active_edges.card / 2 = 3 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

/-! ## B_2: Two triangles sharing the spine -/

/-- B_2: Two triangles sharing spine 0-1. Pages at vertices 2 and 3. -/
def book2 : DynamicGraph 4 where
  active_edges := {
    -- Spine: 0-1
    (0, 1), (1, 0),
    -- Triangle 1: 0-1-2
    (0, 2), (2, 0), (1, 2), (2, 1),
    -- Triangle 2: 0-1-3
    (0, 3), (3, 0), (1, 3), (3, 1)
  }
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> decide
  no_loops := by intro i; fin_cases i <;> decide

/-- B_2 has 10 directed edges (5 undirected: 1 spine + 2×2 page edges). -/
lemma book2_edge_count : book2.active_edges.card = 10 := by native_decide

/-- B_2 is connected. -/
lemma book2_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear book2)) = 1 := by
  let one : Fin 4 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear book2) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G book2 one).val.val i j = 0
    unfold d_G one
    simp only [book2, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear book2) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ book2.active_edges := by decide
        have h_zero : (d_G book2 φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h02 : φ 2 = φ 0 := by
        have h_edge : (0, 2) ∈ book2.active_edges := by decide
        have h_zero : (d_G book2 φ).val.val 0 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h03 : φ 3 = φ 0 := by
        have h_edge : (0, 3) ∈ book2.active_edges := by decide
        have h_zero : (d_G book2 φ).val.val 0 3 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 3
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h02, h03]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- **B_2 Betti Number**: b₁(B_2) = 2

    Two triangles sharing the spine edge. Each triangle contributes one
    independent cycle, even though they share an edge.
-/
theorem book2_betti_two : Module.finrank ℝ (HarmonicSubspace book2) = 2 := by
  have h_dim := harmonic_dimension_eq_cyclomatic book2
  have h_ker := book2_kernel_dim
  have h_edge := book2_edge_count
  have h_edge_half : book2.active_edges.card / 2 = 5 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

/-! ## B_3: Three triangles sharing the spine -/

/-- B_3: Three triangles sharing spine 0-1. Pages at vertices 2, 3, and 4. -/
def book3 : DynamicGraph 5 where
  active_edges := {
    -- Spine: 0-1
    (0, 1), (1, 0),
    -- Triangle 1: 0-1-2
    (0, 2), (2, 0), (1, 2), (2, 1),
    -- Triangle 2: 0-1-3
    (0, 3), (3, 0), (1, 3), (3, 1),
    -- Triangle 3: 0-1-4
    (0, 4), (4, 0), (1, 4), (4, 1)
  }
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> decide
  no_loops := by intro i; fin_cases i <;> decide

/-- B_3 has 14 directed edges (7 undirected: 1 spine + 3×2 page edges). -/
lemma book3_edge_count : book3.active_edges.card = 14 := by native_decide

/-- B_3 is connected. -/
lemma book3_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear book3)) = 1 := by
  let one : Fin 5 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear book3) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G book3 one).val.val i j = 0
    unfold d_G one
    simp only [book3, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear book3) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ book3.active_edges := by decide
        have h_zero : (d_G book3 φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h02 : φ 2 = φ 0 := by
        have h_edge : (0, 2) ∈ book3.active_edges := by decide
        have h_zero : (d_G book3 φ).val.val 0 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h03 : φ 3 = φ 0 := by
        have h_edge : (0, 3) ∈ book3.active_edges := by decide
        have h_zero : (d_G book3 φ).val.val 0 3 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 3
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h04 : φ 4 = φ 0 := by
        have h_edge : (0, 4) ∈ book3.active_edges := by decide
        have h_zero : (d_G book3 φ).val.val 0 4 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 4
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h02, h03, h04]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- **B_3 Betti Number**: b₁(B_3) = 3

    Three triangles sharing the spine edge. Each contributes one independent cycle.
-/
theorem book3_betti_three : Module.finrank ℝ (HarmonicSubspace book3) = 3 := by
  have h_dim := harmonic_dimension_eq_cyclomatic book3
  have h_ker := book3_kernel_dim
  have h_edge := book3_edge_count
  have h_edge_half : book3.active_edges.card / 2 = 7 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

theorem book_formula_1 : Module.finrank ℝ (HarmonicSubspace book1) = 1 := book1_betti_one
theorem book_formula_2 : Module.finrank ℝ (HarmonicSubspace book2) = 2 := book2_betti_two
theorem book_formula_3 : Module.finrank ℝ (HarmonicSubspace book3) = 3 := book3_betti_three

theorem channel_is_transparent :
    Module.finrank ℝ (HarmonicSubspace book2) =
    Module.finrank ℝ (HarmonicSubspace book1) +
    Module.finrank ℝ (HarmonicSubspace book1) := by
  rw [book2_betti_two, book1_betti_one]

theorem triad_same_betti :
    Module.finrank ℝ (HarmonicSubspace book3) =
    Module.finrank ℝ (HarmonicSubspace FriendshipGraph.friendship3) := by
  rw [book3_betti_three, FriendshipGraph.friendship3_betti_three]

theorem vertex_vs_edge_same_result :
    Module.finrank ℝ (HarmonicSubspace book3) =
    Module.finrank ℝ (HarmonicSubspace FriendshipGraph.friendship3) ∧
    Module.finrank ℝ (HarmonicSubspace book2) =
    Module.finrank ℝ (HarmonicSubspace FriendshipGraph.friendship2) := by
  constructor
  · rw [book3_betti_three, FriendshipGraph.friendship3_betti_three]
  · rw [book2_betti_two, FriendshipGraph.friendship2_betti_two]

theorem book_is_economical :
    book3.active_edges.card < FriendshipGraph.friendship3.active_edges.card := by
  rw [book3_edge_count, FriendshipGraph.friendship3_edge_count]
  omega

theorem book_denser_than_friendship :
    (book3.active_edges.card : ℚ) / 2 / 5 >
    (FriendshipGraph.friendship3.active_edges.card : ℚ) / 2 / 7 := by
  rw [book3_edge_count, FriendshipGraph.friendship3_edge_count]
  norm_num

end Diaspora.Hodge.BookGraph
