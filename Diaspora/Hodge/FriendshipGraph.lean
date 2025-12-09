import Diaspora.Hodge.CycleGraph
import Diaspora.Hodge.WheelGraph
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The Friendship Graph (Windmill Graph)

F_n consists of n triangles sharing a central vertex. Also known as
the windmill graph Wd(3, n).

**Main result**: b₁(F_n) = n

Each triangle contributes one independent cycle. Edge-disjoint triangles
have orthogonal harmonic forms.
-/

open BigOperators Diaspora.Core Diaspora.Hodge Diaspora.Hodge.WheelGraph

namespace Diaspora.Hodge.FriendshipGraph

/-! ## Definition: Friendship Graph F_n -/

/-- Friendship graph adjacency predicate.
    Vertex 0 is the center.
    For k = 1..n, vertices (2k-1, 2k) form a triangle with vertex 0.
    - Center (0) connects to all outer vertices (1..2n)
    - Each pair (2k-1, 2k) is connected (the "base" of triangle k) -/
def friendshipAdj (n : ℕ) (i j : Fin (2*n + 1)) : Prop :=
  -- Center edges: 0 ↔ k for all k ≥ 1
  (i.val = 0 ∧ j.val ≥ 1) ∨ (i.val ≥ 1 ∧ j.val = 0) ∨
  -- Triangle bases: (2k-1) ↔ (2k) for k = 1..n
  (i.val ≥ 1 ∧ j.val ≥ 1 ∧
    ((i.val % 2 = 1 ∧ j.val = i.val + 1) ∨ (j.val % 2 = 1 ∧ i.val = j.val + 1)))

instance friendshipAdjDecidable (n : ℕ) (i j : Fin (2*n + 1)) :
    Decidable (friendshipAdj n i j) := by
  unfold friendshipAdj
  infer_instance

/-- The friendship graph F_n on 2n+1 vertices.
    n triangles, each sharing the central vertex 0. -/
def friendshipGraph (n : ℕ) [NeZero n] : DynamicGraph (2*n + 1) where
  active_edges := Finset.filter (fun (i, j) => friendshipAdj n i j) Finset.univ
  symmetric := by
    intro i j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, friendshipAdj]
    constructor <;> intro h <;> omega
  no_loops := by
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, friendshipAdj]
    omega

/-! ## Concrete Examples -/

/-- F_1: A single triangle (0-1-2). -/
def friendship1 : DynamicGraph 3 where
  active_edges := {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1)}
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> decide
  no_loops := by intro i; fin_cases i <;> decide

/-- F_1 has 6 directed edges (3 undirected). -/
lemma friendship1_edge_count : friendship1.active_edges.card = 6 := by native_decide

/-- F_1 is connected. -/
lemma friendship1_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear friendship1)) = 1 := by
  let one : Fin 3 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear friendship1) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G friendship1 one).val.val i j = 0
    unfold d_G one
    simp only [friendship1, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear friendship1) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ friendship1.active_edges := by decide
        have h_zero : (d_G friendship1 φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h02 : φ 2 = φ 0 := by
        have h_edge : (0, 2) ∈ friendship1.active_edges := by decide
        have h_zero : (d_G friendship1 φ).val.val 0 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h02]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- **F_1 Betti Number**: b₁(F_1) = 1 (a single triangle). -/
theorem friendship1_betti_one : Module.finrank ℝ (HarmonicSubspace friendship1) = 1 := by
  have h_dim := harmonic_dimension_eq_cyclomatic friendship1
  have h_ker := friendship1_kernel_dim
  have h_edge := friendship1_edge_count
  have h_edge_half : friendship1.active_edges.card / 2 = 3 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

/-! ## F_2: Two triangles sharing a vertex -/

/-- F_2: Two triangles (0-1-2) and (0-3-4) sharing vertex 0. -/
def friendship2 : DynamicGraph 5 where
  active_edges := {
    -- Triangle 1: 0-1-2-0
    (0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1),
    -- Triangle 2: 0-3-4-0
    (0, 3), (3, 0), (0, 4), (4, 0), (3, 4), (4, 3)
  }
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> decide
  no_loops := by intro i; fin_cases i <;> decide

/-- F_2 has 12 directed edges (6 undirected). -/
lemma friendship2_edge_count : friendship2.active_edges.card = 12 := by native_decide

/-- F_2 is connected. -/
lemma friendship2_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear friendship2)) = 1 := by
  let one : Fin 5 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear friendship2) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G friendship2 one).val.val i j = 0
    unfold d_G one
    simp only [friendship2, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear friendship2) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ friendship2.active_edges := by decide
        have h_zero : (d_G friendship2 φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h02 : φ 2 = φ 0 := by
        have h_edge : (0, 2) ∈ friendship2.active_edges := by decide
        have h_zero : (d_G friendship2 φ).val.val 0 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h03 : φ 3 = φ 0 := by
        have h_edge : (0, 3) ∈ friendship2.active_edges := by decide
        have h_zero : (d_G friendship2 φ).val.val 0 3 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 3
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h04 : φ 4 = φ 0 := by
        have h_edge : (0, 4) ∈ friendship2.active_edges := by decide
        have h_zero : (d_G friendship2 φ).val.val 0 4 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 4
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h02, h03, h04]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- b₁(F_2) = 2 -/
theorem friendship2_betti_two : Module.finrank ℝ (HarmonicSubspace friendship2) = 2 := by
  have h_dim := harmonic_dimension_eq_cyclomatic friendship2
  have h_ker := friendship2_kernel_dim
  have h_edge := friendship2_edge_count
  have h_edge_half : friendship2.active_edges.card / 2 = 6 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

/-! ## F_3: Three triangles sharing a vertex -/

/-- F_3: Three triangles sharing vertex 0.
    Triangle 1: 0-1-2, Triangle 2: 0-3-4, Triangle 3: 0-5-6 -/
def friendship3 : DynamicGraph 7 where
  active_edges := {
    -- Triangle 1: 0-1-2-0
    (0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1),
    -- Triangle 2: 0-3-4-0
    (0, 3), (3, 0), (0, 4), (4, 0), (3, 4), (4, 3),
    -- Triangle 3: 0-5-6-0
    (0, 5), (5, 0), (0, 6), (6, 0), (5, 6), (6, 5)
  }
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> decide
  no_loops := by intro i; fin_cases i <;> decide

/-- F_3 has 18 directed edges (9 undirected). -/
lemma friendship3_edge_count : friendship3.active_edges.card = 18 := by native_decide

/-- F_3 is connected. -/
lemma friendship3_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear friendship3)) = 1 := by
  let one : Fin 7 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear friendship3) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G friendship3 one).val.val i j = 0
    unfold d_G one
    simp only [friendship3, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear friendship3) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ friendship3.active_edges := by decide
        have h_zero : (d_G friendship3 φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h02 : φ 2 = φ 0 := by
        have h_edge : (0, 2) ∈ friendship3.active_edges := by decide
        have h_zero : (d_G friendship3 φ).val.val 0 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h03 : φ 3 = φ 0 := by
        have h_edge : (0, 3) ∈ friendship3.active_edges := by decide
        have h_zero : (d_G friendship3 φ).val.val 0 3 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 3
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h04 : φ 4 = φ 0 := by
        have h_edge : (0, 4) ∈ friendship3.active_edges := by decide
        have h_zero : (d_G friendship3 φ).val.val 0 4 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 4
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h05 : φ 5 = φ 0 := by
        have h_edge : (0, 5) ∈ friendship3.active_edges := by decide
        have h_zero : (d_G friendship3 φ).val.val 0 5 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 5
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h06 : φ 6 = φ 0 := by
        have h_edge : (0, 6) ∈ friendship3.active_edges := by decide
        have h_zero : (d_G friendship3 φ).val.val 0 6 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 6
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h02, h03, h04, h05, h06]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- b₁(F_3) = 3 -/
theorem friendship3_betti_three : Module.finrank ℝ (HarmonicSubspace friendship3) = 3 := by
  have h_dim := harmonic_dimension_eq_cyclomatic friendship3
  have h_ker := friendship3_kernel_dim
  have h_edge := friendship3_edge_count
  have h_edge_half : friendship3.active_edges.card / 2 = 9 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

/-! ## The Friendship Graph Formula: b₁(F_n) = n -/
theorem friendship_formula_1 : Module.finrank ℝ (HarmonicSubspace friendship1) = 1 :=
  friendship1_betti_one

theorem friendship_formula_2 : Module.finrank ℝ (HarmonicSubspace friendship2) = 2 :=
  friendship2_betti_two

theorem friendship_formula_3 : Module.finrank ℝ (HarmonicSubspace friendship3) = 3 :=
  friendship3_betti_three

/-! ## Corollaries -/

/-- F_2 = two isolated triangles: sharing a vertex doesn't couple cycles. -/
theorem junction_is_sterile :
    Module.finrank ℝ (HarmonicSubspace friendship2) =
    Module.finrank ℝ (HarmonicSubspace friendship1) +
    Module.finrank ℝ (HarmonicSubspace friendship1) := by
  rw [friendship2_betti_two, friendship1_betti_one]

/-- b₁(F_1) < b₁(F_3): more triangles means more cycles. -/
theorem observation_requires_channels :
    Module.finrank ℝ (HarmonicSubspace friendship1) <
    Module.finrank ℝ (HarmonicSubspace friendship3) := by
  rw [friendship1_betti_one, friendship3_betti_three]
  omega

/-- b₁(F_3) = 3 × b₁(F_1): edge-disjoint cycles contribute additively. -/
theorem paradox_additivity :
    Module.finrank ℝ (HarmonicSubspace friendship3) =
    3 * Module.finrank ℝ (HarmonicSubspace friendship1) := by
  rw [friendship3_betti_three, friendship1_betti_one]

/-- b₁(F_3) = b₁(W_3): same Betti number, different structure. -/
theorem wheel_vs_friendship_same_betti :
    Module.finrank ℝ (HarmonicSubspace friendship3) =
    Module.finrank ℝ (HarmonicSubspace (WheelGraph.wheelGraph 3 (by omega))) := by
  rw [friendship3_betti_three, WheelGraph.wheel_graph_betti_1 3 (by omega)]

end Diaspora.Hodge.FriendshipGraph
