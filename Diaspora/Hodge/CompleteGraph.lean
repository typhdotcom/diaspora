/-
# Complete Graph Betti Numbers

The complete graph K_n has a beautiful closed-form Betti number:
  b₁(K_n) = (n-1)(n-2)/2

This is the maximum possible first Betti number for any graph on n vertices.
-/

import Diaspora.Hodge.IndexTheorem
import Mathlib.LinearAlgebra.Dimension.Finrank

open BigOperators Diaspora.Core Diaspora.Hodge

namespace Diaspora.Hodge.CompleteGraph

/-! ## Edge Count of Complete Graph -/

/-- The complete graph K_n has n(n-1) directed edges. -/
lemma complete_graph_directed_edge_count (n : ℕ) [DecidableEq (Fin n)] :
    (DynamicGraph.complete n).active_edges.card = n * (n - 1) := by
  -- active_edges = {(i,j) | i ≠ j}
  simp only [DynamicGraph.complete]
  -- Total pairs = n²
  have h_total : (Finset.univ : Finset (Fin n × Fin n)).card = n * n := by
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  -- Diagonal pairs = n
  let diag := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 = p.2)
  have h_diag : diag.card = n := by
    have h_eq : diag = Finset.univ.image (fun i : Fin n => (i, i)) := by
      ext ⟨a, b⟩
      simp only [diag, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
                 Prod.mk.injEq, exists_eq_left]
    rw [h_eq, Finset.card_image_of_injective]
    · simp only [Finset.card_univ, Fintype.card_fin]
    · intro a b h; exact (Prod.mk.inj h).1
  -- Off-diagonal = total - diagonal
  have h_compl : Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2) = Finset.univ \ diag := by
    ext p
    simp only [diag, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, ne_eq]
  have h_sub : diag ⊆ Finset.univ := Finset.filter_subset _ _
  have h_card : (Finset.univ \ diag).card + diag.card = Finset.univ.card :=
    Finset.card_sdiff_add_card_eq_card h_sub
  simp only [h_total, h_diag] at h_card
  -- Show the Finsets are equal
  have h_sdiff_card : (Finset.univ \ diag).card = n * n - n := by omega
  -- n * n - n = n * (n - 1)
  have h_arith : n * n - n = n * (n - 1) := by
    cases n with
    | zero => rfl
    | succ m =>
      simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      have : (m + 1) * (m + 1) - (m + 1) = (m + 1) * m := by
        have h1 : (m + 1) * (m + 1) = (m + 1) * m + (m + 1) := by ring
        omega
      exact this
  -- Convert the goal to use (Finset.univ \ diag)
  suffices h : (Finset.univ \ diag).card = n * (n - 1) by
    convert h using 1
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, diag, ne_eq]
  rw [h_sdiff_card, h_arith]

/-- The complete graph K_n has n(n-1)/2 undirected edges. -/
theorem complete_graph_undirected_edge_count (n : ℕ) [DecidableEq (Fin n)] :
    (DynamicGraph.complete n).active_edges.card / 2 = n * (n - 1) / 2 := by
  rw [complete_graph_directed_edge_count]

/-! ## Connectivity of Complete Graph -/

/-- The gradient kernel on K_n is 1-dimensional. -/
lemma complete_graph_kernel_dim (n : ℕ) [DecidableEq (Fin n)] [NeZero n] :
    Module.finrank ℝ (LinearMap.ker (d_G_linear (DynamicGraph.complete n))) = 1 := by
  let one : Fin n → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear (DynamicGraph.complete n)) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G (DynamicGraph.complete n) one).val.val i j = 0
    unfold d_G one
    simp only [DynamicGraph.complete, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear (DynamicGraph.complete n)) =
                       Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h_const : ∀ i : Fin n, φ i = φ 0 := by
        intro i
        by_cases h : i = 0
        · rw [h]
        · have h_neq : ¬(0 : Fin n) = i := fun h' => h h'.symm
          have h_edge : (0, i) ∈ (DynamicGraph.complete n).active_edges := by
            simp [DynamicGraph.complete, h_neq]
          have h_zero : (d_G (DynamicGraph.complete n) φ).val.val 0 i = 0 := by
            have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 i
            exact this
          unfold d_G at h_zero
          simp only [h_edge, ↓reduceIte] at h_zero
          linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i
      simp only [one, Pi.smul_apply, smul_eq_mul, mul_one, (h_const i).symm]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h
  have : (1 : ℝ) = 0 := congr_fun h 0
  norm_num at this

/-! ## Key Algebraic Lemma -/

/-- Key algebraic identity: n(n-1)/2 + 1 = (n-1)(n-2)/2 + n for n ≥ 1. -/
lemma betti_algebra_key (n : ℕ) (hn : n ≥ 1) : n * (n - 1) / 2 + 1 = (n - 1) * (n - 2) / 2 + n := by
  match n with
  | 0 => omega
  | 1 => decide
  | k + 2 =>
    -- n = k + 2, so n - 1 = k + 1, n - 2 = k
    have h1 : k + 2 - 1 = k + 1 := by omega
    have h2 : k + 2 - 2 = k := by omega
    simp only [h1, h2]
    -- (k+2)(k+1) = (k+1)k + 2(k+1)
    have h_expand : (k + 2) * (k + 1) = (k + 1) * k + 2 * (k + 1) := by ring
    -- (k+1)*k is even (product of consecutive integers)
    have h_even : 2 ∣ (k + 1) * k := by
      rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- k = 2m, so k+1 is odd, k is even
        refine ⟨m * (k + 1), ?_⟩
        subst hm
        ring
      · -- k = 2m + 1, so k+1 = 2(m+1) is even
        refine ⟨(m + 1) * k, ?_⟩
        subst hm
        ring
    rw [h_expand]
    rw [Nat.add_div_of_dvd_right h_even]
    rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    omega

/-! ## The Main Theorem -/

variable {n : ℕ}

/-- **Complete Graph Betti Number Theorem**: b₁(K_n) = (n-1)(n-2)/2 -/
theorem complete_graph_betti_1 [DecidableEq (Fin n)] [NeZero n] :
    Module.finrank ℝ (HarmonicSubspace (DynamicGraph.complete n)) = (n - 1) * (n - 2) / 2 := by
  have h_dim := harmonic_dimension_eq_cyclomatic (DynamicGraph.complete n)
  have h_ker := complete_graph_kernel_dim n
  have h_edge := complete_graph_directed_edge_count n
  have h_alg := betti_algebra_key n (NeZero.pos n)
  omega

/-- For n ≥ 3, K_n has cycles. -/
theorem complete_graph_has_cycles [DecidableEq (Fin n)] [NeZero n] (h : n ≥ 3) :
    Module.finrank ℝ (HarmonicSubspace (DynamicGraph.complete n)) ≥ 1 := by
  rw [complete_graph_betti_1]
  have h1 : n - 1 ≥ 2 := by omega
  have h2 : n - 2 ≥ 1 := by omega
  have : (n - 1) * (n - 2) ≥ 2 := by nlinarith
  omega

/-- K_2 is a tree. -/
theorem K2_is_tree [DecidableEq (Fin 2)] :
    Module.finrank ℝ (HarmonicSubspace (DynamicGraph.complete 2)) = 0 := by
  simp [complete_graph_betti_1]

/-- K_3 has exactly one cycle. -/
theorem K3_betti_one [DecidableEq (Fin 3)] :
    Module.finrank ℝ (HarmonicSubspace (DynamicGraph.complete 3)) = 1 := by
  simp [complete_graph_betti_1]

/-- K_4 has three independent cycles. -/
theorem K4_betti_three [DecidableEq (Fin 4)] :
    Module.finrank ℝ (HarmonicSubspace (DynamicGraph.complete 4)) = 3 := by
  simp [complete_graph_betti_1]

end Diaspora.Hodge.CompleteGraph
