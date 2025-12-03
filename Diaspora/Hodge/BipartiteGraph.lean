/-
# Complete Bipartite Graph Betti Numbers

The complete bipartite graph K_{m,n} has Betti number:
  b₁(K_{m,n}) = (m-1)(n-1)

This reveals beautiful structure:
- K_{1,n} (star) is a tree: b₁ = 0
- K_{2,2} is a 4-cycle: b₁ = 1
- K_{m,n} with m,n ≥ 2 has cycles

The formula (m-1)(n-1) counts independent cycles: each of the (m-1)(n-1)
"fundamental squares" in the grid contributes one cycle mode.
-/

import Diaspora.Hodge.IndexTheorem
import Mathlib.LinearAlgebra.Dimension.Finrank

open BigOperators Diaspora.Core Diaspora.Hodge

namespace Diaspora.Hodge.BipartiteGraph

/-! ## Definition: Complete Bipartite Graph K_{m,n} -/

/-- The complete bipartite graph K_{m,n} on m+n vertices.
    Vertices 0..(m-1) form part A, vertices m..(m+n-1) form part B.
    Every vertex in A is adjacent to every vertex in B. -/
def completeBipartite (m n : ℕ) : DynamicGraph (m + n) where
  active_edges := Finset.filter
    (fun (i, j) =>
      (i.val < m ∧ j.val ≥ m) ∨ (i.val ≥ m ∧ j.val < m))
    Finset.univ
  symmetric := by
    intro i j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  no_loops := by
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega

/-! ## Edge Count of K_{m,n} -/

/-- Helper: the set of cross-edges A→B. -/
lemma card_cross_pairs (m n : ℕ) :
    (Finset.filter (fun p : Fin (m + n) × Fin (m + n) => p.1.val < m ∧ p.2.val ≥ m)
      Finset.univ).card = m * n := by
  -- Direct counting via product structure
  have h_eq : (Finset.filter (fun p : Fin (m + n) × Fin (m + n) => p.1.val < m ∧ p.2.val ≥ m)
      Finset.univ) =
    (Finset.filter (fun i : Fin (m + n) => i.val < m) Finset.univ) ×ˢ
    (Finset.filter (fun j : Fin (m + n) => j.val ≥ m) Finset.univ) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  rw [h_eq, Finset.card_product]
  -- Count vertices in part A: those with i < m
  have h_A : (Finset.filter (fun i : Fin (m + n) => i.val < m) Finset.univ).card = m := by
    let embed_A : Fin m ↪ Fin (m + n) :=
      ⟨fun i => ⟨i.val, Nat.lt_add_right n i.isLt⟩,
       fun i j h => by simp only [Fin.mk.injEq] at h; exact Fin.ext h⟩
    have h_eq' : (Finset.filter (fun i : Fin (m + n) => i.val < m) Finset.univ) =
        (Finset.univ : Finset (Fin m)).map embed_A := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, embed_A,
                 Function.Embedding.coeFn_mk]
      constructor
      · intro hi; use ⟨i.val, hi⟩
      · intro ⟨j, hj⟩; rw [← hj]; exact j.isLt
    rw [h_eq', Finset.card_map, Finset.card_univ, Fintype.card_fin]
  -- Count vertices in part B: those with j ≥ m
  have h_B : (Finset.filter (fun j : Fin (m + n) => j.val ≥ m) Finset.univ).card = n := by
    let embed_B : Fin n ↪ Fin (m + n) :=
      ⟨fun j => ⟨j.val + m, by omega⟩,
       fun i j h => by simp only [Fin.mk.injEq] at h; omega⟩
    have h_eq' : (Finset.filter (fun j : Fin (m + n) => j.val ≥ m) Finset.univ) =
        (Finset.univ : Finset (Fin n)).map embed_B := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, embed_B,
                 Function.Embedding.coeFn_mk]
      constructor
      · intro hj
        have hlt : j.val - m < n := by omega
        use ⟨j.val - m, hlt⟩; ext; simp; omega
      · intro ⟨k, hk⟩; rw [← hk]; simp
    rw [h_eq', Finset.card_map, Finset.card_univ, Fintype.card_fin]
  rw [h_A, h_B]

/-- Helper: the set of cross-edges B→A. -/
lemma card_cross_pairs' (m n : ℕ) :
    (Finset.filter (fun p : Fin (m + n) × Fin (m + n) => p.1.val ≥ m ∧ p.2.val < m)
      Finset.univ).card = n * m := by
  have h_eq : (Finset.filter (fun p : Fin (m + n) × Fin (m + n) => p.1.val ≥ m ∧ p.2.val < m)
      Finset.univ) =
    (Finset.filter (fun i : Fin (m + n) => i.val ≥ m) Finset.univ) ×ˢ
    (Finset.filter (fun j : Fin (m + n) => j.val < m) Finset.univ) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  rw [h_eq, Finset.card_product]
  have h_B : (Finset.filter (fun i : Fin (m + n) => i.val ≥ m) Finset.univ).card = n := by
    let embed_B : Fin n ↪ Fin (m + n) :=
      ⟨fun j => ⟨j.val + m, by omega⟩,
       fun i j h => by simp only [Fin.mk.injEq] at h; omega⟩
    have h_eq' : (Finset.filter (fun j : Fin (m + n) => j.val ≥ m) Finset.univ) =
        (Finset.univ : Finset (Fin n)).map embed_B := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, embed_B,
                 Function.Embedding.coeFn_mk]
      constructor
      · intro hj
        have hlt : j.val - m < n := by omega
        use ⟨j.val - m, hlt⟩; ext; simp; omega
      · intro ⟨k, hk⟩; rw [← hk]; simp
    rw [h_eq', Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have h_A : (Finset.filter (fun j : Fin (m + n) => j.val < m) Finset.univ).card = m := by
    let embed_A : Fin m ↪ Fin (m + n) :=
      ⟨fun i => ⟨i.val, Nat.lt_add_right n i.isLt⟩,
       fun i j h => by simp only [Fin.mk.injEq] at h; exact Fin.ext h⟩
    have h_eq' : (Finset.filter (fun i : Fin (m + n) => i.val < m) Finset.univ) =
        (Finset.univ : Finset (Fin m)).map embed_A := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, embed_A,
                 Function.Embedding.coeFn_mk]
      constructor
      · intro hi; use ⟨i.val, hi⟩
      · intro ⟨j, hj⟩; rw [← hj]; exact j.isLt
    rw [h_eq', Finset.card_map, Finset.card_univ, Fintype.card_fin]
  rw [h_B, h_A]

/-- K_{m,n} has 2mn directed edges (mn undirected edges). -/
lemma bipartite_directed_edge_count (m n : ℕ) :
    (completeBipartite m n).active_edges.card = 2 * m * n := by
  simp only [completeBipartite]
  have h_split : (Finset.filter (fun p : Fin (m + n) × Fin (m + n) =>
      (p.1.val < m ∧ p.2.val ≥ m) ∨ (p.1.val ≥ m ∧ p.2.val < m)) Finset.univ) =
    (Finset.filter (fun p : Fin (m + n) × Fin (m + n) => p.1.val < m ∧ p.2.val ≥ m) Finset.univ) ∪
    (Finset.filter (fun p : Fin (m + n) × Fin (m + n) => p.1.val ≥ m ∧ p.2.val < m) Finset.univ) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  rw [h_split]
  have h_disj : Disjoint
    (Finset.filter (fun p : Fin (m + n) × Fin (m + n) => p.1.val < m ∧ p.2.val ≥ m) Finset.univ)
    (Finset.filter (fun p : Fin (m + n) × Fin (m + n) => p.1.val ≥ m ∧ p.2.val < m) Finset.univ) := by
    rw [Finset.disjoint_filter]
    intro p _ h1; omega
  rw [Finset.card_union_of_disjoint h_disj, card_cross_pairs, card_cross_pairs']
  ring

/-! ## Connectivity of K_{m,n} -/

/-- K_{m,n} is connected when m,n ≥ 1: the kernel of the gradient is 1-dimensional. -/
lemma bipartite_kernel_dim (m n : ℕ) [NeZero m] [NeZero n] :
    Module.finrank ℝ (LinearMap.ker (d_G_linear (completeBipartite m n))) = 1 := by
  let one : Fin (m + n) → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear (completeBipartite m n)) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G (completeBipartite m n) one).val.val i j = 0
    unfold d_G one
    simp only [completeBipartite, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear (completeBipartite m n)) =
                       Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h_const : ∀ i : Fin (m + n), φ i = φ 0 := by
        intro i
        have hm_pos : m ≥ 1 := NeZero.pos m
        have hn_pos : n ≥ 1 := NeZero.pos n
        let bridge : Fin (m + n) := ⟨m, by omega⟩
        have h_bridge_ge : bridge.val ≥ m := le_refl m
        have h_0_lt : (0 : Fin (m + n)).val < m := by simp; omega
        have h_0_bridge : ((0 : Fin (m + n)), bridge) ∈ (completeBipartite m n).active_edges := by
          simp only [completeBipartite, Finset.mem_filter, Finset.mem_univ, true_and]
          left; exact ⟨h_0_lt, h_bridge_ge⟩
        have h_eq_0_bridge : (d_G (completeBipartite m n) φ).val.val 0 bridge = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 bridge
          exact this
        unfold d_G at h_eq_0_bridge
        simp only [h_0_bridge, ↓reduceIte] at h_eq_0_bridge
        have h_bridge_eq_0 : φ bridge = φ 0 := by linarith
        by_cases hi : i.val < m
        · have h_i_bridge : (i, bridge) ∈ (completeBipartite m n).active_edges := by
            simp only [completeBipartite, Finset.mem_filter, Finset.mem_univ, true_and]
            left; exact ⟨hi, h_bridge_ge⟩
          have h_eq_i_bridge : (d_G (completeBipartite m n) φ).val.val i bridge = 0 := by
            have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) i bridge
            exact this
          unfold d_G at h_eq_i_bridge
          simp only [h_i_bridge, ↓reduceIte] at h_eq_i_bridge
          linarith
        · have hi' : i.val ≥ m := by omega
          have h_i_0 : (i, (0 : Fin (m + n))) ∈ (completeBipartite m n).active_edges := by
            simp only [completeBipartite, Finset.mem_filter, Finset.mem_univ, true_and]
            right; exact ⟨hi', h_0_lt⟩
          have h_eq_i_0 : (d_G (completeBipartite m n) φ).val.val i 0 = 0 := by
            have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) i 0
            exact this
          unfold d_G at h_eq_i_0
          simp only [h_i_0, ↓reduceIte] at h_eq_i_0
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

/-! ## Key Algebraic Identity -/

/-- Key algebraic identity for bipartite Betti number. -/
lemma betti_algebra_bipartite (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1) :
    m * n + 1 = (m - 1) * (n - 1) + (m + n) := by
  match m, n with
  | 0, _ => omega
  | _, 0 => omega
  | m' + 1, n' + 1 =>
    simp only [Nat.add_sub_cancel]
    ring

/-! ## The Main Theorem -/

/-- **Complete Bipartite Graph Betti Number**: b₁(K_{m,n}) = (m-1)(n-1) -/
theorem bipartite_betti_1 (m n : ℕ) [NeZero m] [NeZero n] [DecidableEq (Fin (m + n))] :
    Module.finrank ℝ (HarmonicSubspace (completeBipartite m n)) = (m - 1) * (n - 1) := by
  have h_dim := harmonic_dimension_eq_cyclomatic (completeBipartite m n)
  have h_ker := bipartite_kernel_dim m n
  have h_edge := bipartite_directed_edge_count m n
  have hm : m ≥ 1 := NeZero.pos m
  have hn : n ≥ 1 := NeZero.pos n
  have h_alg := betti_algebra_bipartite m n hm hn
  have h_edge_half : (completeBipartite m n).active_edges.card / 2 = m * n := by
    rw [h_edge]
    simp only [Nat.mul_assoc]
    omega
  rw [h_edge_half, h_ker] at h_dim
  omega

/-! ## Corollaries -/

/-- K_{1,n} (star graph) is a tree: b₁ = 0. -/
theorem star_is_tree (n : ℕ) [NeZero n] [DecidableEq (Fin (1 + n))] :
    Module.finrank ℝ (HarmonicSubspace (completeBipartite 1 n)) = 0 := by
  have := bipartite_betti_1 1 n
  simp at this ⊢
  exact this

/-- K_{2,2} is a 4-cycle: b₁ = 1. -/
theorem K22_is_cycle [DecidableEq (Fin 4)] :
    Module.finrank ℝ (HarmonicSubspace (completeBipartite 2 2)) = 1 := by
  have := bipartite_betti_1 2 2
  norm_num at this ⊢
  exact this

/-- K_{3,3} has 4 independent cycles. -/
theorem K33_betti_four [DecidableEq (Fin 6)] :
    Module.finrank ℝ (HarmonicSubspace (completeBipartite 3 3)) = 4 := by
  have := bipartite_betti_1 3 3
  norm_num at this ⊢
  exact this

/-- K_{m,n} with m,n ≥ 2 has at least one cycle. -/
theorem bipartite_has_cycles (m n : ℕ) [NeZero m] [NeZero n] [DecidableEq (Fin (m + n))]
    (hm : m ≥ 2) (hn : n ≥ 2) :
    Module.finrank ℝ (HarmonicSubspace (completeBipartite m n)) ≥ 1 := by
  rw [bipartite_betti_1]
  have h1 : m - 1 ≥ 1 := by omega
  have h2 : n - 1 ≥ 1 := by omega
  have : (m - 1) * (n - 1) ≥ 1 := by
    calc (m - 1) * (n - 1) ≥ 1 * 1 := Nat.mul_le_mul h1 h2
      _ = 1 := by ring
  exact this

end Diaspora.Hodge.BipartiteGraph
