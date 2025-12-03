/-
# Cycle Graph Betti Numbers

The cycle graph C_n (n-cycle) has Betti number:
  b₁(C_n) = 1

This is the simplest graph with non-trivial topology: exactly one independent cycle.
The proof uses the dimension formula: dim(H) + |V| = |E| + dim(Ker d).
For C_n: n vertices, n edges, connected ⟹ b₁ = n - n + 1 = 1.
-/

import Diaspora.Hodge.IndexTheorem
import Mathlib.LinearAlgebra.Dimension.Finrank

open BigOperators Diaspora.Core Diaspora.Hodge

namespace Diaspora.Hodge.CycleGraph

/-! ## Definition: Cycle Graph C_n -/

/-- Adjacent in cycle: j = i + 1 (mod n). This is decidable. -/
def cycleAdjPred {n : ℕ} [NeZero n] (i j : Fin n) : Bool :=
  j.val == (i.val + 1) % n

/-- The cycle graph C_n on n vertices (requires n ≥ 2).
    Vertex i is adjacent to vertices (i-1) mod n and (i+1) mod n. -/
def cycleGraph (n : ℕ) [NeZero n] (hn : n ≥ 2 := by omega) : DynamicGraph n where
  active_edges := Finset.filter
    (fun (i, j) => cycleAdjPred i j || cycleAdjPred j i)
    Finset.univ
  symmetric := by
    intro i j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.or_eq_true,
               beq_iff_eq, cycleAdjPred]
    tauto
  no_loops := by
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.or_eq_true,
               beq_iff_eq, cycleAdjPred, not_or]
    constructor <;> {
      intro h
      have h1 : i.val = (i.val + 1) % n := h
      have h2 : i.val < n := i.isLt
      have h3 : (i.val + 1) % n ≠ i.val := by
        by_cases h_wrap : i.val + 1 < n
        · rw [Nat.mod_eq_of_lt h_wrap]; omega
        · have h_eq : i.val = n - 1 := by omega
          rw [h_eq]
          have : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
          rw [this, Nat.mod_self]
          omega
      exact h3 h1.symm
    }

/-! ## Edge Count of C_n -/

/-- Helper: count of forward edges (i, i+1). -/
lemma card_forward_edges (n : ℕ) [NeZero n] :
    (Finset.filter (fun p : Fin n × Fin n => cycleAdjPred p.1 p.2) Finset.univ).card = n := by
  have h_bij : (Finset.filter (fun p : Fin n × Fin n => cycleAdjPred p.1 p.2) Finset.univ) =
      Finset.univ.image (fun i : Fin n => (i, ⟨(i.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
               Prod.mk.injEq, cycleAdjPred, beq_iff_eq]
    constructor
    · intro h
      use a
      constructor
      · rfl
      · ext; exact h.symm
    · intro ⟨i, hi⟩
      have h1 : i = a := hi.1
      have h2 : ⟨(i.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩ = b := hi.2
      calc b.val = (⟨(i.val + 1) % n, _⟩ : Fin n).val := by rw [h2]
           _ = (i.val + 1) % n := rfl
           _ = (a.val + 1) % n := by rw [h1]
  rw [h_bij]
  rw [Finset.card_image_of_injective]
  · simp only [Finset.card_univ, Fintype.card_fin]
  · intro i j h
    simp only [Prod.mk.injEq] at h
    exact h.1

/-- Helper: count of backward edges. -/
lemma card_backward_edges (n : ℕ) [NeZero n] :
    (Finset.filter (fun p : Fin n × Fin n => cycleAdjPred p.2 p.1) Finset.univ).card = n := by
  have h_bij : (Finset.filter (fun p : Fin n × Fin n => cycleAdjPred p.2 p.1) Finset.univ) =
      Finset.univ.image (fun i : Fin n => (⟨(i.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩, i)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
               Prod.mk.injEq, cycleAdjPred, beq_iff_eq]
    constructor
    · intro h
      use b
      constructor
      · ext; exact h.symm
      · rfl
    · intro ⟨i, hi⟩
      have h1 : ⟨(i.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩ = a := hi.1
      have h2 : i = b := hi.2
      calc a.val = (⟨(i.val + 1) % n, _⟩ : Fin n).val := by rw [h1]
           _ = (i.val + 1) % n := rfl
           _ = (b.val + 1) % n := by rw [h2]
  rw [h_bij]
  rw [Finset.card_image_of_injective]
  · simp only [Finset.card_univ, Fintype.card_fin]
  · intro i j h
    simp only [Prod.mk.injEq] at h
    exact h.2

/-- C_n has 2n directed edges (n undirected edges). -/
lemma cycle_graph_directed_edge_count (n : ℕ) [NeZero n] (hn : n ≥ 3) :
    (cycleGraph n (by omega)).active_edges.card = 2 * n := by
  simp only [cycleGraph]
  have h_split : (Finset.filter (fun p : Fin n × Fin n =>
      cycleAdjPred p.1 p.2 || cycleAdjPred p.2 p.1) Finset.univ) =
    (Finset.filter (fun p : Fin n × Fin n => cycleAdjPred p.1 p.2) Finset.univ) ∪
    (Finset.filter (fun p : Fin n × Fin n => cycleAdjPred p.2 p.1) Finset.univ) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
               Bool.or_eq_true]
  rw [h_split]
  have h_disj : Disjoint
    (Finset.filter (fun p : Fin n × Fin n => cycleAdjPred p.1 p.2) Finset.univ)
    (Finset.filter (fun p : Fin n × Fin n => cycleAdjPred p.2 p.1) Finset.univ) := by
    rw [Finset.disjoint_filter]
    intro ⟨a, b⟩ _
    simp only [cycleAdjPred, beq_iff_eq]
    intro h1 h2
    -- h1: b.val = (a.val + 1) % n
    -- h2: a.val = (b.val + 1) % n
    -- So a.val = ((a.val + 1) % n + 1) % n
    have h_eq : a.val = ((a.val + 1) % n + 1) % n := by rw [← h1]; exact h2
    -- This implies 2 % n = 0, so n | 2
    have h_a_lt : a.val < n := a.isLt
    by_cases h_wrap1 : a.val + 1 < n
    · rw [Nat.mod_eq_of_lt h_wrap1] at h_eq
      by_cases h_wrap2 : a.val + 2 < n
      · rw [Nat.mod_eq_of_lt h_wrap2] at h_eq; omega
      · have : a.val + 2 = n := by omega
        have ha : a.val = n - 2 := by omega
        rw [ha] at h_eq
        have hsub : n - 2 + 1 + 1 = n := by omega
        rw [hsub, Nat.mod_self] at h_eq
        omega
    · have h_a_max : a.val = n - 1 := by omega
      have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
      rw [h_a_max, hsub, Nat.mod_self] at h_eq
      simp only [Nat.zero_add] at h_eq
      rw [Nat.mod_eq_of_lt (by omega : 1 < n)] at h_eq
      omega
  rw [Finset.card_union_of_disjoint h_disj, card_forward_edges, card_backward_edges]
  ring

/-! ## Connectivity of C_n -/

/-- C_n is connected: the gradient kernel is 1-dimensional (constant functions). -/
lemma cycle_graph_kernel_dim (n : ℕ) [NeZero n] (hn : n ≥ 2) :
    Module.finrank ℝ (LinearMap.ker (d_G_linear (cycleGraph n hn))) = 1 := by
  let one : Fin n → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear (cycleGraph n hn)) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G (cycleGraph n hn) one).val.val i j = 0
    unfold d_G one
    simp only [cycleGraph, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear (cycleGraph n hn)) =
                       Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      -- Show all values equal φ 0 by induction on the vertex index
      have h_const : ∀ i : Fin n, φ i = φ 0 := by
        intro i
        have h_step : ∀ k : ℕ, (hk : k < n) → φ ⟨k, hk⟩ = φ 0 := by
          intro k hk
          induction k with
          | zero => rfl
          | succ m ih =>
            have hm : m < n := by omega
            -- Edge (m, m+1) is active since (m+1) % n is the next vertex
            have h_m_succ : (⟨m, hm⟩, ⟨(m + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩) ∈
                            (cycleGraph n hn).active_edges := by
              simp only [cycleGraph, Finset.mem_filter, Finset.mem_univ, true_and,
                         Bool.or_eq_true, cycleAdjPred, beq_iff_eq]
              left
              simp
            have h_zero : (d_G (cycleGraph n hn) φ).val.val ⟨m, hm⟩
                ⟨(m + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩ = 0 := by
              have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) ⟨m, hm⟩
                ⟨(m + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩
              exact this
            unfold d_G at h_zero
            simp only [h_m_succ, ↓reduceIte] at h_zero
            -- h_zero : φ ⟨(m+1) % n, _⟩ - φ ⟨m, _⟩ = 0
            have h_mod : (m + 1) % n = m + 1 := Nat.mod_eq_of_lt hk
            have h_eq : φ ⟨(m + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩ = φ ⟨m, hm⟩ := by linarith
            -- Convert ⟨(m+1) % n, _⟩ to ⟨m+1, hk⟩
            have h_fin_eq : (⟨(m + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩ : Fin n) = ⟨m + 1, hk⟩ := by
              ext; exact h_mod
            rw [h_fin_eq] at h_eq
            rw [h_eq, ih hm]
        exact h_step i.val i.isLt
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i
      simp only [one, Pi.smul_apply, smul_eq_mul, mul_one, (h_const i).symm]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h
  have : (1 : ℝ) = 0 := congr_fun h 0
  norm_num at this

/-! ## The Main Theorem -/

/-- **Cycle Graph Betti Number Theorem**: b₁(C_n) = 1 for n ≥ 3.

    The n-cycle is the simplest graph with non-trivial topology.
    It has exactly one independent cycle, hence b₁ = 1.
-/
theorem cycle_graph_betti_1 (n : ℕ) [NeZero n] [DecidableEq (Fin n)] (hn : n ≥ 3) :
    Module.finrank ℝ (HarmonicSubspace (cycleGraph n (by omega))) = 1 := by
  have h_dim := harmonic_dimension_eq_cyclomatic (cycleGraph n (by omega))
  have h_ker := cycle_graph_kernel_dim n (by omega : n ≥ 2)
  have h_edge := cycle_graph_directed_edge_count n hn
  have h_edge_half : (cycleGraph n (by omega)).active_edges.card / 2 = n := by
    rw [h_edge]; omega
  rw [h_edge_half, h_ker] at h_dim
  omega

/-- C_3 (triangle) has b₁ = 1. -/
theorem C3_betti_one [DecidableEq (Fin 3)] :
    Module.finrank ℝ (HarmonicSubspace (cycleGraph 3 (by omega))) = 1 :=
  cycle_graph_betti_1 3 (by omega)

/-- C_4 (square) has b₁ = 1. -/
theorem C4_betti_one [DecidableEq (Fin 4)] :
    Module.finrank ℝ (HarmonicSubspace (cycleGraph 4 (by omega))) = 1 :=
  cycle_graph_betti_1 4 (by omega)

/-- C_5 (pentagon) has b₁ = 1. -/
theorem C5_betti_one [DecidableEq (Fin 5)] :
    Module.finrank ℝ (HarmonicSubspace (cycleGraph 5 (by omega))) = 1 :=
  cycle_graph_betti_1 5 (by omega)

/-- C_n has exactly one independent cycle for any n ≥ 3. -/
theorem cycle_graph_has_one_cycle (n : ℕ) [NeZero n] [DecidableEq (Fin n)] (hn : n ≥ 3) :
    Module.finrank ℝ (HarmonicSubspace (cycleGraph n (by omega))) = 1 :=
  cycle_graph_betti_1 n hn

end Diaspora.Hodge.CycleGraph
