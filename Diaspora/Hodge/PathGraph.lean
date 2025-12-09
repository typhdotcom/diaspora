import Diaspora.Hodge.CycleGraph
import Diaspora.Logic.Classicality

open BigOperators Diaspora.Core Diaspora.Hodge

/-! # Path Graph: b₁(P_n) = 0 -/

namespace Diaspora.Hodge.PathGraph

def pathAdjPred {n : ℕ} (i j : Fin n) : Bool :=
  (i.val + 1 = j.val) || (j.val + 1 = i.val)

/-- Path graph P_n on n vertices (n ≥ 2). -/
def pathGraph (n : ℕ) [NeZero n] (_hn : n ≥ 2 := by omega) : DynamicGraph n where
  active_edges := Finset.filter
    (fun (i, j) => pathAdjPred i j)
    Finset.univ
  symmetric := by
    intro i j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pathAdjPred,
               Bool.or_eq_true, decide_eq_true_eq]
    tauto
  no_loops := by
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pathAdjPred,
               Bool.or_eq_true, decide_eq_true_eq, not_or]
    omega

/-! ## Edge Count of P_n -/

/-- Forward edges: (i, i+1) for i ∈ {0,...,n-2}. -/
lemma card_forward_edges (n : ℕ) [NeZero n] (hn : n ≥ 2) :
    (Finset.filter (fun p : Fin n × Fin n => p.1.val + 1 = p.2.val) Finset.univ).card = n - 1 := by
  have h_bij : (Finset.filter (fun p : Fin n × Fin n => p.1.val + 1 = p.2.val) Finset.univ) =
      (Finset.univ : Finset (Fin (n-1))).image (fun i : Fin (n-1) =>
        ((⟨i.val, by omega⟩ : Fin n), (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin n))) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro h
      have ha_lt : a.val < n - 1 := by have := b.isLt; omega
      use ⟨a.val, ha_lt⟩
      constructor
      · ext; rfl
      · ext; exact h
    · intro ⟨i, hi⟩
      have h1 : a.val = i.val := by
        have := hi.1; simp only [Fin.ext_iff] at this; exact this.symm
      have h2 : b.val = i.val + 1 := by
        have := hi.2; simp only [Fin.ext_iff] at this; exact this.symm
      omega
  rw [h_bij]
  rw [Finset.card_image_of_injective]
  · simp only [Finset.card_univ, Fintype.card_fin]
  · intro i j h
    simp only [Prod.mk.injEq, Fin.ext_iff] at h
    exact Fin.ext h.1

/-- Backward edges: (i+1, i) for i ∈ {0,...,n-2}. -/
lemma card_backward_edges (n : ℕ) [NeZero n] (hn : n ≥ 2) :
    (Finset.filter (fun p : Fin n × Fin n => p.2.val + 1 = p.1.val) Finset.univ).card = n - 1 := by
  have h_bij : (Finset.filter (fun p : Fin n × Fin n => p.2.val + 1 = p.1.val) Finset.univ) =
      (Finset.univ : Finset (Fin (n-1))).image (fun i : Fin (n-1) =>
        ((⟨i.val + 1, by have := i.isLt; omega⟩ : Fin n), (⟨i.val, by omega⟩ : Fin n))) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro h
      have hb_lt : b.val < n - 1 := by have := a.isLt; omega
      use ⟨b.val, hb_lt⟩
      constructor
      · ext; omega
      · rfl
    · intro ⟨i, hi⟩
      have h1 : a.val = i.val + 1 := by
        have := hi.1; simp only [Fin.ext_iff] at this; exact this.symm
      have h2 : b.val = i.val := by
        have := hi.2; simp only [Fin.ext_iff] at this; exact this.symm
      omega
  rw [h_bij]
  rw [Finset.card_image_of_injective]
  · simp only [Finset.card_univ, Fintype.card_fin]
  · intro i j h
    simp only [Prod.mk.injEq, Fin.ext_iff] at h
    exact Fin.ext h.2

/-- P_n has 2(n-1) directed edges (n-1 undirected edges). -/
lemma path_graph_directed_edge_count (n : ℕ) [NeZero n] (hn : n ≥ 2) :
    (pathGraph n hn).active_edges.card = 2 * (n - 1) := by
  simp only [pathGraph]
  have h_split : (Finset.filter (fun p : Fin n × Fin n => pathAdjPred p.1 p.2) Finset.univ) =
    (Finset.filter (fun p : Fin n × Fin n => p.1.val + 1 = p.2.val) Finset.univ) ∪
    (Finset.filter (fun p : Fin n × Fin n => p.2.val + 1 = p.1.val) Finset.univ) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
               pathAdjPred, Bool.or_eq_true, decide_eq_true_eq]
  rw [h_split]
  have h_disj : Disjoint
    (Finset.filter (fun p : Fin n × Fin n => p.1.val + 1 = p.2.val) Finset.univ)
    (Finset.filter (fun p : Fin n × Fin n => p.2.val + 1 = p.1.val) Finset.univ) := by
    rw [Finset.disjoint_filter]
    intro ⟨a, b⟩ _
    intro h1 h2
    omega
  rw [Finset.card_union_of_disjoint h_disj, card_forward_edges n hn, card_backward_edges n hn]
  ring

/-! ## Connectivity of P_n -/

/-- P_n is connected: the gradient kernel is 1-dimensional (constant functions). -/
lemma path_graph_kernel_dim (n : ℕ) [NeZero n] (hn : n ≥ 2) :
    Module.finrank ℝ (LinearMap.ker (d_G_linear (pathGraph n hn))) = 1 := by
  let one : Fin n → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear (pathGraph n hn)) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G (pathGraph n hn) one).val.val i j = 0
    unfold d_G one
    simp only [pathGraph, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear (pathGraph n hn)) =
                       Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h_const : ∀ i : Fin n, φ i = φ 0 := by
        intro i
        have h_step : ∀ k : ℕ, (hk : k < n) → φ ⟨k, hk⟩ = φ 0 := by
          intro k hk
          induction k with
          | zero => rfl
          | succ m ih =>
            have hm : m < n := by omega
            have h_edge : (⟨m, hm⟩, ⟨m + 1, hk⟩) ∈ (pathGraph n hn).active_edges := by
              simp only [pathGraph, Finset.mem_filter, Finset.mem_univ, true_and,
                         pathAdjPred, Bool.or_eq_true, decide_eq_true_eq]
              left; trivial
            have h_zero : (d_G (pathGraph n hn) φ).val.val ⟨m, hm⟩ ⟨m + 1, hk⟩ = 0 := by
              have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) ⟨m, hm⟩ ⟨m + 1, hk⟩
              exact this
            unfold d_G at h_zero
            simp only [h_edge, ↓reduceIte] at h_zero
            have h_eq : φ ⟨m + 1, hk⟩ = φ ⟨m, hm⟩ := by linarith
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

/-- b₁(P_n) = 0. -/
theorem path_graph_betti_0 (n : ℕ) [NeZero n] [DecidableEq (Fin n)] (hn : n ≥ 2) :
    Module.finrank ℝ (HarmonicSubspace (pathGraph n hn)) = 0 := by
  have h_dim := harmonic_dimension_eq_cyclomatic (pathGraph n hn)
  have h_ker := path_graph_kernel_dim n hn
  have h_edge := path_graph_directed_edge_count n hn
  have h_edge_half : (pathGraph n hn).active_edges.card / 2 = n - 1 := by
    rw [h_edge]; omega
  rw [h_edge_half, h_ker] at h_dim
  omega

/-- P_2 (single edge) has b₁ = 0. -/
theorem P2_betti_zero [DecidableEq (Fin 2)] :
    Module.finrank ℝ (HarmonicSubspace (pathGraph 2 (by omega))) = 0 :=
  path_graph_betti_0 2 (by omega)

/-- P_3 (two edges in a line) has b₁ = 0. -/
theorem P3_betti_zero [DecidableEq (Fin 3)] :
    Module.finrank ℝ (HarmonicSubspace (pathGraph 3 (by omega))) = 0 :=
  path_graph_betti_0 3 (by omega)

/-- P_4 (three edges in a line) has b₁ = 0. -/
theorem P4_betti_zero [DecidableEq (Fin 4)] :
    Module.finrank ℝ (HarmonicSubspace (pathGraph 4 (by omega))) = 0 :=
  path_graph_betti_0 4 (by omega)

theorem path_graph_is_classical (n : ℕ) [NeZero n] [DecidableEq (Fin n)] (hn : n ≥ 2) :
    Diaspora.Logic.IsClassical (pathGraph n hn) := by
  unfold Diaspora.Logic.IsClassical
  exact path_graph_betti_0 n hn

theorem path_graph_all_exact (n : ℕ) [NeZero n] [DecidableEq (Fin n)] (hn : n ≥ 2) :
    ∀ σ : ActiveForm (pathGraph n hn), σ ∈ ImGradient (pathGraph n hn) :=
  Diaspora.Logic.classical_universe_admits_no_paradoxes (pathGraph n hn) (path_graph_is_classical n hn)

/-! ## Path vs Cycle -/

/-- C_n has one more edge than P_n. -/
theorem genesis_costs_one_edge (n : ℕ) [NeZero n] (hn : n ≥ 3) :
    (CycleGraph.cycleGraph n (by omega)).active_edges.card / 2 -
    (pathGraph n (by omega)).active_edges.card / 2 = 1 := by
  have h_cycle := CycleGraph.cycle_graph_directed_edge_count n hn
  have h_path := path_graph_directed_edge_count n (by omega)
  rw [h_cycle, h_path]
  omega

/-- b₁(C_n) - b₁(P_n) = 1. -/
theorem genesis_creates_one_cycle (n : ℕ) [NeZero n] [DecidableEq (Fin n)] (hn : n ≥ 3) :
    Module.finrank ℝ (HarmonicSubspace (CycleGraph.cycleGraph n (by omega))) -
    Module.finrank ℝ (HarmonicSubspace (pathGraph n (by omega))) = 1 := by
  have h_cycle := CycleGraph.cycle_graph_betti_1 n hn
  have h_path := path_graph_betti_0 n (by omega)
  rw [h_cycle, h_path]

end Diaspora.Hodge.PathGraph
