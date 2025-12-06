/-
# Path Graph Betti Numbers

The path graph P_n (n vertices in a line) has Betti number:
  b₁(P_n) = 0

This is the archetype of the **classical universe** in Diaspora's language:
no cycles, no paradoxes, no irreducible frustration. Every constraint
is satisfiable; every 1-cochain is exact.

The path graph is the "vacuum state" - the simplest connected structure
with trivial topology. Adding one edge (closing into a cycle) creates
the first unit of harmonic content. This file proves the vacuum has
b₁ = 0, establishing the baseline from which all topology emerges.

Philosophically: The path represents pure hierarchy without circularity.
Information flows from one end to the other without getting trapped.
There are no fossils of contradiction, no frozen paradoxes, no mass.
-/

import Diaspora.Hodge.CycleGraph
import Diaspora.Logic.Classicality

open BigOperators Diaspora.Core Diaspora.Hodge

namespace Diaspora.Hodge.PathGraph

/-! ## Definition: Path Graph P_n -/

/-- Adjacent in path: j = i + 1 or i = j + 1 (consecutive vertices). -/
def pathAdjPred {n : ℕ} (i j : Fin n) : Bool :=
  (i.val + 1 = j.val) || (j.val + 1 = i.val)

/-- The path graph P_n on n vertices (requires n ≥ 2).
    Vertex i is adjacent to vertices i-1 and i+1 (when they exist). -/
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

/-- **Path Graph Betti Number Theorem**: b₁(P_n) = 0 for n ≥ 2.

    The path graph is the archetype of the classical universe:
    - No cycles means no paradoxes
    - Every 1-cochain is exact (satisfiable)
    - Harmonic subspace is trivial

    This is the "vacuum state" - the baseline with zero topology.
-/
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

/-! ## Philosophical Corollaries -/

/-- The path graph is classical: it has no harmonic content. -/
theorem path_graph_is_classical (n : ℕ) [NeZero n] [DecidableEq (Fin n)] (hn : n ≥ 2) :
    Diaspora.Logic.IsClassical (pathGraph n hn) := by
  unfold Diaspora.Logic.IsClassical
  exact path_graph_betti_0 n hn

/-- On the path graph, every ActiveForm is exact (satisfiable). -/
theorem path_graph_all_exact (n : ℕ) [NeZero n] [DecidableEq (Fin n)] (hn : n ≥ 2) :
    ∀ σ : ActiveForm (pathGraph n hn), σ ∈ ImGradient (pathGraph n hn) :=
  Diaspora.Logic.classical_universe_admits_no_paradoxes (pathGraph n hn) (path_graph_is_classical n hn)

/-! ## The Genesis Gap: Path vs Cycle

The path graph P_n has n-1 edges and b₁ = 0.
The cycle graph C_n has n edges and b₁ = 1.

The difference is exactly ONE edge - the "genesis edge" that closes the loop.
That single edge transforms the classical vacuum into a non-classical universe
with irreducible harmonic content.

Formally: P_n + one_edge ≅ C_n, and b₁ jumps from 0 to 1.
-/

/-- The edge count difference between cycle and path is exactly 1.
    This is the "cost of genesis" - one edge creates the first paradox. -/
theorem genesis_costs_one_edge (n : ℕ) [NeZero n] (hn : n ≥ 3) :
    (CycleGraph.cycleGraph n (by omega)).active_edges.card / 2 -
    (pathGraph n (by omega)).active_edges.card / 2 = 1 := by
  have h_cycle := CycleGraph.cycle_graph_directed_edge_count n hn
  have h_path := path_graph_directed_edge_count n (by omega)
  rw [h_cycle, h_path]
  omega

/-- The Betti number jump from path to cycle is exactly 1.
    Closing the loop creates precisely one unit of irreducible frustration. -/
theorem genesis_creates_one_cycle (n : ℕ) [NeZero n] [DecidableEq (Fin n)] (hn : n ≥ 3) :
    Module.finrank ℝ (HarmonicSubspace (CycleGraph.cycleGraph n (by omega))) -
    Module.finrank ℝ (HarmonicSubspace (pathGraph n (by omega))) = 1 := by
  have h_cycle := CycleGraph.cycle_graph_betti_1 n hn
  have h_path := path_graph_betti_0 n (by omega)
  rw [h_cycle, h_path]

end Diaspora.Hodge.PathGraph
