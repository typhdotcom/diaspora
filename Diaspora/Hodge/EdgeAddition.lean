/-
# The Edge Addition Theorem: Genesis at the Atomic Scale

Every graph transition is built from a single primitive operation: adding an edge.
This file proves the fundamental theorem governing this operation:

  **For a connected graph G, adding an edge increases b₁ by exactly 1.**

This is the "atomic genesis" - the indivisible unit of topology creation.

## Why This Matters

The PathGraph to CycleGraph transition is the canonical example:
- P_n has n-1 edges and b₁ = 0 (classical vacuum)
- C_n has n edges and b₁ = 1 (one unit of topology)

That single "genesis edge" connecting the endpoints is worth exactly one cycle.

## Philosophical Interpretation

In Diaspora's language:
- Every new relationship within a connected system creates one unit of paradox
- Genesis is quantized at the edge level
- You cannot add "half a cycle" - topology comes in discrete units
-/

import Diaspora.Hodge.Decomposition
import Diaspora.Hodge.PathGraph
import Diaspora.Hodge.CycleGraph

open BigOperators Diaspora.Core Diaspora.Hodge

namespace Diaspora.Hodge.EdgeAddition

variable {n : ℕ} [Fintype (Fin n)]

/-! ## Definition: Adding an Edge -/

/-- Add a single edge to a graph.
    The edge (i, j) and its symmetric pair (j, i) are added to active_edges. -/
def addEdge (G : DynamicGraph n) (i j : Fin n) (h_ne : i ≠ j)
    (_h_new : (i, j) ∉ G.active_edges) : DynamicGraph n where
  active_edges := insert (j, i) (insert (i, j) G.active_edges)
  symmetric := by
    intro a b
    simp only [Finset.mem_insert, Prod.mk.injEq]
    constructor
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h_orig
      · right; left; exact ⟨h2, h1⟩
      · left; exact ⟨h2, h1⟩
      · right; right; exact (G.symmetric a b).mp h_orig
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h_orig
      · right; left; exact ⟨h2, h1⟩
      · left; exact ⟨h2, h1⟩
      · right; right; exact (G.symmetric b a).mp h_orig
  no_loops := by
    intro a
    simp only [Finset.mem_insert, Prod.mk.injEq]
    intro h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h_orig
    · exact h_ne (h2.symm.trans h1)
    · exact h_ne (h1.symm.trans h2)
    · exact G.no_loops a h_orig

omit [Fintype (Fin n)] in
/-- The edge count increases by exactly 2 (one directed edge each way). -/
lemma addEdge_card (G : DynamicGraph n) (i j : Fin n) (h_ne : i ≠ j)
    (h_new : (i, j) ∉ G.active_edges) :
    (addEdge G i j h_ne h_new).active_edges.card = G.active_edges.card + 2 := by
  simp only [addEdge]
  have h_new_sym : (j, i) ∉ G.active_edges := fun h => h_new ((G.symmetric j i).mp h)
  have h1 : (insert (i, j) G.active_edges).card = G.active_edges.card + 1 :=
    Finset.card_insert_of_notMem h_new
  have h_ji_not_in : (j, i) ∉ insert (i, j) G.active_edges := by
    simp only [Finset.mem_insert, Prod.mk.injEq, not_or]
    refine ⟨?_, h_new_sym⟩
    intro ⟨h1', h2'⟩
    exact h_ne h1'.symm
  have h2 : (insert (j, i) (insert (i, j) G.active_edges)).card =
            (insert (i, j) G.active_edges).card + 1 :=
    Finset.card_insert_of_notMem h_ji_not_in
  omega

/-! ## Connectivity Preservation -/

/-- Adding an edge to a connected graph preserves connectivity. -/
lemma addEdge_preserves_connectivity (G : DynamicGraph n) [hn : NeZero n]
    (i j : Fin n) (h_ne : i ≠ j) (h_new : (i, j) ∉ G.active_edges)
    (h_conn : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1) :
    Module.finrank ℝ (LinearMap.ker (d_G_linear (addEdge G i j h_ne h_new))) = 1 := by
  let G' := addEdge G i j h_ne h_new
  -- Kernel of G' is contained in kernel of G (more edges = more constraints)
  have h_ker_sub : LinearMap.ker (d_G_linear G') ≤ LinearMap.ker (d_G_linear G) := by
    intro φ hφ
    rw [LinearMap.mem_ker] at hφ ⊢
    -- The key: for φ in ker(d_G_linear G'), we have φ b - φ a = 0 for all edges in G'
    -- Since G.active_edges ⊆ G'.active_edges, this implies φ b - φ a = 0 for all edges in G
    ext a b
    show (d_G G φ).val.val a b = 0
    unfold d_G
    by_cases hab : (a, b) ∈ G.active_edges
    · -- If (a,b) is an edge of G, it's also an edge of G'
      have hab' : (a, b) ∈ G'.active_edges := by
        simp only [G', addEdge, Finset.mem_insert]
        right; right; exact hab
      -- From hφ, we know d_G G' φ = 0, so φ b - φ a = 0 for edges of G'
      have hφ_ab : (d_G G' φ).val.val a b = 0 := by
        have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val hφ)) a b
        exact this
      unfold d_G at hφ_ab
      simp only [hab', ↓reduceIte] at hφ_ab
      simp only [hab, ↓reduceIte]
      exact hφ_ab
    · simp only [hab, ↓reduceIte]
  -- Dimension bound
  have h_dim_le : Module.finrank ℝ (LinearMap.ker (d_G_linear G')) ≤ 1 :=
    (Submodule.finrank_mono h_ker_sub).trans_eq h_conn
  -- Kernel is nontrivial (constant functions are always in it)
  have h_dim_pos : 0 < Module.finrank ℝ (LinearMap.ker (d_G_linear G')) := by
    have h_one : (fun _ : Fin n => (1 : ℝ)) ∈ LinearMap.ker (d_G_linear G') := by
      rw [LinearMap.mem_ker]
      ext a b
      show (d_G G' (fun _ => 1)).val.val a b = 0
      simp only [d_G]
      split_ifs <;> ring
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    use ⟨fun _ => 1, h_one⟩
    intro h_eq_zero
    have heq := congr_arg Subtype.val h_eq_zero
    have : (1 : ℝ) = 0 := congr_fun heq ⟨0, hn.pos⟩
    norm_num at this
  simp only [G'] at h_dim_le h_dim_pos ⊢
  omega

/-! ## The Main Theorem -/

/-- **The Edge Addition Theorem**: Adding an edge to a connected graph
    increases the Betti number by exactly 1.
-/
theorem edge_addition_increases_betti (G : DynamicGraph n) [DecidableEq (Fin n)] [NeZero n]
    (i j : Fin n) (h_ne : i ≠ j) (h_new : (i, j) ∉ G.active_edges)
    (h_conn : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1) :
    Module.finrank ℝ (HarmonicSubspace (addEdge G i j h_ne h_new)) =
    Module.finrank ℝ (HarmonicSubspace G) + 1 := by
  have h_conn' := addEdge_preserves_connectivity G i j h_ne h_new h_conn
  have h_G := harmonic_dimension_eq_cyclomatic G
  have h_G' := harmonic_dimension_eq_cyclomatic (addEdge G i j h_ne h_new)
  have h_card := addEdge_card G i j h_ne h_new
  rw [h_conn] at h_G
  rw [h_conn'] at h_G'
  have h_even := active_edges_even_card G
  obtain ⟨k, hk⟩ := h_even
  simp only [h_card, hk] at h_G'
  -- Now h_G' has (k + k + 2) / 2, and h_G has k + k, so use omega directly
  simp only [hk] at h_G
  omega

/-! ## Corollaries -/

/-- The Genesis Gap: path → cycle adds exactly one edge and one cycle. -/
theorem genesis_gap_via_edge_addition (n : ℕ) [NeZero n] [DecidableEq (Fin n)] (hn : n ≥ 3) :
    Module.finrank ℝ (HarmonicSubspace (CycleGraph.cycleGraph n (by omega))) =
    Module.finrank ℝ (HarmonicSubspace (PathGraph.pathGraph n (by omega : n ≥ 2))) + 1 := by
  rw [CycleGraph.cycle_graph_betti_1 n hn, PathGraph.path_graph_betti_0 n (by omega : n ≥ 2)]

/-- Betti number counts excess edges beyond a spanning tree.
    Reformulated: b₁ + (n - 1) = |E| / 2, where |E| / 2 is the number of undirected edges. -/
theorem betti_counts_excess_edges [DecidableEq (Fin n)] [NeZero n] (G : DynamicGraph n)
    (h_conn : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1) :
    Module.finrank ℝ (HarmonicSubspace G) + (n - 1) = G.active_edges.card / 2 := by
  have h := harmonic_dimension_eq_cyclomatic G
  rw [h_conn] at h
  -- Use even card to relate card and card/2
  have h_even := active_edges_even_card G
  obtain ⟨k, hk⟩ := h_even
  have h_div : (k + k) / 2 = k := by omega
  simp only [hk, h_div] at h ⊢
  -- Now h: finrank + n = k + 1, goal: finrank + (n - 1) = k
  have h_n_pos : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  omega

/-- A connected graph is a tree iff it has exactly n-1 edges. -/
theorem tree_characterization [DecidableEq (Fin n)] [NeZero n] (G : DynamicGraph n)
    (h_conn : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1) :
    Module.finrank ℝ (HarmonicSubspace G) = 0 ↔ G.active_edges.card / 2 = n - 1 := by
  have h := betti_counts_excess_edges G h_conn
  have h_even := active_edges_even_card G
  obtain ⟨k, hk⟩ := h_even
  have h_div : (k + k) / 2 = k := by omega
  simp only [hk, h_div] at h ⊢
  -- h: finrank + (n - 1) = k, goal: finrank = 0 ↔ k = n - 1
  have h_n_pos : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  omega

/-! ## Interpretation

The Edge Addition Theorem reveals the atomic structure of genesis:

1. **Quantization**: Topology comes in discrete units.
2. **The Genesis Moment**: Every cycle traces to one "genesis edge."
3. **Accumulation**: K_n achieves (n-1)(n-2)/2 cycles via that many excess edges.
-/

end Diaspora.Hodge.EdgeAddition
