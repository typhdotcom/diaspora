import Diaspora.Hodge.CompleteGraph
import Diaspora.Hodge.CycleGraph
import Diaspora.Hodge.PathGraph

/-!
# The Maximum Topology Theorem

b₁(G) ≤ b₁(K_n) = (n-1)(n-2)/2 for connected graphs on n vertices.
-/

open BigOperators Diaspora.Core Diaspora.Hodge

namespace Diaspora.Hodge.MaximumTopology

variable {n : ℕ}

/-! ## Edge Count Bounds -/

/-- Every simple graph on n vertices has at most n(n-1)/2 undirected edges.
    The complete graph saturates this bound. -/
lemma edge_count_le_complete [DecidableEq (Fin n)] (G : DynamicGraph n) :
    G.active_edges.card ≤ n * (n - 1) := by
  have h_sub : G.active_edges ⊆ (DynamicGraph.complete n).active_edges := by
    intro ⟨i, j⟩ h_mem
    simp only [DynamicGraph.complete, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun h_eq => G.no_loops i (h_eq ▸ h_mem)
  calc G.active_edges.card
      ≤ (DynamicGraph.complete n).active_edges.card := Finset.card_le_card h_sub
    _ = n * (n - 1) := CompleteGraph.complete_graph_directed_edge_count n

/-- Undirected edge count bound. -/
lemma undirected_edge_count_le_complete [DecidableEq (Fin n)] (G : DynamicGraph n) :
    G.active_edges.card / 2 ≤ n * (n - 1) / 2 := by
  exact Nat.div_le_div_right (edge_count_le_complete G)

/-! ## The Betti Number Bound -/

/-- **The Maximum Topology Theorem**: For connected graphs, b₁(G) ≤ b₁(K_n).

    The complete graph achieves the maximum possible first Betti number
    among all graphs on n vertices.

    Proof: The Betti number satisfies b₁ + n = |E| + 1 for connected graphs.
    Since |E(G)| ≤ |E(K_n)|, we get b₁(G) ≤ b₁(K_n).
-/
theorem betti_one_le_complete [DecidableEq (Fin n)] [NeZero n] (G : DynamicGraph n)
    (h_conn : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1) :
    Module.finrank ℝ (HarmonicSubspace G) ≤
    Module.finrank ℝ (HarmonicSubspace (DynamicGraph.complete n)) := by
  have h_G := harmonic_dimension_eq_cyclomatic G
  have h_Kn := harmonic_dimension_eq_cyclomatic (DynamicGraph.complete n)
  have h_Kn_conn := CompleteGraph.complete_graph_kernel_dim n
  have h_edge_dir := edge_count_le_complete G
  have h_G_even := active_edges_even_card G
  have h_Kn_even := active_edges_even_card (DynamicGraph.complete n)
  rw [h_conn] at h_G
  rw [h_Kn_conn] at h_Kn
  obtain ⟨kG, hkG⟩ := h_G_even
  obtain ⟨kKn, hkKn⟩ := h_Kn_even
  have h_G_half : G.active_edges.card / 2 = kG := by rw [hkG]; omega
  have h_Kn_half : (DynamicGraph.complete n).active_edges.card / 2 = kKn := by rw [hkKn]; omega
  rw [h_G_half] at h_G
  rw [h_Kn_half] at h_Kn
  have h_edge_half : kG ≤ kKn := by
    have h1 : G.active_edges.card / 2 ≤ (n * (n - 1)) / 2 := Nat.div_le_div_right h_edge_dir
    have h2 : (n * (n - 1)) / 2 = (DynamicGraph.complete n).active_edges.card / 2 := by
      rw [CompleteGraph.complete_graph_directed_edge_count]
    rw [h_G_half, h2, h_Kn_half] at h1
    exact h1
  omega

/-- The Betti bound in explicit form. -/
theorem betti_one_le_formula [DecidableEq (Fin n)] [NeZero n] (G : DynamicGraph n)
    (h_conn : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1) :
    Module.finrank ℝ (HarmonicSubspace G) ≤ (n - 1) * (n - 2) / 2 := by
  calc Module.finrank ℝ (HarmonicSubspace G)
      ≤ Module.finrank ℝ (HarmonicSubspace (DynamicGraph.complete n)) :=
          betti_one_le_complete G h_conn
    _ = (n - 1) * (n - 2) / 2 := CompleteGraph.complete_graph_betti_1

/-! ## Edge-Topology Monotonicity -/

/-- More edges implies higher Betti number (for connected graphs).

    If G ⊆ H as edge sets and both are connected, then b₁(G) ≤ b₁(H).
    Topology is monotonic in connectivity.
-/
theorem betti_monotone_in_edges [DecidableEq (Fin n)] [NeZero n]
    (G H : DynamicGraph n)
    (h_sub : G.active_edges ⊆ H.active_edges)
    (h_G_conn : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1)
    (h_H_conn : Module.finrank ℝ (LinearMap.ker (d_G_linear H)) = 1) :
    Module.finrank ℝ (HarmonicSubspace G) ≤ Module.finrank ℝ (HarmonicSubspace H) := by
  have h_G := harmonic_dimension_eq_cyclomatic G
  have h_H := harmonic_dimension_eq_cyclomatic H
  have h_edge : G.active_edges.card ≤ H.active_edges.card := Finset.card_le_card h_sub
  rw [h_G_conn] at h_G
  rw [h_H_conn] at h_H
  omega

/-! ## Extremal Characterizations -/

/-- The cycle achieves minimum non-zero Betti number: b₁(C_n) = 1.

    Among all non-classical (non-tree) connected graphs, the cycle
    is the simplest - it has exactly one independent cycle.
-/
theorem cycle_is_minimal_non_classical [NeZero n] [DecidableEq (Fin n)] (hn : n ≥ 3) :
    Module.finrank ℝ (HarmonicSubspace (CycleGraph.cycleGraph n (by omega))) = 1 :=
  CycleGraph.cycle_graph_betti_1 n (by omega)

/-- The complete graph achieves maximum Betti number: b₁(K_n) = (n-1)(n-2)/2.

    Among all graphs on n vertices, K_n has the most independent cycles.
-/
theorem complete_is_maximal [DecidableEq (Fin n)] [NeZero n] :
    Module.finrank ℝ (HarmonicSubspace (DynamicGraph.complete n)) = (n - 1) * (n - 2) / 2 :=
  CompleteGraph.complete_graph_betti_1

/-! ## The Topology Spectrum -/

/-- The topology spectrum: all Betti numbers from 0 to (n-1)(n-2)/2 are achievable.

    For n ≥ 3:
    - b₁ = 0: Path graph (tree)
    - b₁ = 1: Cycle graph
    - b₁ = (n-1)(n-2)/2: Complete graph
    - All intermediate values are achievable by adding/removing edges
-/
theorem betti_range_achievable_endpoints [DecidableEq (Fin n)] [NeZero n] (hn : n ≥ 3) :
    (∃ G : DynamicGraph n,
      Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1 ∧
      Module.finrank ℝ (HarmonicSubspace G) = 0) ∧
    (∃ G : DynamicGraph n,
      Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1 ∧
      Module.finrank ℝ (HarmonicSubspace G) = 1) ∧
    (∃ G : DynamicGraph n,
      Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1 ∧
      Module.finrank ℝ (HarmonicSubspace G) = (n - 1) * (n - 2) / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · use PathGraph.pathGraph n (by omega)
    exact ⟨PathGraph.path_graph_kernel_dim n (by omega), PathGraph.path_graph_betti_0 n (by omega)⟩
  · use CycleGraph.cycleGraph n (by omega)
    exact ⟨CycleGraph.cycle_graph_kernel_dim n (by omega), CycleGraph.cycle_graph_betti_1 n (by omega)⟩
  · use DynamicGraph.complete n
    exact ⟨CompleteGraph.complete_graph_kernel_dim n, CompleteGraph.complete_graph_betti_1⟩

theorem maximum_frustration_principle [DecidableEq (Fin n)] [NeZero n] (G : DynamicGraph n)
    (_h_conn : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1)
    (h_complete : G = DynamicGraph.complete n) :
    ∀ H : DynamicGraph n,
      Module.finrank ℝ (LinearMap.ker (d_G_linear H)) = 1 →
      Module.finrank ℝ (HarmonicSubspace H) ≤ Module.finrank ℝ (HarmonicSubspace G) := by
  intro H h_H_conn
  rw [h_complete]
  exact betti_one_le_complete H h_H_conn

end Diaspora.Hodge.MaximumTopology
