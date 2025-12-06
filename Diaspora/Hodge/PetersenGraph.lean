/-
# The Petersen Graph: Democratic Paradox

The Petersen graph is arguably the most famous small graph in mathematics.
It appears as a counterexample to numerous plausible conjectures and serves
as a touchstone for graph-theoretic intuitions.

## Construction

The Petersen graph has 10 vertices arranged as:
- An outer pentagon (vertices 0-4)
- An inner pentagram (vertices 5-9)
- Each outer vertex connects to its corresponding inner vertex

    0
   / \
  4   1
  |\ /|
  | X |     (outer pentagon 0-1-2-3-4-0)
  |/ \|
  3   2

The inner vertices form a pentagram: 5-7-9-6-8-5 (skip by 2).

## The Main Result

  **b₁(Petersen) = 6**

This is simply |E| - |V| + 1 = 15 - 10 + 1 = 6.

## What Makes Petersen Special?

1. **Vertex-transitive**: Every vertex "looks the same" - any vertex can be
   mapped to any other by a graph automorphism. The 6 independent cycles are
   uniformly distributed across all 10 vertices.

2. **3-regular**: Every vertex has exactly 3 neighbors. No vertex is
   more or less connected than any other.

3. **No Hamilton cycle**: Despite being highly connected, you cannot visit
   all vertices exactly once and return to start.

## Philosophical Interpretation: Democratic Paradox

In Diaspora's language, the Petersen graph represents **collective responsibility**.
The 6-dimensional harmonic subspace cannot be "blamed" on any particular vertex
or edge - the frustration is distributed uniformly across the entire structure.

Compare this to:
- **Wheel graph**: The hub is clearly special (creates all cycles)
- **Friendship graph**: The central vertex is a junction for all triangles
- **Complete graph**: High-degree vertices dominate the topology

The Petersen graph is the archetypal example of a structure where paradox
has no localized source. Every vertex participates equally in the irreducible
frustration. This is a counterexample to the intuition that complexity must
have a center - sometimes, complexity is genuinely distributed.

In human terms: blame cannot always be assigned. Some paradoxes are truly
collective, arising from the structure of relationships rather than from
any individual participant.
-/

import Diaspora.Hodge.Decomposition
import Mathlib.LinearAlgebra.Dimension.Finrank

open BigOperators Diaspora.Core Diaspora.Hodge

namespace Diaspora.Hodge.PetersenGraph

/-- The Petersen graph on 10 vertices.

    Outer pentagon: 0-1-2-3-4-0
    Inner pentagram: 5-7-9-6-8-5 (connecting every second vertex)
    Spokes: i ↔ i+5 for i ∈ {0,1,2,3,4}
-/
def petersen : DynamicGraph 10 where
  active_edges := {
    -- Outer pentagon: 0-1-2-3-4-0
    (0, 1), (1, 0),
    (1, 2), (2, 1),
    (2, 3), (3, 2),
    (3, 4), (4, 3),
    (4, 0), (0, 4),
    -- Inner pentagram: 5-7-9-6-8-5 (skip by 2 in the inner ring)
    (5, 7), (7, 5),
    (7, 9), (9, 7),
    (9, 6), (6, 9),
    (6, 8), (8, 6),
    (8, 5), (5, 8),
    -- Spokes connecting outer to inner
    (0, 5), (5, 0),
    (1, 6), (6, 1),
    (2, 7), (7, 2),
    (3, 8), (8, 3),
    (4, 9), (9, 4)
  }
  symmetric := by decide
  no_loops := by decide

/-- The Petersen graph has 30 directed edges (15 undirected).
    - 5 outer pentagon edges
    - 5 inner pentagram edges
    - 5 spokes
    Total: 15 undirected = 30 directed
-/
lemma petersen_edge_count : petersen.active_edges.card = 30 := by native_decide

/-- Every vertex in the Petersen graph has exactly 3 neighbors (3-regular). -/
lemma petersen_is_3_regular (v : Fin 10) :
    (petersen.active_edges.filter (fun e => e.1 = v)).card = 3 := by
  fin_cases v <;> native_decide

/-- The Petersen graph is connected: kernel dimension = 1.

    The proof shows that any potential in the gradient kernel must be constant
    by tracing connectivity through the graph structure.
-/
lemma petersen_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear petersen)) = 1 := by
  let one : Fin 10 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear petersen) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G petersen one).val.val i j = 0
    unfold d_G one
    simp only [petersen]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear petersen) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      -- Trace connectivity through outer pentagon
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ petersen.active_edges := by decide
        have h_zero : (d_G petersen φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h12 : φ 2 = φ 1 := by
        have h_edge : (1, 2) ∈ petersen.active_edges := by decide
        have h_zero : (d_G petersen φ).val.val 1 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h23 : φ 3 = φ 2 := by
        have h_edge : (2, 3) ∈ petersen.active_edges := by decide
        have h_zero : (d_G petersen φ).val.val 2 3 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 2 3
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h34 : φ 4 = φ 3 := by
        have h_edge : (3, 4) ∈ petersen.active_edges := by decide
        have h_zero : (d_G petersen φ).val.val 3 4 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 3 4
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      -- Connect to inner vertices via spokes
      have h05 : φ 5 = φ 0 := by
        have h_edge : (0, 5) ∈ petersen.active_edges := by decide
        have h_zero : (d_G petersen φ).val.val 0 5 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 5
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h16 : φ 6 = φ 1 := by
        have h_edge : (1, 6) ∈ petersen.active_edges := by decide
        have h_zero : (d_G petersen φ).val.val 1 6 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 6
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h27 : φ 7 = φ 2 := by
        have h_edge : (2, 7) ∈ petersen.active_edges := by decide
        have h_zero : (d_G petersen φ).val.val 2 7 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 2 7
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h38 : φ 8 = φ 3 := by
        have h_edge : (3, 8) ∈ petersen.active_edges := by decide
        have h_zero : (d_G petersen φ).val.val 3 8 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 3 8
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h49 : φ 9 = φ 4 := by
        have h_edge : (4, 9) ∈ petersen.active_edges := by decide
        have h_zero : (d_G petersen φ).val.val 4 9 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 4 9
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h12, h23, h34, h05, h16, h27, h38, h49]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- **The Petersen Graph Betti Number**: b₁(Petersen) = 6

    The Petersen graph has 6 independent cycles.
    Since it's connected with 10 vertices and 15 edges:
      b₁ = |E| - |V| + 1 = 15 - 10 + 1 = 6

    These 6 cycles are distributed uniformly across the graph -
    no vertex or edge is more "responsible" for the topology than any other.
-/
theorem petersen_betti_six : Module.finrank ℝ (HarmonicSubspace petersen) = 6 := by
  have h_dim := harmonic_dimension_eq_cyclomatic petersen
  have h_ker := petersen_kernel_dim
  have h_edge := petersen_edge_count
  have h_edge_half : petersen.active_edges.card / 2 = 15 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

/-- The Petersen graph is non-classical: it has positive harmonic dimension. -/
theorem petersen_nonclassical : Module.finrank ℝ (HarmonicSubspace petersen) > 0 := by
  rw [petersen_betti_six]; omega

/-! ## Comparative Analysis -/

/-- Vertices in Petersen: 10 -/
lemma petersen_vertex_count : Fintype.card (Fin 10) = 10 := by rfl

/-- Edges in Petersen (undirected): 15 -/
lemma petersen_undirected_edge_count : petersen.active_edges.card / 2 = 15 := by
  rw [petersen_edge_count]

/-- Cycle efficiency: cycles per edge.
    Petersen: 6/15 = 0.4 cycles per edge
    For comparison:
    - Triangle: 1/3 ≈ 0.33
    - Complete K_5: 6/10 = 0.6
    - 10-cycle: 1/10 = 0.1
-/
theorem petersen_cycle_efficiency : (6 : ℚ) / 15 = 2 / 5 := by norm_num

/-- Vertex coverage: cycles per vertex.
    Petersen: 6/10 = 0.6 cycles per vertex -/
theorem petersen_vertex_coverage : (6 : ℚ) / 10 = 3 / 5 := by norm_num

/-! ## The Democratic Paradox Principle

The Petersen graph illustrates a key philosophical point: topological complexity
can be genuinely distributed rather than localized.

In many graphs, there's a "center of blame":
- Wheel: the hub creates all cycles
- Friendship: the central vertex hosts all triangles
- Star: the center controls all connectivity

The Petersen graph is different. Its automorphism group acts transitively on
vertices, meaning every vertex is structurally equivalent. The 6 cycles of
harmonic frustration cannot be attributed to any particular vertex - they are
a property of the collective arrangement.

This is the **Democratic Paradox**: a structure where blame cannot be assigned
to individuals, only to the pattern of relationships as a whole.
-/

/-- The Petersen graph's 3-regularity means every vertex participates
    equally in the graph structure. -/
theorem petersen_uniform_degree : ∀ v : Fin 10,
    (petersen.active_edges.filter (fun e => e.1 = v)).card = 3 :=
  petersen_is_3_regular

/-! ## The Petersen Graph as a Counterexample Machine

Historically, the Petersen graph has served as a counterexample to many
plausible graph-theoretic conjectures:

1. **Hamiltonicity**: The Petersen graph is 3-connected and 3-regular,
   yet has no Hamilton cycle.

2. **Edge-coloring**: It's the smallest 3-regular graph requiring
   4 colors for proper edge-coloring (chromatic index = 4).

3. **Various conjectures** about cycle covers, independent sets, etc.

In Diaspora's interpretation, Petersen's role as a counterexample suggests
that intuitions about "well-behaved" graphs fail precisely when topology
is democratically distributed. The absence of a privileged center makes
the graph resistant to many optimization strategies.

This connects to a broader theme: systems without hierarchy are often
harder to analyze, optimize, or control. The Petersen graph's uniform
structure makes it locally simple but globally complex.
-/

end Diaspora.Hodge.PetersenGraph
