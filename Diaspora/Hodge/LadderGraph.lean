/-
# Ladder Graph Betti Numbers

The ladder graph L_n (rectangular ladder) consists of two parallel paths
of n vertices, connected by n "rungs":

    Top:    0 — 1 — 2 — ... — (n-1)
            |   |   |           |
    Bottom: n — n+1— n+2— ... — (2n-1)

The Betti number is:
  b₁(L_n) = n - 1

This is the "open" version of the prism graph. While the prism closes
both paths into cycles, the ladder leaves them open.

**The Closure Theorem:** The difference between prism and ladder Betti
numbers is exactly 2:
  b₁(Prism_n) - b₁(Ladder_n) = (n + 1) - (n - 1) = 2

This generalizes the "genesis gap" (path→cycle adds 1) to higher dimensions:
closing TWO paths into TWO cycles adds 2 to the Betti number.

Physical interpretation: The ladder is a "partially classical" structure.
It has topology (n-1 independent cycles formed by the rungs and path segments),
but less than its closed counterpart. Each closure (connecting the ends of
a path to form a cycle) adds one unit of irreducible frustration.

Philosophical reading: The prism's topology is "propped up" by its closure
at both ends. Opening it (cutting the closing edges) releases 2 units of
harmonic content. This is the topological analog of severing a loop of
self-reference.
-/

import Diaspora.Hodge.IndexTheorem
import Diaspora.Hodge.PrismGraph
import Diaspora.Hodge.PathGraph
import Mathlib.LinearAlgebra.Dimension.Finrank

open BigOperators Diaspora.Core Diaspora.Hodge

namespace Diaspora.Hodge.LadderGraph

/-! ## Concrete Ladder Graphs for small n -/

/-- The 3-ladder (L_3) on 6 vertices.
    Top path: 0-1-2, Bottom path: 3-4-5, Rungs: 0-3, 1-4, 2-5 -/
def ladder3 : DynamicGraph 6 where
  active_edges := {
    -- Top path (NOT a cycle - no edge from 2 to 0)
    (0, 1), (1, 0), (1, 2), (2, 1),
    -- Bottom path (NOT a cycle - no edge from 5 to 3)
    (3, 4), (4, 3), (4, 5), (5, 4),
    -- Rungs
    (0, 3), (3, 0), (1, 4), (4, 1), (2, 5), (5, 2)
  }
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> decide
  no_loops := by intro i; fin_cases i <;> decide

/-- L_3 has 14 directed edges (7 undirected: 2 top + 2 bottom + 3 rungs). -/
lemma ladder3_edge_count : ladder3.active_edges.card = 14 := by native_decide

/-- L_3 is connected: kernel dimension = 1. -/
lemma ladder3_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear ladder3)) = 1 := by
  let one : Fin 6 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear ladder3) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G ladder3 one).val.val i j = 0
    unfold d_G one
    simp only [ladder3, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear ladder3) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ ladder3.active_edges := by simp [ladder3]
        have h_zero : (d_G ladder3 φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h12 : φ 2 = φ 1 := by
        have h_edge : (1, 2) ∈ ladder3.active_edges := by simp [ladder3]
        have h_zero : (d_G ladder3 φ).val.val 1 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h03 : φ 3 = φ 0 := by
        have h_edge : (0, 3) ∈ ladder3.active_edges := by simp [ladder3]
        have h_zero : (d_G ladder3 φ).val.val 0 3 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 3
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h34 : φ 4 = φ 3 := by
        have h_edge : (3, 4) ∈ ladder3.active_edges := by simp [ladder3]
        have h_zero : (d_G ladder3 φ).val.val 3 4 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 3 4
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h45 : φ 5 = φ 4 := by
        have h_edge : (4, 5) ∈ ladder3.active_edges := by simp [ladder3]
        have h_zero : (d_G ladder3 φ).val.val 4 5 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 4 5
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h12, h03, h34, h45]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- **Ladder_3 Betti Number**: b₁(L_3) = 2

    The 3-ladder has 2 independent cycles:
    - The "square" 0-1-4-3-0
    - The "square" 1-2-5-4-1

    Compare to Prism_3 which has 4 cycles. The difference is 2:
    one for each closing edge (2-0 on top, 5-3 on bottom).
-/
theorem ladder3_betti_two : Module.finrank ℝ (HarmonicSubspace ladder3) = 2 := by
  have h_dim := harmonic_dimension_eq_cyclomatic ladder3
  have h_ker := ladder3_kernel_dim
  have h_edge := ladder3_edge_count
  have h_edge_half : ladder3.active_edges.card / 2 = 7 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

/-! ## The 4-Ladder -/

/-- The 4-ladder (L_4) on 8 vertices.
    Top path: 0-1-2-3, Bottom path: 4-5-6-7, Rungs: 0-4, 1-5, 2-6, 3-7 -/
def ladder4 : DynamicGraph 8 where
  active_edges := {
    -- Top path (NOT a cycle - no edge from 3 to 0)
    (0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2),
    -- Bottom path (NOT a cycle - no edge from 7 to 4)
    (4, 5), (5, 4), (5, 6), (6, 5), (6, 7), (7, 6),
    -- Rungs
    (0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2), (3, 7), (7, 3)
  }
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> decide
  no_loops := by intro i; fin_cases i <;> decide

/-- L_4 has 20 directed edges (10 undirected: 3 top + 3 bottom + 4 rungs). -/
lemma ladder4_edge_count : ladder4.active_edges.card = 20 := by native_decide

/-- L_4 is connected: kernel dimension = 1. -/
lemma ladder4_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear ladder4)) = 1 := by
  let one : Fin 8 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear ladder4) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G ladder4 one).val.val i j = 0
    unfold d_G one
    simp only [ladder4, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear ladder4) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ ladder4.active_edges := by simp [ladder4]
        have h_zero : (d_G ladder4 φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h12 : φ 2 = φ 1 := by
        have h_edge : (1, 2) ∈ ladder4.active_edges := by simp [ladder4]
        have h_zero : (d_G ladder4 φ).val.val 1 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h23 : φ 3 = φ 2 := by
        have h_edge : (2, 3) ∈ ladder4.active_edges := by simp [ladder4]
        have h_zero : (d_G ladder4 φ).val.val 2 3 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 2 3
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h04 : φ 4 = φ 0 := by
        have h_edge : (0, 4) ∈ ladder4.active_edges := by simp [ladder4]
        have h_zero : (d_G ladder4 φ).val.val 0 4 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 4
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h45 : φ 5 = φ 4 := by
        have h_edge : (4, 5) ∈ ladder4.active_edges := by simp [ladder4]
        have h_zero : (d_G ladder4 φ).val.val 4 5 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 4 5
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h56 : φ 6 = φ 5 := by
        have h_edge : (5, 6) ∈ ladder4.active_edges := by simp [ladder4]
        have h_zero : (d_G ladder4 φ).val.val 5 6 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 5 6
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h67 : φ 7 = φ 6 := by
        have h_edge : (6, 7) ∈ ladder4.active_edges := by simp [ladder4]
        have h_zero : (d_G ladder4 φ).val.val 6 7 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 6 7
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h12, h23, h04, h45, h56, h67]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- **Ladder_4 Betti Number**: b₁(L_4) = 3

    The 4-ladder has 3 independent cycles (one for each "square" between rungs).
    Compare to Prism_4 (cube) which has 5 cycles. Difference is 2.
-/
theorem ladder4_betti_three : Module.finrank ℝ (HarmonicSubspace ladder4) = 3 := by
  have h_dim := harmonic_dimension_eq_cyclomatic ladder4
  have h_ker := ladder4_kernel_dim
  have h_edge := ladder4_edge_count
  have h_edge_half : ladder4.active_edges.card / 2 = 10 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

/-! ## The Closure Theorem

The fundamental relationship between ladders and prisms:
  b₁(Prism_n) - b₁(Ladder_n) = 2

This generalizes the "genesis gap" from PathGraph.lean:
- Path P_n has b₁ = 0
- Cycle C_n has b₁ = 1
- Difference: 1 (closing one path adds one cycle)

For ladders and prisms:
- Ladder L_n has b₁ = n - 1
- Prism_n has b₁ = n + 1
- Difference: 2 (closing two paths adds two cycles)

Each "closure" (connecting the endpoints of a path to form a cycle)
contributes exactly one unit of harmonic content.
-/

/-- **The Closure Theorem for n=3**: Closing the ladder into a prism adds 2 cycles.

    Prism_3 = Ladder_3 + 2 closing edges (2-0 on top, 5-3 on bottom)
    b₁(Prism_3) - b₁(Ladder_3) = 4 - 2 = 2
-/
theorem closure_theorem_3 :
    Module.finrank ℝ (HarmonicSubspace PrismGraph.prism3) -
    Module.finrank ℝ (HarmonicSubspace ladder3) = 2 := by
  rw [PrismGraph.prism3_betti_four, ladder3_betti_two]

/-- **The Closure Theorem for n=4**: Closing the ladder into a prism adds 2 cycles.

    Prism_4 = Ladder_4 + 2 closing edges (3-0 on top, 7-4 on bottom)
    b₁(Prism_4) - b₁(Ladder_4) = 5 - 3 = 2
-/
theorem closure_theorem_4 :
    Module.finrank ℝ (HarmonicSubspace PrismGraph.prism4) -
    Module.finrank ℝ (HarmonicSubspace ladder4) = 2 := by
  rw [PrismGraph.prism4_betti_five, ladder4_betti_three]

/-! ## The Pattern: b₁(L_n) = n - 1

The ladder graph has the pattern:
- L_3: b₁ = 2 = 3 - 1
- L_4: b₁ = 3 = 4 - 1

General formula: b₁(L_n) = n - 1

Proof (sketch):
- Vertices: 2n
- Edges: (n-1) top path + (n-1) bottom path + n rungs = 3n - 2
- For connected graphs: b₁ = |E| - |V| + 1 = (3n-2) - 2n + 1 = n - 1

This matches the fan graph F_n (cone of path), which also has b₁ = n - 1.
The ladder and fan have the same Betti number but different structures:
- Fan: apex connected to all vertices of a path
- Ladder: two paths connected by rungs

Both represent different ways to create n-1 independent cycles using 2n vertices.
-/

/-- L_3 follows the pattern b₁ = n - 1. -/
theorem ladder3_pattern : Module.finrank ℝ (HarmonicSubspace ladder3) = 3 - 1 := by
  rw [ladder3_betti_two]

/-- L_4 follows the pattern b₁ = n - 1. -/
theorem ladder4_pattern : Module.finrank ℝ (HarmonicSubspace ladder4) = 4 - 1 := by
  rw [ladder4_betti_three]

/-! ## Edge Difference: The Cost of Closure

The edge count difference between prism and ladder is exactly 2:
- Prism_n has 3n edges (n top + n bottom + n rungs)
- Ladder_n has 3n - 2 edges ((n-1) top + (n-1) bottom + n rungs)
- Difference: 2 edges

These 2 edges are exactly the "closing" edges that connect the endpoints
of each path to form a cycle. Each closing edge contributes 1 to the Betti number.

This is a higher-dimensional analog of the genesis gap:
- Path→Cycle: 1 edge → 1 cycle
- Ladder→Prism: 2 edges → 2 cycles
-/

/-- The edge count difference between Prism_3 and Ladder_3 is 2.
    These are the "genesis edges" that close the paths into cycles. -/
theorem closure_edge_cost_3 :
    PrismGraph.prism3.active_edges.card / 2 - ladder3.active_edges.card / 2 = 2 := by
  rw [PrismGraph.prism3_edge_count, ladder3_edge_count]

/-- The edge count difference between Prism_4 and Ladder_4 is 2. -/
theorem closure_edge_cost_4 :
    PrismGraph.prism4.active_edges.card / 2 - ladder4.active_edges.card / 2 = 2 := by
  rw [PrismGraph.prism4_edge_count, ladder4_edge_count]

/-- **The Exchange Rate**: Each closing edge buys exactly one cycle.
    For the ladder→prism transition: 2 edges → 2 cycles. -/
theorem closure_exchange_rate_3 :
    PrismGraph.prism3.active_edges.card / 2 - ladder3.active_edges.card / 2 =
    Module.finrank ℝ (HarmonicSubspace PrismGraph.prism3) -
    Module.finrank ℝ (HarmonicSubspace ladder3) := by
  rw [PrismGraph.prism3_edge_count, ladder3_edge_count,
      PrismGraph.prism3_betti_four, ladder3_betti_two]

theorem closure_exchange_rate_4 :
    PrismGraph.prism4.active_edges.card / 2 - ladder4.active_edges.card / 2 =
    Module.finrank ℝ (HarmonicSubspace PrismGraph.prism4) -
    Module.finrank ℝ (HarmonicSubspace ladder4) := by
  rw [PrismGraph.prism4_edge_count, ladder4_edge_count,
      PrismGraph.prism4_betti_five, ladder4_betti_three]

/-! ## Philosophical Interpretation

The ladder-prism relationship reveals a fundamental truth about closure:

1. **The Cost of Self-Reference**: Closing a loop (making the end meet the
   beginning) costs exactly 1 edge but creates exactly 1 unit of irreducible
   frustration. The ladder→prism transition does this twice.

2. **Partial Classicality**: The ladder has n-1 cycles - it's not classical
   (like the path with 0 cycles), but it's "less topological" than the prism
   (which has n+1). Opening a structure reduces its harmonic content.

3. **Genesis is Additive**: If closing one path creates 1 cycle, closing two
   paths creates 2 cycles. The topology creation is local and independent -
   each closure acts on its own.

4. **The Ladder as a Bridge State**: Between the fully classical (two disjoint
   paths) and the fully non-classical (prism), the ladder represents a middle
   ground. The rungs create topology, but the open ends prevent the full
   "prism frustration" from manifesting.
-/

end Diaspora.Hodge.LadderGraph
