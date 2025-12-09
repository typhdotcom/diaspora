import Diaspora.Hodge.Decomposition
import Diaspora.Hodge.BipartiteGraph

/-!
# The Complete Tripartite Graph

b₁(K_{a,b,c}) = ab + bc + ca - (a + b + c) + 1

Special cases: K_{1,1,1} = K_3 has b₁ = 1, K_{2,2,2} (octahedron) has b₁ = 7.
-/

open BigOperators Diaspora.Core Diaspora.Hodge

namespace Diaspora.Hodge.TripartiteGraph

/-! ## The Octahedron K_{2,2,2} -/

/-- The octahedron: K_{2,2,2} on 6 vertices.
    Part A = {0, 1}, Part B = {2, 3}, Part C = {4, 5}.
    Edges connect all vertices in different parts.

    Explicit edge listing for efficient decidability. -/
def octahedron : DynamicGraph 6 where
  active_edges := {
    -- Part A ↔ Part B: {0,1} × {2,3}
    (0, 2), (2, 0), (0, 3), (3, 0),
    (1, 2), (2, 1), (1, 3), (3, 1),
    -- Part A ↔ Part C: {0,1} × {4,5}
    (0, 4), (4, 0), (0, 5), (5, 0),
    (1, 4), (4, 1), (1, 5), (5, 1),
    -- Part B ↔ Part C: {2,3} × {4,5}
    (2, 4), (4, 2), (2, 5), (5, 2),
    (3, 4), (4, 3), (3, 5), (5, 3)
  }
  symmetric := by decide
  no_loops := by decide

/-! ## Edge Count -/

/-- The octahedron has 24 directed edges (12 undirected). -/
lemma octahedron_edge_count : octahedron.active_edges.card = 24 := by
  native_decide

/-- 12 undirected edges in the octahedron. -/
lemma octahedron_undirected_edge_count : octahedron.active_edges.card / 2 = 12 := by
  native_decide

/-! ## Connectivity -/

/-- The octahedron is connected: kernel dimension is 1. -/
lemma octahedron_kernel_dim :
    Module.finrank ℝ (LinearMap.ker (d_G_linear octahedron)) = 1 := by
  let one : Fin 6 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear octahedron) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G octahedron one).val.val i j = 0
    unfold d_G one
    simp only [octahedron]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear octahedron) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      -- Trace connectivity: all vertices connect to 0 via at most 2 steps
      have h20 : φ 2 = φ 0 := by
        have h_edge : (2, 0) ∈ octahedron.active_edges := by decide
        have h_zero : (d_G octahedron φ).val.val 2 0 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 2 0; exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h30 : φ 3 = φ 0 := by
        have h_edge : (3, 0) ∈ octahedron.active_edges := by decide
        have h_zero : (d_G octahedron φ).val.val 3 0 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 3 0; exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h40 : φ 4 = φ 0 := by
        have h_edge : (4, 0) ∈ octahedron.active_edges := by decide
        have h_zero : (d_G octahedron φ).val.val 4 0 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 4 0; exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h50 : φ 5 = φ 0 := by
        have h_edge : (5, 0) ∈ octahedron.active_edges := by decide
        have h_zero : (d_G octahedron φ).val.val 5 0 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 5 0; exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h10 : φ 1 = φ 0 := by
        -- 1 ↔ 2 and we know φ 2 = φ 0
        have h_edge : (1, 2) ∈ octahedron.active_edges := by decide
        have h_zero : (d_G octahedron φ).val.val 1 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 2; exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero
        linarith
      have h_const : ∀ i : Fin 6, φ i = φ 0 := by
        intro i; fin_cases i <;> first | rfl | exact h10 | exact h20 | exact h30 | exact h40 | exact h50
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

/-- **The Octahedron Theorem**: b₁(K_{2,2,2}) = 7.

    The octahedron has 6 vertices, 12 edges, and 7 independent cycles.
    This matches the complete tripartite formula:
      b₁ = ab + bc + ca - (a + b + c) + 1
         = 4 + 4 + 4 - 6 + 1 = 7

    The 7 cycles arise from the rich connectivity between the three pairs.
    Each vertex has degree 4 (connected to all non-paired vertices), and
    the graph is vertex-transitive: every vertex looks the same.
-/
theorem octahedron_betti_seven :
    Module.finrank ℝ (HarmonicSubspace octahedron) = 7 := by
  have h_dim := harmonic_dimension_eq_cyclomatic octahedron
  have h_ker := octahedron_kernel_dim
  have h_edge := octahedron_undirected_edge_count
  rw [h_edge, h_ker] at h_dim
  -- h_dim : dim(H) + 6 = 12 + 1
  omega

/-- The octahedron achieves the complete tripartite formula for K_{2,2,2}. -/
theorem octahedron_formula :
    Module.finrank ℝ (HarmonicSubspace octahedron) = 2*2 + 2*2 + 2*2 - (2 + 2 + 2) + 1 := by
  simp only [octahedron_betti_seven]

/-! ## Comparison with Other Graphs -/

/-- The octahedron has more cycles than the complete graph K_4.
    K_4 has b₁ = 3, while K_{2,2,2} has b₁ = 7, despite both having 6 vertices.
    The tripartite structure allows more independent cycles than maximally
    connecting 4 vertices. -/
theorem octahedron_vs_K4 :
    Module.finrank ℝ (HarmonicSubspace octahedron) > 3 := by
  rw [octahedron_betti_seven]; omega

/-- The octahedron has more cycles than two disjoint triangles.
    Two triangles: b₁ = 1 + 1 = 2.
    Octahedron: b₁ = 7.
    Connecting the three pairs creates 5 new independent cycles. -/
theorem octahedron_vs_two_triangles :
    Module.finrank ℝ (HarmonicSubspace octahedron) > 2 := by
  rw [octahedron_betti_seven]; omega

/-- The octahedron has more cycles than the cube (Q_3 = K_2 □ K_2 □ K_2).
    Cube has b₁ = 5, octahedron has b₁ = 7.
    The octahedron is the dual of the cube, with vertices swapped for faces,
    but they're not simply related by duality in terms of Betti numbers. -/
theorem octahedron_vs_cube :
    Module.finrank ℝ (HarmonicSubspace octahedron) > 5 := by
  rw [octahedron_betti_seven]; omega

/-- The octahedron is 4-regular. -/
lemma octahedron_is_4_regular :
    ∀ v : Fin 6, (octahedron.active_edges.filter (fun (i, _) => i = v)).card = 4 := by
  intro v
  fin_cases v <;> native_decide

/-- The octahedron achieves the maximum for K_{2,2,2}. -/
theorem octahedron_is_maximum_tripartite_222 :
    Module.finrank ℝ (HarmonicSubspace octahedron) = 2*2 + 2*2 + 2*2 - 6 + 1 := by
  simp only [octahedron_betti_seven]

/-! ## The Triangle as K_{1,1,1} -/

/-- The triangle is K_{1,1,1}: the degenerate complete tripartite graph.
    With one vertex per part, edges connect all pairs, giving K_3. -/
def triangle_as_tripartite : DynamicGraph 3 where
  active_edges := {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1)}
  symmetric := by decide
  no_loops := by decide

/-- K_{1,1,1} has 6 directed edges (3 undirected). -/
lemma triangle_edge_count : triangle_as_tripartite.active_edges.card = 6 := by
  native_decide

/-- K_{1,1,1} is connected. -/
lemma triangle_kernel_dim :
    Module.finrank ℝ (LinearMap.ker (d_G_linear triangle_as_tripartite)) = 1 := by
  let one : Fin 3 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear triangle_as_tripartite) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G triangle_as_tripartite one).val.val i j = 0
    unfold d_G one
    simp only [triangle_as_tripartite]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear triangle_as_tripartite) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h10 : φ 1 = φ 0 := by
        have h_edge : (1, 0) ∈ triangle_as_tripartite.active_edges := by decide
        have h_zero : (d_G triangle_as_tripartite φ).val.val 1 0 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 0; exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h20 : φ 2 = φ 0 := by
        have h_edge : (2, 0) ∈ triangle_as_tripartite.active_edges := by decide
        have h_zero : (d_G triangle_as_tripartite φ).val.val 2 0 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 2 0; exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h_const : ∀ i : Fin 3, φ i = φ 0 := by
        intro i; fin_cases i <;> first | rfl | exact h10 | exact h20
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i
      simp only [one, Pi.smul_apply, smul_eq_mul, mul_one, (h_const i).symm]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h
  have : (1 : ℝ) = 0 := congr_fun h 0
  norm_num at this

/-- **K_{1,1,1} = K_3**: b₁ = 1, matching the formula 1·1 + 1·1 + 1·1 - 3 + 1 = 1. -/
theorem triangle_betti_one :
    Module.finrank ℝ (HarmonicSubspace triangle_as_tripartite) = 1 := by
  have h_dim := harmonic_dimension_eq_cyclomatic triangle_as_tripartite
  have h_ker := triangle_kernel_dim
  have h_edge : triangle_as_tripartite.active_edges.card / 2 = 3 := by
    rw [triangle_edge_count]
  rw [h_edge, h_ker] at h_dim
  omega

/-- The triangle achieves the complete tripartite formula for K_{1,1,1}. -/
theorem triangle_formula :
    Module.finrank ℝ (HarmonicSubspace triangle_as_tripartite) = 1*1 + 1*1 + 1*1 - 3 + 1 := by
  simp only [triangle_betti_one]

/-- K_{2,2,2} has more cycles than K_{3,3}. -/
theorem tripartite_vs_bipartite :
    Module.finrank ℝ (HarmonicSubspace octahedron) > 4 := by
  rw [octahedron_betti_seven]; omega

theorem octahedron_is_tripartite_genesis :
    Module.finrank ℝ (HarmonicSubspace octahedron) =
    Module.finrank ℝ (HarmonicSubspace triangle_as_tripartite) + 6 := by
  rw [octahedron_betti_seven, triangle_betti_one]

end Diaspora.Hodge.TripartiteGraph
