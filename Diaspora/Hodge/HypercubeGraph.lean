/-
# Hypercube Graph Betti Numbers

The n-dimensional hypercube Q_n has 2^n vertices (binary strings of length n)
and two vertices are adjacent iff they differ in exactly one bit.

    Q_1:  0 — 1                     (path P_2, b₁ = 0)

    Q_2:  00 — 01                   (square C_4, b₁ = 1)
           |    |
          10 — 11

    Q_3:  000 — 001                 (cube, b₁ = 5)
           |  ×  |
          010 — 011
           |     |
          100 — 101
           |  ×  |
          110 — 111

The recursive structure: Q_n = two copies of Q_{n-1} connected by 2^{n-1} edges.

## The Main Result

  **b₁(Q_n) = n·2^{n-1} - 2^n + 1 = 2^{n-1}(n - 2) + 1**

Concrete values:
- Q_1: 2^0(-1) + 1 = 0  (path, classical vacuum)
- Q_2: 2^1(0) + 1 = 1   (square, single cycle)
- Q_3: 2^2(1) + 1 = 5   (cube, same as Prism_4)
- Q_4: 2^3(2) + 1 = 17  (tesseract)

## The Dimensional Doubling Theorem

Going from Q_{n-1} to Q_n:
- Vertices double: 2^{n-1} → 2^n
- Edges: (n-1)·2^{n-2} becomes n·2^{n-1}
- The increase in b₁:

  b₁(Q_n) - 2·b₁(Q_{n-1}) = number of NEW independent cycles

This captures how connecting "parallel universes" creates new topology
beyond what each universe had separately.

## Physical Interpretation

The hypercube is the discrete analog of a higher-dimensional torus.
Each dimension contributes new wrapping cycles. The formula
b₁ = 2^{n-1}(n-2) + 1 shows that topology grows exponentially
with dimension - the "information capacity" of the universe
explodes as you add dimensions.
-/

import Diaspora.Hodge.PrismGraph
import Mathlib.LinearAlgebra.Dimension.Finrank

open BigOperators Diaspora.Core Diaspora.Hodge

namespace Diaspora.Hodge.HypercubeGraph

/-! ## Q_2: The Square (4-cycle)

Q_2 is isomorphic to C_4. Vertices: 00=0, 01=1, 10=2, 11=3
Edges: 0-1 (differ in bit 0), 0-2 (differ in bit 1), 1-3, 2-3 -/

def hypercube2 : DynamicGraph 4 where
  active_edges := {
    (0, 1), (1, 0),  -- 00-01
    (0, 2), (2, 0),  -- 00-10
    (1, 3), (3, 1),  -- 01-11
    (2, 3), (3, 2)   -- 10-11
  }
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> decide
  no_loops := by intro i; fin_cases i <;> decide

/-- Q_2 has 8 directed edges (4 undirected). -/
lemma hypercube2_edge_count : hypercube2.active_edges.card = 8 := by native_decide

/-- Q_2 is connected: kernel dimension = 1. -/
lemma hypercube2_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear hypercube2)) = 1 := by
  let one : Fin 4 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear hypercube2) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G hypercube2 one).val.val i j = 0
    unfold d_G one
    simp only [hypercube2, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear hypercube2) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ hypercube2.active_edges := by simp [hypercube2]
        have h_zero : (d_G hypercube2 φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h02 : φ 2 = φ 0 := by
        have h_edge : (0, 2) ∈ hypercube2.active_edges := by simp [hypercube2]
        have h_zero : (d_G hypercube2 φ).val.val 0 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h13 : φ 3 = φ 1 := by
        have h_edge : (1, 3) ∈ hypercube2.active_edges := by simp [hypercube2]
        have h_zero : (d_G hypercube2 φ).val.val 1 3 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 3
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h02, h13]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- **Q_2 Betti Number**: b₁(Q_2) = 1

    The square has exactly one independent cycle.
    Formula: 2^1(2-2) + 1 = 1 ✓ -/
theorem hypercube2_betti_one : Module.finrank ℝ (HarmonicSubspace hypercube2) = 1 := by
  have h_dim := harmonic_dimension_eq_cyclomatic hypercube2
  have h_ker := hypercube2_kernel_dim
  have h_edge := hypercube2_edge_count
  have h_edge_half : hypercube2.active_edges.card / 2 = 4 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

/-! ## Q_3: The Cube (3-dimensional hypercube)

Vertices: binary strings 000 to 111, mapped to 0..7
Edges: pairs differing in exactly one bit -/

def hypercube3 : DynamicGraph 8 where
  active_edges := {
    -- Edges from vertices 0xx (differ in bit 0: rightmost)
    (0, 1), (1, 0),  -- 000-001
    (2, 3), (3, 2),  -- 010-011
    (4, 5), (5, 4),  -- 100-101
    (6, 7), (7, 6),  -- 110-111
    -- Edges from vertices x0x (differ in bit 1: middle)
    (0, 2), (2, 0),  -- 000-010
    (1, 3), (3, 1),  -- 001-011
    (4, 6), (6, 4),  -- 100-110
    (5, 7), (7, 5),  -- 101-111
    -- Edges from vertices xx0 (differ in bit 2: leftmost)
    (0, 4), (4, 0),  -- 000-100
    (1, 5), (5, 1),  -- 001-101
    (2, 6), (6, 2),  -- 010-110
    (3, 7), (7, 3)   -- 011-111
  }
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> decide
  no_loops := by intro i; fin_cases i <;> decide

/-- Q_3 has 24 directed edges (12 undirected). -/
lemma hypercube3_edge_count : hypercube3.active_edges.card = 24 := by native_decide

/-- Q_3 is connected: kernel dimension = 1. -/
lemma hypercube3_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear hypercube3)) = 1 := by
  let one : Fin 8 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear hypercube3) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G hypercube3 one).val.val i j = 0
    unfold d_G one
    simp only [hypercube3, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear hypercube3) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ hypercube3.active_edges := by simp [hypercube3]
        have h_zero : (d_G hypercube3 φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h02 : φ 2 = φ 0 := by
        have h_edge : (0, 2) ∈ hypercube3.active_edges := by simp [hypercube3]
        have h_zero : (d_G hypercube3 φ).val.val 0 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h04 : φ 4 = φ 0 := by
        have h_edge : (0, 4) ∈ hypercube3.active_edges := by simp [hypercube3]
        have h_zero : (d_G hypercube3 φ).val.val 0 4 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 4
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h13 : φ 3 = φ 1 := by
        have h_edge : (1, 3) ∈ hypercube3.active_edges := by simp [hypercube3]
        have h_zero : (d_G hypercube3 φ).val.val 1 3 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 3
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h15 : φ 5 = φ 1 := by
        have h_edge : (1, 5) ∈ hypercube3.active_edges := by simp [hypercube3]
        have h_zero : (d_G hypercube3 φ).val.val 1 5 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 5
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h26 : φ 6 = φ 2 := by
        have h_edge : (2, 6) ∈ hypercube3.active_edges := by simp [hypercube3]
        have h_zero : (d_G hypercube3 φ).val.val 2 6 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 2 6
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h37 : φ 7 = φ 3 := by
        have h_edge : (3, 7) ∈ hypercube3.active_edges := by simp [hypercube3]
        have h_zero : (d_G hypercube3 φ).val.val 3 7 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 3 7
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h02, h04, h13, h15, h26, h37]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- **Q_3 Betti Number**: b₁(Q_3) = 5

    The cube has 5 independent cycles (6 faces - 1 for dependency).
    Formula: 2^2(3-2) + 1 = 4 + 1 = 5 ✓ -/
theorem hypercube3_betti_five : Module.finrank ℝ (HarmonicSubspace hypercube3) = 5 := by
  have h_dim := harmonic_dimension_eq_cyclomatic hypercube3
  have h_ker := hypercube3_kernel_dim
  have h_edge := hypercube3_edge_count
  have h_edge_half : hypercube3.active_edges.card / 2 = 12 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

/-- Q_3 has the same Betti number as Prism_4 (they are isomorphic graphs). -/
theorem hypercube3_eq_prism4_betti :
    Module.finrank ℝ (HarmonicSubspace hypercube3) =
    Module.finrank ℝ (HarmonicSubspace PrismGraph.prism4) := by
  rw [hypercube3_betti_five, PrismGraph.prism4_betti_five]

/-! ## Q_4: The Tesseract (4-dimensional hypercube)

16 vertices (0..15 representing 0000..1111)
32 edges (each vertex has degree 4) -/

set_option maxRecDepth 1024 in
def hypercube4 : DynamicGraph 16 where
  active_edges := {
    -- Bit 0 edges (rightmost)
    (0, 1), (1, 0), (2, 3), (3, 2), (4, 5), (5, 4), (6, 7), (7, 6),
    (8, 9), (9, 8), (10, 11), (11, 10), (12, 13), (13, 12), (14, 15), (15, 14),
    -- Bit 1 edges
    (0, 2), (2, 0), (1, 3), (3, 1), (4, 6), (6, 4), (5, 7), (7, 5),
    (8, 10), (10, 8), (9, 11), (11, 9), (12, 14), (14, 12), (13, 15), (15, 13),
    -- Bit 2 edges
    (0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2), (3, 7), (7, 3),
    (8, 12), (12, 8), (9, 13), (13, 9), (10, 14), (14, 10), (11, 15), (15, 11),
    -- Bit 3 edges (leftmost)
    (0, 8), (8, 0), (1, 9), (9, 1), (2, 10), (10, 2), (3, 11), (11, 3),
    (4, 12), (12, 4), (5, 13), (13, 5), (6, 14), (14, 6), (7, 15), (15, 7)
  }
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> native_decide
  no_loops := by intro i; fin_cases i <;> native_decide

/-- Q_4 has 64 directed edges (32 undirected). -/
lemma hypercube4_edge_count : hypercube4.active_edges.card = 64 := by native_decide

/-- Q_4 is connected: kernel dimension = 1. -/
lemma hypercube4_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear hypercube4)) = 1 := by
  let one : Fin 16 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear hypercube4) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G hypercube4 one).val.val i j = 0
    unfold d_G one
    simp only [hypercube4]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear hypercube4) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      -- Prove all values equal φ 0 by following edges
      have h01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ hypercube4.active_edges := by native_decide
        have h_zero : (d_G hypercube4 φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h02 : φ 2 = φ 0 := by
        have h_edge : (0, 2) ∈ hypercube4.active_edges := by native_decide
        have h_zero : (d_G hypercube4 φ).val.val 0 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 2
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h04 : φ 4 = φ 0 := by
        have h_edge : (0, 4) ∈ hypercube4.active_edges := by native_decide
        have h_zero : (d_G hypercube4 φ).val.val 0 4 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 4
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h08 : φ 8 = φ 0 := by
        have h_edge : (0, 8) ∈ hypercube4.active_edges := by native_decide
        have h_zero : (d_G hypercube4 φ).val.val 0 8 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 8
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h13 : φ 3 = φ 1 := by
        have h_edge : (1, 3) ∈ hypercube4.active_edges := by native_decide
        have h_zero : (d_G hypercube4 φ).val.val 1 3 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 3
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h15 : φ 5 = φ 1 := by
        have h_edge : (1, 5) ∈ hypercube4.active_edges := by native_decide
        have h_zero : (d_G hypercube4 φ).val.val 1 5 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 5
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h19 : φ 9 = φ 1 := by
        have h_edge : (1, 9) ∈ hypercube4.active_edges := by native_decide
        have h_zero : (d_G hypercube4 φ).val.val 1 9 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 9
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h26 : φ 6 = φ 2 := by
        have h_edge : (2, 6) ∈ hypercube4.active_edges := by native_decide
        have h_zero : (d_G hypercube4 φ).val.val 2 6 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 2 6
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h2_10 : φ 10 = φ 2 := by
        have h_edge : (2, 10) ∈ hypercube4.active_edges := by native_decide
        have h_zero : (d_G hypercube4 φ).val.val 2 10 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 2 10
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h37 : φ 7 = φ 3 := by
        have h_edge : (3, 7) ∈ hypercube4.active_edges := by native_decide
        have h_zero : (d_G hypercube4 φ).val.val 3 7 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 3 7
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h3_11 : φ 11 = φ 3 := by
        have h_edge : (3, 11) ∈ hypercube4.active_edges := by native_decide
        have h_zero : (d_G hypercube4 φ).val.val 3 11 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 3 11
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h4_12 : φ 12 = φ 4 := by
        have h_edge : (4, 12) ∈ hypercube4.active_edges := by native_decide
        have h_zero : (d_G hypercube4 φ).val.val 4 12 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 4 12
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h5_13 : φ 13 = φ 5 := by
        have h_edge : (5, 13) ∈ hypercube4.active_edges := by native_decide
        have h_zero : (d_G hypercube4 φ).val.val 5 13 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 5 13
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h6_14 : φ 14 = φ 6 := by
        have h_edge : (6, 14) ∈ hypercube4.active_edges := by native_decide
        have h_zero : (d_G hypercube4 φ).val.val 6 14 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 6 14
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h7_15 : φ 15 = φ 7 := by
        have h_edge : (7, 15) ∈ hypercube4.active_edges := by native_decide
        have h_zero : (d_G hypercube4 φ).val.val 7 15 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 7 15
          exact this
        unfold d_G at h_zero; simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h01, h02, h04, h08, h13, h15, h19, h26, h2_10, h37, h3_11, h4_12, h5_13, h6_14, h7_15]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- **Q_4 Betti Number**: b₁(Q_4) = 17

    The tesseract has 17 independent cycles.
    Formula: 2^3(4-2) + 1 = 8·2 + 1 = 17 ✓ -/
theorem hypercube4_betti_seventeen : Module.finrank ℝ (HarmonicSubspace hypercube4) = 17 := by
  have h_dim := harmonic_dimension_eq_cyclomatic hypercube4
  have h_ker := hypercube4_kernel_dim
  have h_edge := hypercube4_edge_count
  have h_edge_half : hypercube4.active_edges.card / 2 = 32 := by rw [h_edge]
  rw [h_edge_half, h_ker] at h_dim
  omega

/-! ## The Hypercube Formula

b₁(Q_n) = n·2^{n-1} - 2^n + 1 = 2^{n-1}(n - 2) + 1

Verification:
- n=2: 2^1(0) + 1 = 1 ✓
- n=3: 2^2(1) + 1 = 5 ✓
- n=4: 2^3(2) + 1 = 17 ✓ -/

/-- Q_2 follows the formula. -/
theorem hypercube2_formula : Module.finrank ℝ (HarmonicSubspace hypercube2) = 2^1 * (2 - 2) + 1 := by
  rw [hypercube2_betti_one]; ring

/-- Q_3 follows the formula. -/
theorem hypercube3_formula : Module.finrank ℝ (HarmonicSubspace hypercube3) = 2^2 * (3 - 2) + 1 := by
  rw [hypercube3_betti_five]; ring

/-- Q_4 follows the formula. -/
theorem hypercube4_formula : Module.finrank ℝ (HarmonicSubspace hypercube4) = 2^3 * (4 - 2) + 1 := by
  rw [hypercube4_betti_seventeen]; ring

/-! ## The Dimensional Doubling Theorem

When we go from Q_{n-1} to Q_n, we double the structure and connect
corresponding vertices. This creates more cycles than 2× the original.

b₁(Q_n) - 2·b₁(Q_{n-1}) measures the "new" topology from connection. -/

/-- Doubling from Q_2 to Q_3 creates 3 extra cycles.

    2·b₁(Q_2) = 2·1 = 2
    b₁(Q_3) = 5
    New cycles = 5 - 2 = 3

    These 3 cycles thread between the two Q_2 "faces" of Q_3. -/
theorem doubling_2_to_3 :
    Module.finrank ℝ (HarmonicSubspace hypercube3) -
    2 * Module.finrank ℝ (HarmonicSubspace hypercube2) = 3 := by
  rw [hypercube3_betti_five, hypercube2_betti_one]

/-- Doubling from Q_3 to Q_4 creates 7 extra cycles.

    2·b₁(Q_3) = 2·5 = 10
    b₁(Q_4) = 17
    New cycles = 17 - 10 = 7

    Pattern: doubling creates 2^{n-1} - 1 new cycles. -/
theorem doubling_3_to_4 :
    Module.finrank ℝ (HarmonicSubspace hypercube4) -
    2 * Module.finrank ℝ (HarmonicSubspace hypercube3) = 7 := by
  rw [hypercube4_betti_seventeen, hypercube3_betti_five]

/-- The doubling increment follows the pattern 2^{n-1} - 1.

    Q_2→Q_3: 2^2 - 1 = 3 ✓
    Q_3→Q_4: 2^3 - 1 = 7 ✓

    This is the number of new 4-cycles created by connecting
    the two copies: each of the 2^{n-1} connecting edges creates
    a new cycle, minus 1 for dependency. -/
theorem doubling_increment_pattern_3 :
    Module.finrank ℝ (HarmonicSubspace hypercube3) -
    2 * Module.finrank ℝ (HarmonicSubspace hypercube2) = 2^2 - 1 := by
  rw [hypercube3_betti_five, hypercube2_betti_one]; native_decide

theorem doubling_increment_pattern_4 :
    Module.finrank ℝ (HarmonicSubspace hypercube4) -
    2 * Module.finrank ℝ (HarmonicSubspace hypercube3) = 2^3 - 1 := by
  rw [hypercube4_betti_seventeen, hypercube3_betti_five]; native_decide

/-! ## Philosophical Interpretation

The hypercube represents the discrete analog of higher-dimensional space.

**Exponential Topology**

The formula b₁(Q_n) = 2^{n-1}(n-2) + 1 shows that topology grows
exponentially with dimension. Each new dimension doesn't just add
cycles linearly - it multiplies the existing complexity.

**The Doubling Paradox**

When we duplicate a universe and connect corresponding points,
we get more topology than the sum of parts. The "handshake" between
parallel universes creates 2^{n-1} - 1 new independent cycles.

**Information Density**

A hypercube on 2^n vertices has b₁ ≈ n·2^{n-1} cycles. The ratio
b₁/|V| ≈ n/2 grows with dimension. Higher-dimensional spaces are
"topologically denser" - more irreducible structure per vertex.

**Classical vs Quantum**

Q_1 (the path) is classical: b₁ = 0.
Q_n for n ≥ 2 has cycles, hence irreducible frustration.
The jump from Q_1 to Q_2 is the "genesis" - the first non-trivial
topology. But unlike the cycle graph where this is a single cycle,
the hypercube structure amplifies: each dimension contributes new
channels for harmonic content.
-/

end Diaspora.Hodge.HypercubeGraph
