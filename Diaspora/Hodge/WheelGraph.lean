/-
# Wheel Graph Betti Numbers

The wheel graph W_n (hub connected to n-cycle) has Betti number:
  b₁(W_n) = n

This is a striking result: adding a "central observer" to a cycle
doesn't simplify topology—it multiplies it.

The n-cycle alone has b₁ = 1 (one independent cycle).
Adding a hub creates n independent cycles (each spoke forms a
new cycle with part of the rim).

Physical interpretation: An observer that "sees everything" creates
n channels of irreducible frustration. Observation amplifies rather
than resolves the harmonic content. The hub cannot relax the cycle
because every shortcut it provides creates a new cycle.
-/

import Diaspora.Hodge.IndexTheorem
import Mathlib.LinearAlgebra.Dimension.Finrank

open BigOperators Diaspora.Core Diaspora.Hodge

namespace Diaspora.Hodge.WheelGraph

/-! ## Definition: Wheel Graph W_n -/

/-- Wheel adjacency predicate.
    Vertex 0 is the hub; vertices 1..n form the rim.
    Hub connects to all rim vertices; rim vertices connect cyclically. -/
def wheelAdj (n : ℕ) (i j : Fin (n + 1)) : Prop :=
  -- Spoke edges: hub (0) ↔ rim (1..n)
  (i.val = 0 ∧ 1 ≤ j.val) ∨ (1 ≤ i.val ∧ j.val = 0) ∨
  -- Rim edges: k ↔ k+1 (mod n) for k ∈ 1..n
  -- Written as: both ≥ 1, and |i - j| = 1 or {i,j} = {1,n}
  (1 ≤ i.val ∧ 1 ≤ j.val ∧
    ((i.val + 1 = j.val) ∨ (j.val + 1 = i.val) ∨
     (i.val = 1 ∧ j.val = n) ∨ (i.val = n ∧ j.val = 1)))

instance wheelAdjDecidable (n : ℕ) (i j : Fin (n + 1)) : Decidable (wheelAdj n i j) := by
  unfold wheelAdj
  infer_instance

/-- The wheel graph W_n on n+1 vertices. -/
def wheelGraph (n : ℕ) [NeZero n] (hn : n ≥ 3 := by omega) : DynamicGraph (n + 1) where
  active_edges := Finset.filter (fun (i, j) => wheelAdj n i j) Finset.univ
  symmetric := by
    intro i j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, wheelAdj]
    constructor <;> intro h <;> omega
  no_loops := by
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, wheelAdj]
    omega

/-! ## Edge Count of W_n -/

/-- Hub-out edges: (0, k) for k ∈ {1,...,n}. -/
def hubOutEdges (n : ℕ) : Finset (Fin (n+1) × Fin (n+1)) :=
  Finset.filter (fun p => p.1.val = 0 ∧ 1 ≤ p.2.val) Finset.univ

/-- Hub-in edges: (k, 0) for k ∈ {1,...,n}. -/
def hubInEdges (n : ℕ) : Finset (Fin (n+1) × Fin (n+1)) :=
  Finset.filter (fun p => 1 ≤ p.1.val ∧ p.2.val = 0) Finset.univ

/-- Rim forward edges: (k, k+1) for k ∈ {1,...,n-1} plus (n, 1). -/
def rimForwardEdges (n : ℕ) : Finset (Fin (n+1) × Fin (n+1)) :=
  Finset.filter (fun p => 1 ≤ p.1.val ∧ 1 ≤ p.2.val ∧
    (p.1.val + 1 = p.2.val ∨ (p.1.val = n ∧ p.2.val = 1))) Finset.univ

/-- Rim backward edges: (k+1, k) for k ∈ {1,...,n-1} plus (1, n). -/
def rimBackwardEdges (n : ℕ) : Finset (Fin (n+1) × Fin (n+1)) :=
  Finset.filter (fun p => 1 ≤ p.1.val ∧ 1 ≤ p.2.val ∧
    (p.2.val + 1 = p.1.val ∨ (p.1.val = 1 ∧ p.2.val = n))) Finset.univ

lemma hubOutEdges_card (n : ℕ) [NeZero n] : (hubOutEdges n).card = n := by
  have h_eq : hubOutEdges n = Finset.univ.image
      (fun k : Fin n => ((0 : Fin (n+1)), ⟨k.val + 1, Nat.add_lt_add_right k.isLt 1⟩)) := by
    ext ⟨a, b⟩
    simp only [hubOutEdges, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro ⟨ha, hb⟩
      have hb' : b.val - 1 < n := by omega
      use ⟨b.val - 1, hb'⟩
      constructor
      · ext; exact ha.symm
      · ext; simp only [Nat.sub_add_cancel hb]
    · intro ⟨k, hk⟩
      constructor
      · have := hk.1; simp only [Fin.ext_iff] at this; exact this.symm
      · have := hk.2; simp only [Fin.ext_iff] at this; omega
  rw [h_eq, Finset.card_image_of_injective]
  · simp only [Finset.card_univ, Fintype.card_fin]
  · intro i j h; simp only [Prod.mk.injEq, Fin.ext_iff] at h; omega

lemma hubInEdges_card (n : ℕ) [NeZero n] : (hubInEdges n).card = n := by
  have h_eq : hubInEdges n = Finset.univ.image
      (fun k : Fin n => (⟨k.val + 1, Nat.add_lt_add_right k.isLt 1⟩, (0 : Fin (n+1)))) := by
    ext ⟨a, b⟩
    simp only [hubInEdges, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro ⟨ha, hb⟩
      have ha' : a.val - 1 < n := by omega
      use ⟨a.val - 1, ha'⟩
      constructor
      · ext; simp only [Nat.sub_add_cancel ha]
      · ext; exact hb.symm
    · intro ⟨k, hk⟩
      constructor
      · have := hk.1; simp only [Fin.ext_iff] at this; omega
      · have := hk.2; simp only [Fin.ext_iff] at this; exact this.symm
  rw [h_eq, Finset.card_image_of_injective]
  · simp only [Finset.card_univ, Fintype.card_fin]
  · intro i j h; simp only [Prod.mk.injEq, Fin.ext_iff] at h; omega

lemma rimForwardEdges_card (n : ℕ) [NeZero n] (hn : n ≥ 3) : (rimForwardEdges n).card = n := by
  have h_eq : rimForwardEdges n = Finset.univ.image
      (fun k : Fin n =>
        let src : Fin (n+1) := ⟨k.val + 1, Nat.add_lt_add_right k.isLt 1⟩
        let dst : Fin (n+1) := if h : k.val + 1 < n then ⟨k.val + 2, by omega⟩ else ⟨1, by omega⟩
        (src, dst)) := by
    ext ⟨a, b⟩
    simp only [rimForwardEdges, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro ⟨ha, hb, hab⟩
      rcases hab with h_succ | ⟨h_an, h_b1⟩
      · have hk : a.val - 1 < n := by omega
        use ⟨a.val - 1, hk⟩
        constructor
        · ext; simp only [Nat.sub_add_cancel ha]
        · have h_lt : a.val - 1 + 1 < n := by omega
          simp only [h_lt, ↓reduceDIte, Fin.ext_iff]
          omega
      · have hk : n - 1 < n := by omega
        use ⟨n - 1, hk⟩
        constructor
        · ext; simp only [Nat.sub_add_cancel (by omega : 1 ≤ n)]; exact h_an.symm
        · have h_nlt : ¬(n - 1 + 1 < n) := by omega
          simp only [h_nlt, ↓reduceDIte, Fin.ext_iff]
          exact h_b1.symm
    · intro ⟨k, hk⟩
      have hsrc := hk.1
      have hdst := hk.2
      simp only [Fin.ext_iff] at hsrc hdst
      have hk_lt := k.isLt
      constructor
      · omega
      constructor
      · by_cases h_lt : k.val + 1 < n
        · simp only [h_lt, ↓reduceDIte, Fin.val_mk] at hdst; omega
        · simp only [h_lt, ↓reduceDIte, Fin.val_mk] at hdst; omega
      · by_cases h_lt : k.val + 1 < n
        · simp only [h_lt, ↓reduceDIte, Fin.val_mk] at hdst
          left; omega
        · simp only [h_lt, ↓reduceDIte, Fin.val_mk] at hdst
          right; constructor <;> omega
  rw [h_eq, Finset.card_image_of_injective]
  · simp only [Finset.card_univ, Fintype.card_fin]
  · intro i j h
    simp only [Prod.mk.injEq, Fin.ext_iff] at h
    omega

lemma rimBackwardEdges_card (n : ℕ) [NeZero n] (hn : n ≥ 3) : (rimBackwardEdges n).card = n := by
  have h_eq : rimBackwardEdges n = Finset.univ.image
      (fun k : Fin n =>
        let dst : Fin (n+1) := ⟨k.val + 1, Nat.add_lt_add_right k.isLt 1⟩
        let src : Fin (n+1) := if h : k.val + 1 < n then ⟨k.val + 2, by omega⟩ else ⟨1, by omega⟩
        (src, dst)) := by
    ext ⟨a, b⟩
    simp only [rimBackwardEdges, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro ⟨ha, hb, hab⟩
      rcases hab with h_succ | ⟨h_a1, h_bn⟩
      · have hk : b.val - 1 < n := by omega
        use ⟨b.val - 1, hk⟩
        constructor
        · have h_lt : b.val - 1 + 1 < n := by omega
          simp only [h_lt, ↓reduceDIte, Fin.ext_iff]
          omega
        · ext; simp only [Nat.sub_add_cancel hb]
      · have hk : n - 1 < n := by omega
        use ⟨n - 1, hk⟩
        constructor
        · have h_nlt : ¬(n - 1 + 1 < n) := by omega
          simp only [h_nlt, ↓reduceDIte, Fin.ext_iff]
          exact h_a1.symm
        · ext; simp only [Nat.sub_add_cancel (by omega : 1 ≤ n)]; exact h_bn.symm
    · intro ⟨k, hk⟩
      have hsrc := hk.1
      have hdst := hk.2
      simp only [Fin.ext_iff] at hsrc hdst
      have hk_lt := k.isLt
      constructor
      · by_cases h_lt : k.val + 1 < n
        · simp only [h_lt, ↓reduceDIte, Fin.val_mk] at hsrc; omega
        · simp only [h_lt, ↓reduceDIte, Fin.val_mk] at hsrc; omega
      constructor
      · omega
      · by_cases h_lt : k.val + 1 < n
        · simp only [h_lt, ↓reduceDIte, Fin.val_mk] at hsrc
          left; omega
        · simp only [h_lt, ↓reduceDIte, Fin.val_mk] at hsrc
          right; constructor <;> omega
  rw [h_eq, Finset.card_image_of_injective]
  · simp only [Finset.card_univ, Fintype.card_fin]
  · intro i j h
    simp only [Prod.mk.injEq, Fin.ext_iff] at h
    have hi_lt := i.isLt
    have hj_lt := j.isLt
    by_cases hi : i.val + 1 < n <;> by_cases hj : j.val + 1 < n
    · simp only [hi, hj, ↓reduceDIte, Fin.val_mk] at h; omega
    · simp only [hi, hj, ↓reduceDIte, Fin.val_mk] at h; omega
    · simp only [hi, hj, ↓reduceDIte, Fin.val_mk] at h; omega
    · simp only [hi, hj, ↓reduceDIte, Fin.val_mk] at h; omega

lemma wheel_edges_decomposition (n : ℕ) [NeZero n] (hn : n ≥ 3) :
    (wheelGraph n hn).active_edges =
      hubOutEdges n ∪ hubInEdges n ∪ rimForwardEdges n ∪ rimBackwardEdges n := by
  ext ⟨a, b⟩
  simp only [wheelGraph, Finset.mem_filter, Finset.mem_univ, true_and, wheelAdj,
             Finset.mem_union, hubOutEdges, hubInEdges, rimForwardEdges, rimBackwardEdges]
  constructor
  · intro h
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb, hc⟩
    · left; left; left; exact ⟨ha, hb⟩
    · left; left; right; exact ⟨ha, hb⟩
    · rcases hc with h1 | h2 | h3 | h4
      · left; right; exact ⟨ha, hb, Or.inl h1⟩
      · right; exact ⟨ha, hb, Or.inl h2⟩
      · right; exact ⟨ha, hb, Or.inr h3⟩
      · left; right; exact ⟨ha, hb, Or.inr h4⟩
  · intro h
    rcases h with (((⟨ha, hb⟩ | ⟨ha, hb⟩) | ⟨ha, hb, hc⟩) | ⟨ha, hb, hc⟩)
    · left; exact ⟨ha, hb⟩
    · right; left; exact ⟨ha, hb⟩
    · right; right
      rcases hc with h1 | h2
      · exact ⟨ha, hb, Or.inl h1⟩
      · exact ⟨ha, hb, Or.inr (Or.inr (Or.inr h2))⟩
    · right; right
      rcases hc with h1 | h2
      · exact ⟨ha, hb, Or.inr (Or.inl h1)⟩
      · exact ⟨ha, hb, Or.inr (Or.inr (Or.inl h2))⟩

lemma wheel_edges_disjoint (n : ℕ) [NeZero n] (hn : n ≥ 3) :
    Disjoint (hubOutEdges n) (hubInEdges n) ∧
    Disjoint (hubOutEdges n) (rimForwardEdges n) ∧
    Disjoint (hubOutEdges n) (rimBackwardEdges n) ∧
    Disjoint (hubInEdges n) (rimForwardEdges n) ∧
    Disjoint (hubInEdges n) (rimBackwardEdges n) ∧
    Disjoint (rimForwardEdges n) (rimBackwardEdges n) := by
  simp only [hubOutEdges, hubInEdges, rimForwardEdges, rimBackwardEdges]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> {
    rw [Finset.disjoint_filter]
    intro ⟨a, b⟩ _
    omega
  }

/-- W_n has 4n directed edges (2n undirected: n spokes + n rim). -/
lemma wheel_graph_directed_edge_count (n : ℕ) [NeZero n] (hn : n ≥ 3) :
    (wheelGraph n hn).active_edges.card = 4 * n := by
  rw [wheel_edges_decomposition n hn]
  have hdisj := wheel_edges_disjoint n hn
  have h1 := hubOutEdges_card n
  have h2 := hubInEdges_card n
  have h3 := rimForwardEdges_card n hn
  have h4 := rimBackwardEdges_card n hn
  -- ((A ∪ B) ∪ C) ∪ D
  -- Need: (A ∪ B ∪ C) disjoint from D
  -- hdisj = ⟨d₁, d₂, d₃, d₄, d₅, d₆⟩ where:
  -- d₁ = hubOut ⊥ hubIn, d₂ = hubOut ⊥ rimFwd, d₃ = hubOut ⊥ rimBack
  -- d₄ = hubIn ⊥ rimFwd, d₅ = hubIn ⊥ rimBack, d₆ = rimFwd ⊥ rimBack
  have hd_last : Disjoint (hubOutEdges n ∪ hubInEdges n ∪ rimForwardEdges n) (rimBackwardEdges n) := by
    rw [Finset.disjoint_union_left]
    constructor
    · rw [Finset.disjoint_union_left]
      exact ⟨hdisj.2.2.1, hdisj.2.2.2.2.1⟩
    · exact hdisj.2.2.2.2.2
  rw [Finset.card_union_of_disjoint hd_last]
  -- Now ((A ∪ B) ∪ C)
  have hd_mid : Disjoint (hubOutEdges n ∪ hubInEdges n) (rimForwardEdges n) := by
    rw [Finset.disjoint_union_left]
    exact ⟨hdisj.2.1, hdisj.2.2.2.1⟩
  rw [Finset.card_union_of_disjoint hd_mid]
  -- Now (A ∪ B)
  rw [Finset.card_union_of_disjoint hdisj.1]
  rw [h1, h2, h3, h4]
  ring

/-! ## Connectivity of W_n -/

/-- W_n is connected: the gradient kernel is 1-dimensional.

The hub connects directly to every rim vertex, so any two vertices
are at most 2 edges apart. This means constant functions span the kernel.
-/
lemma wheel_graph_kernel_dim (n : ℕ) [NeZero n] (hn : n ≥ 3) :
    Module.finrank ℝ (LinearMap.ker (d_G_linear (wheelGraph n hn))) = 1 := by
  let one : Fin (n+1) → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear (wheelGraph n hn)) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G (wheelGraph n hn) one).val.val i j = 0
    unfold d_G one
    simp only [wheelGraph, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear (wheelGraph n hn)) =
                       Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h_const : ∀ i : Fin (n+1), φ i = φ 0 := by
        intro i
        by_cases hi : i.val = 0
        · have h_eq : i = 0 := Fin.ext hi
          rw [h_eq]
        · have hi' : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr hi
          have h_edge : ((0 : Fin (n+1)), i) ∈ (wheelGraph n hn).active_edges := by
            simp only [wheelGraph, Finset.mem_filter, Finset.mem_univ, true_and, wheelAdj]
            left; exact ⟨rfl, hi'⟩
          have h_zero : (d_G (wheelGraph n hn) φ).val.val 0 i = 0 := by
            have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 i
            exact this
          unfold d_G at h_zero
          simp only [h_edge, ↓reduceIte] at h_zero
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

/-! ## The Main Theorem -/

/-- **Wheel Graph Betti Number Theorem**: b₁(W_n) = n for n ≥ 3.

    The wheel graph has n independent cycles. Each spoke creates a new
    cycle with part of the rim, but these cycles overlap to form a basis
    of exactly n independent modes.

    Interpretation: A central observer that "sees everything" on a cycle
    creates n times as much irreducible frustration as the cycle alone.
    Observation amplifies topology rather than resolving it.
-/
theorem wheel_graph_betti_1 (n : ℕ) [NeZero n] [DecidableEq (Fin (n+1))] (hn : n ≥ 3) :
    Module.finrank ℝ (HarmonicSubspace (wheelGraph n hn)) = n := by
  have h_dim := harmonic_dimension_eq_cyclomatic (wheelGraph n hn)
  have h_ker := wheel_graph_kernel_dim n hn
  have h_edge := wheel_graph_directed_edge_count n hn
  have h_edge_half : (wheelGraph n hn).active_edges.card / 2 = 2 * n := by
    rw [h_edge]; omega
  rw [h_edge_half, h_ker] at h_dim
  omega

/-- W_3 (tetrahedron minus one face) has b₁ = 3. -/
theorem W3_betti_three [DecidableEq (Fin 4)] :
    Module.finrank ℝ (HarmonicSubspace (wheelGraph 3 (by omega))) = 3 :=
  wheel_graph_betti_1 3 (by omega)

/-- W_4 (square with center) has b₁ = 4. -/
theorem W4_betti_four [DecidableEq (Fin 5)] :
    Module.finrank ℝ (HarmonicSubspace (wheelGraph 4 (by omega))) = 4 :=
  wheel_graph_betti_1 4 (by omega)

/-- W_5 (pentagon with center) has b₁ = 5. -/
theorem W5_betti_five [DecidableEq (Fin 6)] :
    Module.finrank ℝ (HarmonicSubspace (wheelGraph 5 (by omega))) = 5 :=
  wheel_graph_betti_1 5 (by omega)

/-! ## Philosophical Corollaries -/

/-- Adding a hub to a cycle multiplies the Betti number by n.

    The n-cycle has b₁ = 1. The wheel has b₁ = n.
    Observation creates n times the frustration.
-/
theorem observation_amplifies_topology (n : ℕ) [NeZero n] [DecidableEq (Fin (n+1))] (hn : n ≥ 3) :
    Module.finrank ℝ (HarmonicSubspace (wheelGraph n hn)) =
    n * 1 := by
  rw [wheel_graph_betti_1 n hn, mul_one]

/-- The wheel graph always has non-trivial topology for n ≥ 3. -/
theorem wheel_has_cycles (n : ℕ) [NeZero n] [DecidableEq (Fin (n+1))] (hn : n ≥ 3) :
    Module.finrank ℝ (HarmonicSubspace (wheelGraph n hn)) ≥ 1 := by
  rw [wheel_graph_betti_1 n hn]
  omega

end Diaspora.Hodge.WheelGraph
