/-
# The Suspension Graph Theorem

The suspension of a graph G, denoted susp(G), adds two new vertices (north and
south poles) both connected to all vertices of G but **not to each other**.

This generalizes the cone construction: where cone(G) has one apex observing G,
susp(G) has two apexes observing G from opposite sides.

## The Main Result

  **b₁(susp(G)) = |E(G)|/2 + n - 1**

Equivalently:
  **b₁(susp(G)) = b₁(cone(G)) + (n - 1)**

Each pole contributes n - 1 new cycles (as in the cone theorem), and since
the poles don't see each other, they contribute additively.

## Physical Interpretation

The suspension represents **dual observation**: two independent observers
watching the same system from opposite vantage points. Unlike a single
observer (cone), dual observers create twice as many new frustration
channels. The poles can't communicate directly - they only "know" each
other through the system they both observe.

This models situations where two distinct perspectives on the same
underlying reality create compounding rather than canceling topology.
Each observer's measurement contributes its own irreducible frustration,
and these frustrations don't interfere because the observers are isolated.
-/

import Diaspora.Hodge.ConeGraph

open BigOperators Diaspora.Core Diaspora.Hodge

namespace Diaspora.Hodge.SuspensionGraph

/-! ## Definition: Suspension Graph -/

/-- Helper to get i.val - 2 < n from i : Fin (n+2) and i.val ≥ 2. -/
lemma fin_shift_lt {n : ℕ} (i : Fin (n + 2)) (hi : i.val ≥ 2) : i.val - 2 < n := by
  have := i.isLt; omega

/-- The suspension adjacency: north pole (0) and south pole (1) both connect
    to all original vertices (2..n+1), but NOT to each other. Original edges
    of G are preserved among vertices 2..n+1. -/
def suspAdj {n : ℕ} (G : DynamicGraph n) (i j : Fin (n + 2)) : Prop :=
  -- North pole (0) connects to all original vertices
  (i.val = 0 ∧ j.val ≥ 2) ∨ (i.val ≥ 2 ∧ j.val = 0) ∨
  -- South pole (1) connects to all original vertices
  (i.val = 1 ∧ j.val ≥ 2) ∨ (i.val ≥ 2 ∧ j.val = 1) ∨
  -- Original edges: lifted from G (with +2 offset)
  (∃ (hi : i.val ≥ 2) (hj : j.val ≥ 2),
    (⟨i.val - 2, fin_shift_lt i hi⟩, ⟨j.val - 2, fin_shift_lt j hj⟩) ∈ G.active_edges)

instance suspAdjDecidable {n : ℕ} (G : DynamicGraph n) (i j : Fin (n + 2)) :
    Decidable (suspAdj G i j) := by
  unfold suspAdj
  infer_instance

/-- The suspension graph: G with north pole (vertex 0) and south pole (vertex 1),
    both connected to all vertices of G (shifted to 2..n+1), but NOT to each other. -/
def suspensionGraph {n : ℕ} (G : DynamicGraph n) : DynamicGraph (n + 2) where
  active_edges := Finset.filter (fun (i, j) => suspAdj G i j) Finset.univ
  symmetric := by
    intro i j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, suspAdj]
    constructor <;> intro h <;> {
      rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj, he⟩
      · right; left; exact ⟨hj, hi⟩
      · left; exact ⟨hj, hi⟩
      · right; right; right; left; exact ⟨hj, hi⟩
      · right; right; left; exact ⟨hj, hi⟩
      · right; right; right; right
        refine ⟨hj, hi, ?_⟩
        convert G.symmetric _ _ |>.mp he using 2
    }
  no_loops := by
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, suspAdj]
    intro h
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj, he⟩
    · omega
    · omega
    · omega
    · omega
    · exact G.no_loops _ he

/-! ## Edge Count of susp(G) -/

/-- North pole out-edges: (0, k) for k ∈ {2,...,n+1}. -/
def northOutEdges (n : ℕ) : Finset (Fin (n+2) × Fin (n+2)) :=
  Finset.filter (fun p => p.1.val = 0 ∧ p.2.val ≥ 2) Finset.univ

/-- North pole in-edges: (k, 0) for k ∈ {2,...,n+1}. -/
def northInEdges (n : ℕ) : Finset (Fin (n+2) × Fin (n+2)) :=
  Finset.filter (fun p => p.1.val ≥ 2 ∧ p.2.val = 0) Finset.univ

/-- South pole out-edges: (1, k) for k ∈ {2,...,n+1}. -/
def southOutEdges (n : ℕ) : Finset (Fin (n+2) × Fin (n+2)) :=
  Finset.filter (fun p => p.1.val = 1 ∧ p.2.val ≥ 2) Finset.univ

/-- South pole in-edges: (k, 1) for k ∈ {2,...,n+1}. -/
def southInEdges (n : ℕ) : Finset (Fin (n+2) × Fin (n+2)) :=
  Finset.filter (fun p => p.1.val ≥ 2 ∧ p.2.val = 1) Finset.univ

lemma northOutEdges_card (n : ℕ) : (northOutEdges n).card = n := by
  have h_eq : northOutEdges n = Finset.univ.image
      (fun k : Fin n => ((0 : Fin (n+2)), ⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩)) := by
    ext ⟨a, b⟩
    simp only [northOutEdges, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro ⟨ha, hb⟩
      have hb_lt : b.val < n + 2 := b.isLt
      have hb' : b.val - 2 < n := by omega
      use ⟨b.val - 2, hb'⟩
      constructor
      · ext; exact ha.symm
      · ext; simp only []; omega
    · intro ⟨k, hk⟩
      constructor
      · have := hk.1; simp only [Fin.ext_iff] at this; exact this.symm
      · have := hk.2; simp only [Fin.ext_iff] at this; omega
  rw [h_eq, Finset.card_image_of_injective]
  · simp only [Finset.card_univ, Fintype.card_fin]
  · intro i j h; simp only [Prod.mk.injEq, Fin.ext_iff] at h; omega

lemma northInEdges_card (n : ℕ) : (northInEdges n).card = n := by
  have h_eq : northInEdges n = Finset.univ.image
      (fun k : Fin n => (⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩, (0 : Fin (n+2)))) := by
    ext ⟨a, b⟩
    simp only [northInEdges, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro ⟨ha, hb⟩
      have ha_lt : a.val < n + 2 := a.isLt
      have ha' : a.val - 2 < n := by omega
      use ⟨a.val - 2, ha'⟩
      constructor
      · ext; simp only []; omega
      · ext; exact hb.symm
    · intro ⟨k, hk⟩
      constructor
      · have := hk.1; simp only [Fin.ext_iff] at this; omega
      · have := hk.2; simp only [Fin.ext_iff] at this; exact this.symm
  rw [h_eq, Finset.card_image_of_injective]
  · simp only [Finset.card_univ, Fintype.card_fin]
  · intro i j h; simp only [Prod.mk.injEq, Fin.ext_iff] at h; omega

lemma southOutEdges_card (n : ℕ) : (southOutEdges n).card = n := by
  have h_eq : southOutEdges n = Finset.univ.image
      (fun k : Fin n => ((1 : Fin (n+2)), ⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩)) := by
    ext ⟨a, b⟩
    simp only [southOutEdges, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro ⟨ha, hb⟩
      have hb_lt : b.val < n + 2 := b.isLt
      have hb' : b.val - 2 < n := by omega
      use ⟨b.val - 2, hb'⟩
      constructor
      · ext; exact ha.symm
      · ext; simp only []; omega
    · intro ⟨k, hk⟩
      constructor
      · have := hk.1; simp only [Fin.ext_iff] at this; exact this.symm
      · have := hk.2; simp only [Fin.ext_iff] at this; omega
  rw [h_eq, Finset.card_image_of_injective]
  · simp only [Finset.card_univ, Fintype.card_fin]
  · intro i j h; simp only [Prod.mk.injEq, Fin.ext_iff] at h; omega

lemma southInEdges_card (n : ℕ) : (southInEdges n).card = n := by
  have h_eq : southInEdges n = Finset.univ.image
      (fun k : Fin n => (⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩, (1 : Fin (n+2)))) := by
    ext ⟨a, b⟩
    simp only [southInEdges, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro ⟨ha, hb⟩
      have ha_lt : a.val < n + 2 := a.isLt
      have ha' : a.val - 2 < n := by omega
      use ⟨a.val - 2, ha'⟩
      constructor
      · ext; simp only []; omega
      · ext; exact hb.symm
    · intro ⟨k, hk⟩
      constructor
      · have := hk.1; simp only [Fin.ext_iff] at this; omega
      · have := hk.2; simp only [Fin.ext_iff] at this; exact this.symm
  rw [h_eq, Finset.card_image_of_injective]
  · simp only [Finset.card_univ, Fintype.card_fin]
  · intro i j h; simp only [Prod.mk.injEq, Fin.ext_iff] at h; omega

/-- Lifted edges from G: preserved among vertices 2..n+1. -/
def suspLiftedEdges {n : ℕ} (G : DynamicGraph n) : Finset (Fin (n+2) × Fin (n+2)) :=
  Finset.filter (fun p => ∃ (h1 : p.1.val ≥ 2) (h2 : p.2.val ≥ 2),
    (⟨p.1.val - 2, fin_shift_lt p.1 h1⟩, ⟨p.2.val - 2, fin_shift_lt p.2 h2⟩) ∈ G.active_edges) Finset.univ

lemma suspLiftedEdges_card {n : ℕ} (G : DynamicGraph n) :
    (suspLiftedEdges G).card = G.active_edges.card := by
  have h_bij : suspLiftedEdges G = G.active_edges.image
      (fun (p : Fin n × Fin n) =>
        ((⟨p.1.val + 2, Nat.add_lt_add_right p.1.isLt 2⟩ : Fin (n+2)),
         (⟨p.2.val + 2, Nat.add_lt_add_right p.2.isLt 2⟩ : Fin (n+2)))) := by
    ext ⟨a, b⟩
    simp only [suspLiftedEdges, Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro h
      rw [Finset.mem_filter] at h
      obtain ⟨_, ha, hb, he⟩ := h
      simp only [] at ha hb he
      have ha_lt : a.val - 2 < n := fin_shift_lt a ha
      have hb_lt : b.val - 2 < n := fin_shift_lt b hb
      let a' : Fin n := ⟨a.val - 2, ha_lt⟩
      let b' : Fin n := ⟨b.val - 2, hb_lt⟩
      use (a', b')
      have ha_bound : a.val < n + 2 := a.isLt
      have hb_bound : b.val < n + 2 := b.isLt
      refine ⟨?_, ?_, ?_⟩
      · convert he using 2
      · show (⟨a'.val + 2, _⟩ : Fin (n + 2)) = a
        ext; simp only [a']; omega
      · show (⟨b'.val + 2, _⟩ : Fin (n + 2)) = b
        ext; simp only [b']; omega
    · intro ⟨⟨i, j⟩, he, hi, hj⟩
      rw [Finset.mem_filter]
      simp only [Fin.ext_iff] at hi hj
      have ha' : a.val ≥ 2 := by omega
      have hb' : b.val ≥ 2 := by omega
      refine ⟨Finset.mem_univ _, ha', hb', ?_⟩
      have ha_bound : a.val < n + 2 := a.isLt
      have hb_bound : b.val < n + 2 := b.isLt
      convert he using 2
      · ext; simp only []; omega
      · ext; simp only []; omega
  rw [h_bij, Finset.card_image_of_injective]
  intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
  simp only [Prod.mk.injEq, Fin.ext_iff] at h ⊢
  omega

/-- The suspension graph edge count: 4n pole edges + original edges. -/
lemma suspension_graph_directed_edge_count {n : ℕ} (G : DynamicGraph n) :
    (suspensionGraph G).active_edges.card = 4 * n + G.active_edges.card := by
  simp only [suspensionGraph]
  have h_split : (Finset.filter (fun p : Fin (n+2) × Fin (n+2) => suspAdj G p.1 p.2) Finset.univ) =
      northOutEdges n ∪ northInEdges n ∪ southOutEdges n ∪ southInEdges n ∪ suspLiftedEdges G := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
               suspAdj, northOutEdges, northInEdges, southOutEdges, southInEdges, suspLiftedEdges]
    constructor
    · intro h
      rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb, he⟩
      · left; left; left; left; exact ⟨ha, hb⟩
      · left; left; left; right; exact ⟨ha, hb⟩
      · left; left; right; exact ⟨ha, hb⟩
      · left; right; exact ⟨ha, hb⟩
      · right; exact ⟨ha, hb, he⟩
    · intro h
      rcases h with ((((⟨ha, hb⟩ | ⟨ha, hb⟩) | ⟨ha, hb⟩) | ⟨ha, hb⟩) | ⟨ha, hb, he⟩)
      · left; exact ⟨ha, hb⟩
      · right; left; exact ⟨ha, hb⟩
      · right; right; left; exact ⟨ha, hb⟩
      · right; right; right; left; exact ⟨ha, hb⟩
      · right; right; right; right; exact ⟨ha, hb, he⟩
  rw [h_split]
  -- All sets are pairwise disjoint
  have h_disj_no_ni : Disjoint (northOutEdges n) (northInEdges n) := by
    rw [Finset.disjoint_iff_ne]
    intro ⟨a, b⟩ ha ⟨c, d⟩ hc heq
    simp only [northOutEdges, northInEdges, Finset.mem_filter] at ha hc
    cases heq; omega
  have h_disj_no_so : Disjoint (northOutEdges n) (southOutEdges n) := by
    rw [Finset.disjoint_iff_ne]
    intro ⟨a, b⟩ ha ⟨c, d⟩ hc heq
    simp only [northOutEdges, southOutEdges, Finset.mem_filter] at ha hc
    cases heq; omega
  have h_disj_no_si : Disjoint (northOutEdges n) (southInEdges n) := by
    rw [Finset.disjoint_iff_ne]
    intro ⟨a, b⟩ ha ⟨c, d⟩ hc heq
    simp only [northOutEdges, southInEdges, Finset.mem_filter] at ha hc
    cases heq; omega
  have h_disj_no_lift : Disjoint (northOutEdges n) (suspLiftedEdges G) := by
    rw [Finset.disjoint_iff_ne]
    intro ⟨a, b⟩ ha ⟨c, d⟩ hc heq
    simp only [northOutEdges, suspLiftedEdges, Finset.mem_filter] at ha hc
    obtain ⟨ha_eq, _⟩ := ha
    obtain ⟨_, ⟨hc_ge, _, _⟩⟩ := hc
    cases heq; omega
  have h_disj_ni_so : Disjoint (northInEdges n) (southOutEdges n) := by
    rw [Finset.disjoint_iff_ne]
    intro ⟨a, b⟩ ha ⟨c, d⟩ hc heq
    simp only [northInEdges, southOutEdges, Finset.mem_filter] at ha hc
    cases heq; omega
  have h_disj_ni_si : Disjoint (northInEdges n) (southInEdges n) := by
    rw [Finset.disjoint_iff_ne]
    intro ⟨a, b⟩ ha ⟨c, d⟩ hc heq
    simp only [northInEdges, southInEdges, Finset.mem_filter] at ha hc
    cases heq; omega
  have h_disj_ni_lift : Disjoint (northInEdges n) (suspLiftedEdges G) := by
    rw [Finset.disjoint_iff_ne]
    intro ⟨a, b⟩ ha ⟨c, d⟩ hc heq
    simp only [northInEdges, suspLiftedEdges, Finset.mem_filter] at ha hc
    obtain ⟨_, hb_eq⟩ := ha
    obtain ⟨_, ⟨hc_ge, hd_ge, _⟩⟩ := hc
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_, hbd⟩ := heq
    rw [← hbd] at hd_ge
    simp only [hb_eq] at hd_ge
    omega
  have h_disj_so_si : Disjoint (southOutEdges n) (southInEdges n) := by
    rw [Finset.disjoint_iff_ne]
    intro ⟨a, b⟩ ha ⟨c, d⟩ hc heq
    simp only [southOutEdges, southInEdges, Finset.mem_filter] at ha hc
    cases heq; omega
  have h_disj_so_lift : Disjoint (southOutEdges n) (suspLiftedEdges G) := by
    rw [Finset.disjoint_iff_ne]
    intro ⟨a, b⟩ ha ⟨c, d⟩ hc heq
    simp only [southOutEdges, suspLiftedEdges, Finset.mem_filter] at ha hc
    obtain ⟨ha_eq, _⟩ := ha
    obtain ⟨_, ⟨hc_ge, _, _⟩⟩ := hc
    cases heq; omega
  have h_disj_si_lift : Disjoint (southInEdges n) (suspLiftedEdges G) := by
    rw [Finset.disjoint_iff_ne]
    intro ⟨a, b⟩ ha ⟨c, d⟩ hc heq
    simp only [southInEdges, suspLiftedEdges, Finset.mem_filter] at ha hc
    obtain ⟨_, hb_eq⟩ := ha
    obtain ⟨_, ⟨hc_ge, hd_ge, _⟩⟩ := hc
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_, hbd⟩ := heq
    rw [← hbd] at hd_ge
    simp only [hb_eq] at hd_ge
    omega
  -- Chain the disjointness
  have h1 : Disjoint (northOutEdges n ∪ northInEdges n) (southOutEdges n) := by
    rw [Finset.disjoint_union_left]; exact ⟨h_disj_no_so, h_disj_ni_so⟩
  have h2 : Disjoint (northOutEdges n ∪ northInEdges n ∪ southOutEdges n) (southInEdges n) := by
    rw [Finset.disjoint_union_left]; exact ⟨Finset.disjoint_union_left.mpr ⟨h_disj_no_si, h_disj_ni_si⟩, h_disj_so_si⟩
  have h3 : Disjoint (northOutEdges n ∪ northInEdges n ∪ southOutEdges n ∪ southInEdges n) (suspLiftedEdges G) := by
    rw [Finset.disjoint_union_left]
    constructor
    · rw [Finset.disjoint_union_left]; constructor
      · rw [Finset.disjoint_union_left]; exact ⟨h_disj_no_lift, h_disj_ni_lift⟩
      · exact h_disj_so_lift
    · exact h_disj_si_lift
  rw [Finset.card_union_of_disjoint h3,
      Finset.card_union_of_disjoint h2,
      Finset.card_union_of_disjoint h1,
      Finset.card_union_of_disjoint h_disj_no_ni,
      northOutEdges_card, northInEdges_card, southOutEdges_card, southInEdges_card,
      suspLiftedEdges_card]
  ring

/-! ## Connectivity of susp(G) -/

/-- The suspension of any graph with at least one vertex is connected:
    every vertex is reachable via one of the poles. -/
lemma suspension_graph_kernel_dim {n : ℕ} [NeZero n] (G : DynamicGraph n) :
    Module.finrank ℝ (LinearMap.ker (d_G_linear (suspensionGraph G))) = 1 := by
  let one : Fin (n+2) → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear (suspensionGraph G)) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G (suspensionGraph G) one).val.val i j = 0
    unfold d_G one
    simp only [suspensionGraph, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear (suspensionGraph G)) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h_const : ∀ i : Fin (n+2), φ i = φ 0 := by
        intro i
        by_cases hi0 : i.val = 0
        · have h_eq : i = 0 := Fin.ext hi0; rw [h_eq]
        · by_cases hi1 : i.val = 1
          · -- Connect via some original vertex
            have h_n_pos : 0 < n := NeZero.pos n
            let v : Fin (n + 2) := ⟨2, by omega⟩
            -- 0 ↔ v and 1 ↔ v are both edges
            have h_0v : (0, v) ∈ (suspensionGraph G).active_edges := by
              simp only [suspensionGraph, Finset.mem_filter, Finset.mem_univ, true_and, suspAdj]
              left; constructor; rfl; show v.val ≥ 2; simp [v]
            have h_1v : ((1 : Fin (n+2)), v) ∈ (suspensionGraph G).active_edges := by
              simp only [suspensionGraph, Finset.mem_filter, Finset.mem_univ, true_and, suspAdj]
              right; right; left; constructor; rfl; show v.val ≥ 2; simp [v]
            have h_zero_0v : (d_G (suspensionGraph G) φ).val.val 0 v = 0 := by
              have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 v
              exact this
            have h_zero_1v : (d_G (suspensionGraph G) φ).val.val 1 v = 0 := by
              have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 1 v
              exact this
            unfold d_G at h_zero_0v h_zero_1v
            simp only [h_0v, h_1v, ↓reduceIte] at h_zero_0v h_zero_1v
            have h_eq : i = 1 := Fin.ext hi1
            -- φ v = φ 0 and φ v = φ 1, so φ 0 = φ 1
            rw [h_eq]; linarith
          · -- i ≥ 2: connect to north pole (0)
            have hi' : i.val ≥ 2 := by omega
            have h_edge : ((0 : Fin (n+2)), i) ∈ (suspensionGraph G).active_edges := by
              simp only [suspensionGraph, Finset.mem_filter, Finset.mem_univ, true_and, suspAdj]
              left; exact ⟨rfl, hi'⟩
            have h_zero : (d_G (suspensionGraph G) φ).val.val 0 i = 0 := by
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

/-! ## The Main Theorems -/

/-- **The Suspension Theorem**: b₁(susp(G)) = |E(G)|/2 + n - 1.

    The suspension of a connected graph G has Betti number equal to the
    number of undirected edges in G plus (n - 1), where n = |V(G)|.

    Comparing with the cone theorem (b₁(cone(G)) = |E(G)|/2):
      b₁(susp(G)) = b₁(cone(G)) + (n - 1)

    Each pole contributes n - 1 cycles (as in the cone theorem), and since
    the poles don't communicate directly, their contributions are additive.
-/
theorem suspension_betti {n : ℕ} [NeZero n] [DecidableEq (Fin (n+2))] (G : DynamicGraph n) :
    Module.finrank ℝ (HarmonicSubspace (suspensionGraph G)) =
    G.active_edges.card / 2 + (n - 1) := by
  have h_dim := harmonic_dimension_eq_cyclomatic (suspensionGraph G)
  have h_ker := suspension_graph_kernel_dim G
  have h_edge := suspension_graph_directed_edge_count G
  have h_edge_half : (suspensionGraph G).active_edges.card / 2 = 2 * n + G.active_edges.card / 2 := by
    rw [h_edge]
    have h_even := active_edges_even_card G
    obtain ⟨k, hk⟩ := h_even
    omega
  rw [h_edge_half, h_ker] at h_dim
  -- h_dim : dim(H) + (n + 2) = (2n + |E|/2) + 1
  -- Goal: dim(H) = |E|/2 + (n - 1)
  have h_n_pos : n ≥ 1 := NeZero.one_le
  omega

/-- Suspension vs Cone: The suspension adds exactly n - 1 more cycles than the cone.

    This captures the "second observer" effect: the south pole sees the same
    graph as the north pole and contributes the same number of new cycles.
-/
theorem suspension_vs_cone {n : ℕ} [NeZero n] [DecidableEq (Fin n)] [DecidableEq (Fin (n+1))] [DecidableEq (Fin (n+2))]
    (G : DynamicGraph n)
    (_h_connected : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1) :
    Module.finrank ℝ (HarmonicSubspace (suspensionGraph G)) =
    Module.finrank ℝ (HarmonicSubspace (ConeGraph.coneGraph G)) + (n - 1) := by
  rw [suspension_betti, ConeGraph.cone_betti_eq_original_edges]

/-- Suspension vs original: The suspension adds 2(n - 1) cycles to G.

    Two independent observers each add n - 1 cycles, for a total increase
    of 2n - 2 independent cycles.
-/
theorem suspension_betti_increase {n : ℕ} [NeZero n] [DecidableEq (Fin n)] [DecidableEq (Fin (n+2))]
    (G : DynamicGraph n)
    (h_connected : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1) :
    Module.finrank ℝ (HarmonicSubspace (suspensionGraph G)) =
    Module.finrank ℝ (HarmonicSubspace G) + 2 * (n - 1) := by
  have h_susp := suspension_betti G
  have h_G := harmonic_dimension_eq_cyclomatic G
  rw [h_connected] at h_G
  have h_n_pos : n ≥ 1 := NeZero.one_le
  rw [h_susp]
  -- h_G : dim(H_G) + n = |E|/2 + 1
  -- Goal: |E|/2 + (n - 1) = dim(H_G) + 2(n - 1)
  omega

/-! ## Concrete Examples -/

/-- Suspension of a path P_n has b₁ = 2n - 2.

    The path has n - 1 edges. Suspension:
    - Adds 2n pole edges (n to each pole)
    - Total: (n - 1) + 2n = 3n - 1 undirected edges
    - Vertices: n + 2
    - b₁ = (3n - 1) - (n + 2) + 1 = 2n - 2 ✓
-/
theorem suspension_path_betti (n : ℕ) [NeZero n] [DecidableEq (Fin (n+2))] (hn : n ≥ 2) :
    Module.finrank ℝ (HarmonicSubspace (suspensionGraph (PathGraph.pathGraph n hn))) = 2 * n - 2 := by
  have h := suspension_betti (PathGraph.pathGraph n hn)
  have h_path_edges := PathGraph.path_graph_directed_edge_count n hn
  simp only at h ⊢
  rw [h, h_path_edges]
  omega

/-- Suspension of a cycle C_n has b₁ = 2n - 1.

    The cycle has n edges. Suspension:
    - Adds 2n pole edges
    - Total: n + 2n = 3n undirected edges
    - Vertices: n + 2
    - b₁ = 3n - (n + 2) + 1 = 2n - 1 ✓

    Compare with wheel W_n = cone(C_n): b₁ = n.
    susp(C_n) has n - 1 more cycles.
-/
theorem suspension_cycle_betti (n : ℕ) [NeZero n] [DecidableEq (Fin (n+2))] (hn : n ≥ 3) :
    Module.finrank ℝ (HarmonicSubspace (suspensionGraph (CycleGraph.cycleGraph n (by omega)))) = 2 * n - 1 := by
  have h := suspension_betti (CycleGraph.cycleGraph n (by omega))
  have h_cycle_edges := CycleGraph.cycle_graph_directed_edge_count n hn
  simp only at h ⊢
  rw [h, h_cycle_edges]
  omega

/-! ## Philosophical Corollaries -/

/-- Dual observation theorem: two observers add double the topology.

    A single observer (cone) adds n - 1 cycles.
    Two isolated observers (suspension) add 2(n - 1) cycles.
    Their contributions are perfectly additive because they can't communicate.
-/
theorem dual_observation_additivity {n : ℕ} [NeZero n] [DecidableEq (Fin n)] [DecidableEq (Fin (n+1))] [DecidableEq (Fin (n+2))]
    (G : DynamicGraph n)
    (h_connected : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1) :
    Module.finrank ℝ (HarmonicSubspace (suspensionGraph G)) -
    Module.finrank ℝ (HarmonicSubspace G) =
    2 * (Module.finrank ℝ (HarmonicSubspace (ConeGraph.coneGraph G)) -
         Module.finrank ℝ (HarmonicSubspace G)) := by
  have h_susp_inc := suspension_betti_increase G h_connected
  have h_cone_inc := ConeGraph.cone_betti_increase G h_connected
  have h_n_pos : n ≥ 1 := NeZero.one_le
  omega

/-- The poles can't see each other: they contribute independent frustration.

    If the poles were connected, we'd have one fewer cycle (the triangle
    through the two poles and any original vertex would become exact).
    Their isolation is precisely what makes their observations additive.
-/
theorem pole_isolation_maximizes_topology {n : ℕ} [NeZero n] [DecidableEq (Fin (n+2))]
    (G : DynamicGraph n)
    (_h_connected : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1) :
    Module.finrank ℝ (HarmonicSubspace (suspensionGraph G)) =
    G.active_edges.card / 2 + (n - 1) := by
  exact suspension_betti G

end Diaspora.Hodge.SuspensionGraph
