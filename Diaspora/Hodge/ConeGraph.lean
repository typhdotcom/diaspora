import Diaspora.Hodge.WheelGraph
import Diaspora.Hodge.PathGraph

/-! # Cone Graph: b₁(cone(G)) = |E(G)| -/

open BigOperators Diaspora.Core Diaspora.Hodge

namespace Diaspora.Hodge.ConeGraph

/-! ## Definition: Cone Graph -/

/-- Helper to get i.val - 1 < n from i : Fin (n+1) and i.val > 0. -/
lemma fin_pred_lt {n : ℕ} (i : Fin (n + 1)) (hi : i.val > 0) : i.val - 1 < n := by
  have := i.isLt; omega

/-- The cone adjacency: the apex (vertex 0) connects to all other vertices.
    Original edges of G are preserved among vertices 1..n. -/
def coneAdj {n : ℕ} (G : DynamicGraph n) (i j : Fin (n + 1)) : Prop :=
  -- Apex edges: 0 ↔ k for all k > 0
  (i.val = 0 ∧ j.val > 0) ∨ (i.val > 0 ∧ j.val = 0) ∨
  -- Original edges: lifted from G
  (∃ (hi : i.val > 0) (hj : j.val > 0),
    (⟨i.val - 1, fin_pred_lt i hi⟩, ⟨j.val - 1, fin_pred_lt j hj⟩) ∈ G.active_edges)

instance coneAdjDecidable {n : ℕ} (G : DynamicGraph n) (i j : Fin (n + 1)) :
    Decidable (coneAdj G i j) := by
  unfold coneAdj
  infer_instance

/-- The cone graph: G with an apex (vertex 0) connected to all vertices of G.
    The original vertices of G become vertices 1..n. -/
def coneGraph {n : ℕ} (G : DynamicGraph n) : DynamicGraph (n + 1) where
  active_edges := Finset.filter (fun (i, j) => coneAdj G i j) Finset.univ
  symmetric := by
    intro i j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, coneAdj]
    constructor <;> intro h <;> {
      rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj, he⟩
      · right; left; exact ⟨hj, hi⟩
      · left; exact ⟨hj, hi⟩
      · right; right
        refine ⟨hj, hi, ?_⟩
        convert G.symmetric _ _ |>.mp he using 2
    }
  no_loops := by
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, coneAdj]
    intro h
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj, he⟩
    · omega
    · omega
    · exact G.no_loops _ he

/-! ## Edge Count of cone(G) -/

/-- Apex-out edges: (0, k) for k ∈ {1,...,n}. -/
def apexOutEdges (n : ℕ) : Finset (Fin (n+1) × Fin (n+1)) :=
  Finset.filter (fun p => p.1.val = 0 ∧ p.2.val > 0) Finset.univ

/-- Apex-in edges: (k, 0) for k ∈ {1,...,n}. -/
def apexInEdges (n : ℕ) : Finset (Fin (n+1) × Fin (n+1)) :=
  Finset.filter (fun p => p.1.val > 0 ∧ p.2.val = 0) Finset.univ

lemma apexOutEdges_card (n : ℕ) : (apexOutEdges n).card = n := by
  have h_eq : apexOutEdges n = Finset.univ.image
      (fun k : Fin n => ((0 : Fin (n+1)), ⟨k.val + 1, Nat.add_lt_add_right k.isLt 1⟩)) := by
    ext ⟨a, b⟩
    simp only [apexOutEdges, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro ⟨ha, hb⟩
      have hb_lt : b.val < n + 1 := b.isLt
      have hb' : b.val - 1 < n := by omega
      use ⟨b.val - 1, hb'⟩
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

lemma apexInEdges_card (n : ℕ) : (apexInEdges n).card = n := by
  have h_eq : apexInEdges n = Finset.univ.image
      (fun k : Fin n => (⟨k.val + 1, Nat.add_lt_add_right k.isLt 1⟩, (0 : Fin (n+1)))) := by
    ext ⟨a, b⟩
    simp only [apexInEdges, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro ⟨ha, hb⟩
      have ha_lt : a.val < n + 1 := a.isLt
      have ha' : a.val - 1 < n := by omega
      use ⟨a.val - 1, ha'⟩
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

/-- Lifted edges from G: preserved among vertices 1..n. -/
def liftedEdges {n : ℕ} (G : DynamicGraph n) : Finset (Fin (n+1) × Fin (n+1)) :=
  Finset.filter (fun p => ∃ (h1 : p.1.val > 0) (h2 : p.2.val > 0),
    (⟨p.1.val - 1, fin_pred_lt p.1 h1⟩, ⟨p.2.val - 1, fin_pred_lt p.2 h2⟩) ∈ G.active_edges) Finset.univ

lemma liftedEdges_card {n : ℕ} (G : DynamicGraph n) :
    (liftedEdges G).card = G.active_edges.card := by
  have h_bij : liftedEdges G = G.active_edges.image
      (fun (p : Fin n × Fin n) =>
        ((⟨p.1.val + 1, Nat.add_lt_add_right p.1.isLt 1⟩ : Fin (n+1)),
         (⟨p.2.val + 1, Nat.add_lt_add_right p.2.isLt 1⟩ : Fin (n+1)))) := by
    ext ⟨a, b⟩
    simp only [liftedEdges, Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro h
      rw [Finset.mem_filter] at h
      obtain ⟨_, ha, hb, he⟩ := h
      simp only [] at ha hb he
      have ha_lt : a.val - 1 < n := fin_pred_lt a ha
      have hb_lt : b.val - 1 < n := fin_pred_lt b hb
      let a' : Fin n := ⟨a.val - 1, ha_lt⟩
      let b' : Fin n := ⟨b.val - 1, hb_lt⟩
      use (a', b')
      have ha_bound : a.val < n + 1 := a.isLt
      have hb_bound : b.val < n + 1 := b.isLt
      refine ⟨?_, ?_, ?_⟩
      · convert he using 2
      · show (⟨a'.val + 1, _⟩ : Fin (n + 1)) = a
        ext; simp only [a']; omega
      · show (⟨b'.val + 1, _⟩ : Fin (n + 1)) = b
        ext; simp only [b']; omega
    · intro ⟨⟨i, j⟩, he, hi, hj⟩
      rw [Finset.mem_filter]
      simp only [Fin.ext_iff] at hi hj
      have ha' : a.val > 0 := by omega
      have hb' : b.val > 0 := by omega
      refine ⟨Finset.mem_univ _, ha', hb', ?_⟩
      have ha_bound : a.val < n + 1 := a.isLt
      have hb_bound : b.val < n + 1 := b.isLt
      convert he using 2
      · ext; simp only []; omega
      · ext; simp only []; omega
  rw [h_bij, Finset.card_image_of_injective]
  intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
  simp only [Prod.mk.injEq, Fin.ext_iff] at h ⊢
  omega

/-- The cone graph edge count: 2n apex edges + original edges. -/
lemma cone_graph_directed_edge_count {n : ℕ} (G : DynamicGraph n) :
    (coneGraph G).active_edges.card = 2 * n + G.active_edges.card := by
  simp only [coneGraph]
  have h_split : (Finset.filter (fun p : Fin (n+1) × Fin (n+1) => coneAdj G p.1 p.2) Finset.univ) =
      apexOutEdges n ∪ apexInEdges n ∪ liftedEdges G := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
               coneAdj, apexOutEdges, apexInEdges, liftedEdges]
    constructor
    · intro h
      rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb, he⟩
      · left; left; exact ⟨ha, hb⟩
      · left; right; exact ⟨ha, hb⟩
      · right; exact ⟨ha, hb, he⟩
    · intro h
      rcases h with ((⟨ha, hb⟩ | ⟨ha, hb⟩) | ⟨ha, hb, he⟩)
      · left; exact ⟨ha, hb⟩
      · right; left; exact ⟨ha, hb⟩
      · right; right; exact ⟨ha, hb, he⟩
  rw [h_split]
  have h_disj1 : Disjoint (apexOutEdges n) (apexInEdges n) := by
    simp only [apexOutEdges, apexInEdges]
    rw [Finset.disjoint_filter]; intro _ _; omega
  have h_disj2 : Disjoint (apexOutEdges n) (liftedEdges G) := by
    rw [Finset.disjoint_iff_ne]
    intro ⟨a, b⟩ ha ⟨c, d⟩ hc heq
    simp only [apexOutEdges, Finset.mem_filter] at ha
    simp only [liftedEdges, Finset.mem_filter] at hc
    obtain ⟨_, ha_eq, _⟩ := ha
    obtain ⟨_, hc_gt, _, _⟩ := hc
    cases heq; omega
  have h_disj3 : Disjoint (apexInEdges n) (liftedEdges G) := by
    rw [Finset.disjoint_iff_ne]
    intro ⟨a, b⟩ ha ⟨c, d⟩ hc heq
    simp only [apexInEdges, Finset.mem_filter] at ha
    simp only [liftedEdges, Finset.mem_filter] at hc
    obtain ⟨_, _, hb_eq⟩ := ha
    obtain ⟨_, _, hd_gt, _⟩ := hc
    cases heq; omega
  have h_disj_union : Disjoint (apexOutEdges n ∪ apexInEdges n) (liftedEdges G) := by
    rw [Finset.disjoint_union_left]; exact ⟨h_disj2, h_disj3⟩
  rw [Finset.card_union_of_disjoint h_disj_union,
      Finset.card_union_of_disjoint h_disj1,
      apexOutEdges_card, apexInEdges_card, liftedEdges_card]
  ring

/-! ## Connectivity of cone(G) -/

/-- The cone of any graph is connected: the apex connects to everything. -/
lemma cone_graph_kernel_dim {n : ℕ} [NeZero n] (G : DynamicGraph n) :
    Module.finrank ℝ (LinearMap.ker (d_G_linear (coneGraph G))) = 1 := by
  let one : Fin (n+1) → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear (coneGraph G)) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G (coneGraph G) one).val.val i j = 0
    unfold d_G one
    simp only [coneGraph, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear (coneGraph G)) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      have h_const : ∀ i : Fin (n+1), φ i = φ 0 := by
        intro i
        by_cases hi : i.val = 0
        · have h_eq : i = 0 := Fin.ext hi; rw [h_eq]
        · have hi' : i.val > 0 := Nat.pos_of_ne_zero hi
          have h_edge : ((0 : Fin (n+1)), i) ∈ (coneGraph G).active_edges := by
            simp only [coneGraph, Finset.mem_filter, Finset.mem_univ, true_and, coneAdj]
            left; exact ⟨rfl, hi'⟩
          have h_zero : (d_G (coneGraph G) φ).val.val 0 i = 0 := by
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

/-- b₁(cone(G)) = |E(G)| -/
theorem cone_betti_eq_original_edges {n : ℕ} [NeZero n] [DecidableEq (Fin (n+1))] (G : DynamicGraph n) :
    Module.finrank ℝ (HarmonicSubspace (coneGraph G)) = G.active_edges.card / 2 := by
  have h_dim := harmonic_dimension_eq_cyclomatic (coneGraph G)
  have h_ker := cone_graph_kernel_dim G
  have h_edge := cone_graph_directed_edge_count G
  have h_edge_half : (coneGraph G).active_edges.card / 2 = n + G.active_edges.card / 2 := by
    rw [h_edge]
    have h_even := active_edges_even_card G
    obtain ⟨k, hk⟩ := h_even
    omega
  rw [h_edge_half, h_ker] at h_dim
  omega

/-- Coning increases b₁ by |V| - 1. -/
theorem cone_betti_increase {n : ℕ} [NeZero n] [DecidableEq (Fin n)] [DecidableEq (Fin (n+1))]
    (G : DynamicGraph n)
    (h_connected : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1) :
    Module.finrank ℝ (HarmonicSubspace (coneGraph G)) =
    Module.finrank ℝ (HarmonicSubspace G) + (n - 1) := by
  have h_cone := cone_betti_eq_original_edges G
  have h_G := harmonic_dimension_eq_cyclomatic G
  rw [h_connected] at h_G
  have h_n_pos : n ≥ 1 := NeZero.one_le
  rw [h_cone]
  -- h_G : dim(H) + n = |E|/2 + 1
  -- Goal: |E|/2 = dim(H) + (n - 1)
  omega

/-! ## The Fan Graph: Cone of a Path -/

/-- Fan graph: cone of a path. -/
def fanGraph (n : ℕ) [NeZero n] (hn : n ≥ 2 := by omega) : DynamicGraph (n + 1) :=
  coneGraph (PathGraph.pathGraph n hn)

/-- b₁(F_n) = n - 1. -/
theorem fan_graph_betti (n : ℕ) [NeZero n] [DecidableEq (Fin (n+1))] (hn : n ≥ 2) :
    Module.finrank ℝ (HarmonicSubspace (fanGraph n hn)) = n - 1 := by
  have h := cone_betti_eq_original_edges (PathGraph.pathGraph n hn)
  have h_path_edges := PathGraph.path_graph_directed_edge_count n hn
  simp only [fanGraph] at h ⊢
  rw [h, h_path_edges]
  omega

/-- Fan graph F_2 (a triangle) has b₁ = 1. -/
theorem fan2_betti_one [DecidableEq (Fin 3)] :
    Module.finrank ℝ (HarmonicSubspace (fanGraph 2 (by omega))) = 1 := by
  have h := fan_graph_betti 2 (by omega)
  omega

/-- Fan graph F_3 has b₁ = 2. -/
theorem fan3_betti_two [DecidableEq (Fin 4)] :
    Module.finrank ℝ (HarmonicSubspace (fanGraph 3 (by omega))) = 2 := by
  have h := fan_graph_betti 3 (by omega)
  omega

/-- Fan graph F_4 has b₁ = 3. -/
theorem fan4_betti_three [DecidableEq (Fin 5)] :
    Module.finrank ℝ (HarmonicSubspace (fanGraph 4 (by omega))) = 3 := by
  have h := fan_graph_betti 4 (by omega)
  omega

/-! ## Corollaries -/

/-- W_n = cone(C_n), so b₁(W_n) = n. -/
theorem wheel_is_cone_of_cycle (n : ℕ) [NeZero n] (hn : n ≥ 3) :
    Module.finrank ℝ (HarmonicSubspace (WheelGraph.wheelGraph n hn)) =
    (CycleGraph.cycleGraph n (by omega)).active_edges.card / 2 := by
  rw [WheelGraph.wheel_graph_betti_1 n hn]
  rw [CycleGraph.cycle_graph_directed_edge_count n hn]
  omega

/-- Coning never decreases b₁. -/
theorem observation_amplification {n : ℕ} [NeZero n] [DecidableEq (Fin n)] [DecidableEq (Fin (n+1))]
    (G : DynamicGraph n)
    (h_connected : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1) :
    Module.finrank ℝ (HarmonicSubspace (coneGraph G)) ≥
    Module.finrank ℝ (HarmonicSubspace G) := by
  rw [cone_betti_increase G h_connected]
  omega

/-- b₁(cone(G)) > 0 iff b₁(G) > 0 or n ≥ 2. -/
theorem coning_preserves_topology {n : ℕ} [NeZero n] [DecidableEq (Fin n)] [DecidableEq (Fin (n+1))]
    (G : DynamicGraph n)
    (h_connected : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1) :
    Module.finrank ℝ (HarmonicSubspace (coneGraph G)) > 0 ↔
    (Module.finrank ℝ (HarmonicSubspace G) > 0 ∨ n ≥ 2) := by
  rw [cone_betti_increase G h_connected]
  constructor
  · intro h
    by_cases hG : Module.finrank ℝ (HarmonicSubspace G) > 0
    · left; exact hG
    · right; omega
  · intro h
    rcases h with hG | hn
    · omega
    · omega

end Diaspora.Hodge.ConeGraph
