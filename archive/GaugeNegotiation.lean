/-
# Gauge Negotiation: Structural Consequences of Merging

Proves structural theorems about what happens when two configurations are merged.

The key results proven by construction:
1. Merging two holonomy-free systems can create holonomy (frustration emerges)
2. Merging a frustrated system with a counter-perspective can reduce holonomy

Both theorems use explicit 3-4 node examples with verified arithmetic.
-/

import Diaspora.GaugeTheoreticHolonomy

open GaugeTheoretic

namespace GaugeNegotiation

/-! ## Theorem 1: Negotiation Can Create Holonomy -/

/-- Graph for X_A: two edges forming a path 0 → 1 → 2 -/
def G_A : SimpleGraph (Fin 4) where
  Adj i j := (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)
  symm _ _ h := by cases h <;> tauto
  loopless i h := by cases h <;> omega

instance : DecidableRel G_A.Adj := fun i j => by
  unfold G_A
  infer_instance

/-- Graph for X_B: two edges forming a path 2 → 3 → 0 -/
def G_B : SimpleGraph (Fin 4) where
  Adj i j := (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨ (i = 3 ∧ j = 0) ∨ (i = 0 ∧ j = 3)
  symm _ _ h := by cases h <;> tauto
  loopless i h := by cases h <;> omega

instance : DecidableRel G_B.Adj := fun i j => by
  unfold G_B
  infer_instance

/-- Configuration X_A: path 0 → 1 → 2 with constraints 5.0 each -/
def X_A : ConfigSpace 4 := {
  graph := G_A
  adj_decidable := inferInstance
  node_phases := fun _ => 0
  constraints := fun _ _ _ => 5.0
}

/-- Configuration X_B: path 2 → 3 → 0 with constraints 5.0 each -/
def X_B : ConfigSpace 4 := {
  graph := G_B
  adj_decidable := inferInstance
  node_phases := fun _ => 0
  constraints := fun _ _ _ => 5.0
}

/-- Dummy task for negotiation -/
def task_4 : ExternalTask 4 := {
  measure_violation := fun _ => 0
  violation_nonneg := fun _ => le_refl 0
}

/-- The negotiation problem -/
def prob_create : NegotiationProblem 4 := {
  X_A := X_A
  X_B := X_B
  task := task_4
  lam := 1.0
  h_lam_pos := by norm_num
}

/-- The 4-cycle in the union graph: 0 → 1 → 2 → 3 → 0 -/
def cycle_union : Cycle 4 (union_config prob_create).graph 4 := {
  nodes := fun i =>
    match i with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => 2
    | ⟨3, _⟩ => 3
    | ⟨4, _⟩ => 0
    | ⟨n+5, h⟩ => absurd h (by omega)
  closes := by rfl
  adjacent := by
    intro i
    fin_cases i
    · -- 0 → 1
      show (union_config prob_create).graph.Adj 0 1
      unfold union_config prob_create X_A X_B
      show (graph_union G_A G_B).Adj 0 1
      unfold graph_union G_A
      left
      tauto
    · -- 1 → 2
      unfold union_config prob_create X_A X_B graph_union G_A
      left
      tauto
    · -- 2 → 3
      unfold union_config prob_create X_A X_B graph_union G_B
      right
      tauto
    · -- 3 → 0
      unfold union_config prob_create X_A X_B graph_union G_B
      right
      tauto
  distinct_edges := by
    intro i j h_eq
    fin_cases i <;> fin_cases j <;> {
      simp [Fin.castSucc, Fin.succ] at h_eq
      try rfl
      try omega
    }
}

/--
Theorem 1: Merging two holonomy-free systems can create holonomy.
We prove by construction that the union of X_A and X_B, which have no
cycles, creates a 4-cycle with a holonomy of 20.0.
-/
-- Helper lemmas to show each edge constraint equals 5.0
lemma edge_01_constraint :
    (union_config prob_create).constraints 0 1 (cycle_union.adjacent 0) = 5.0 := by
  unfold union_config prob_create X_A X_B merge_constraints
  simp only [G_A, G_B]
  rfl

lemma edge_12_constraint :
    (union_config prob_create).constraints 1 2 (cycle_union.adjacent 1) = 5.0 := by
  unfold union_config prob_create X_A X_B merge_constraints
  simp only [G_A, G_B]
  rfl

lemma edge_23_constraint :
    (union_config prob_create).constraints 2 3 (cycle_union.adjacent 2) = 5.0 := by
  unfold union_config prob_create X_A X_B merge_constraints
  simp only [G_A, G_B]
  rfl

lemma edge_30_constraint :
    (union_config prob_create).constraints 3 0 (cycle_union.adjacent 3) = 5.0 := by
  unfold union_config prob_create X_A X_B merge_constraints
  simp only [G_A, G_B]
  rfl

theorem negotiation_creates_holonomy :
    cycle_holonomy (union_config prob_create) cycle_union = 20.0 := by
  -- Expand the holonomy sum
  unfold cycle_holonomy
  rw [Fin.sum_univ_four]
  -- Simplify the cycle_union.nodes applications
  show (union_config prob_create).constraints
    (cycle_union.nodes 0) (cycle_union.nodes 1) (cycle_union.adjacent 0) +
    (union_config prob_create).constraints
    (cycle_union.nodes 1) (cycle_union.nodes 2) (cycle_union.adjacent 1) +
    (union_config prob_create).constraints
    (cycle_union.nodes 2) (cycle_union.nodes 3) (cycle_union.adjacent 2) +
    (union_config prob_create).constraints
    (cycle_union.nodes 3) (cycle_union.nodes 4) (cycle_union.adjacent 3) = 20.0
  -- cycle_union.nodes i = i for i < 4, and nodes 4 = 0
  simp only [cycle_union]
  -- Now we have constraints on (0,1), (1,2), (2,3), (3,0)
  rw [edge_01_constraint, edge_12_constraint, edge_23_constraint, edge_30_constraint]
  norm_num

/--
Corollary: The merged system has a provably non-zero minimum cost.
This connects the negotiation result back to the main holonomy theorem.
-/
theorem negotiation_creates_cost :
    0 < V_int (union_config prob_create) := by
  -- We need to prove K ≠ 0
  have h_K_ne_zero : cycle_holonomy (union_config prob_create) cycle_union ≠ 0 := by
    rw [negotiation_creates_holonomy]
    norm_num
  -- We need to prove k ≥ 3
  have h_k : 3 ≤ 4 := by norm_num
  -- Apply the main theorem from the other file
  exact cycle_creates_holonomy (union_config prob_create) cycle_union h_k h_K_ne_zero

/-! ## Theorem 2: Negotiation Can Resolve Holonomy -/

/-- Graph for X_C: a full triangle on 3 nodes -/
def G_C : SimpleGraph (Fin 3) where
  Adj i j := i ≠ j
  symm _ _ h := Ne.symm h
  loopless _ h := h rfl

instance : DecidableRel G_C.Adj := fun i j => by
  unfold G_C
  infer_instance

/-- Graph for X_D: a single edge (0, 1) -/
def G_D : SimpleGraph (Fin 3) where
  Adj i j := (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)
  symm _ _ h := by cases h <;> tauto
  loopless i h := by cases h <;> omega

instance : DecidableRel G_D.Adj := fun i j => by
  unfold G_D
  infer_instance

/-- Configuration X_C: a frustrated triangle with constraints 10.0 each -/
def X_C : ConfigSpace 3 := {
  graph := G_C
  adj_decidable := inferInstance
  node_phases := fun _ => 0
  constraints := fun _ _ _ => 10.0
}

/-- Configuration X_D: a counter-perspective on edge (0, 1) with constraint -10.0 -/
def X_D : ConfigSpace 3 := {
  graph := G_D
  adj_decidable := inferInstance
  node_phases := fun _ => 0
  constraints := fun _ _ _ => -10.0
}

/-- Dummy task for negotiation -/
def task_3 : ExternalTask 3 := {
  measure_violation := fun _ => 0
  violation_nonneg := fun _ => le_refl 0
}

/-- The negotiation problem for resolution -/
def prob_resolve : NegotiationProblem 3 := {
  X_A := X_C
  X_B := X_D
  task := task_3
  lam := 1.0
  h_lam_pos := by norm_num
}

/-- The 3-cycle in X_C: 0 → 1 → 2 → 0 -/
def cycle_C : Cycle 3 X_C.graph 3 := {
  nodes := fun i =>
    match i with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => 2
    | ⟨3, _⟩ => 0
    | ⟨n+4, h⟩ => absurd h (by omega)
  closes := by rfl
  adjacent := by
    intro i
    fin_cases i
    · -- 0 → 1
      unfold X_C G_C
      simp
    · -- 1 → 2
      unfold X_C G_C
      simp
    · -- 2 → 0
      unfold X_C G_C
      simp
  distinct_edges := by
    intro i j h_eq
    fin_cases i <;> fin_cases j <;> {
      simp [Fin.castSucc, Fin.succ] at h_eq
      try rfl
      try omega
    }
}

/-- The 3-cycle in the union graph: 0 → 1 → 2 → 0 -/
def cycle_resolve : Cycle 3 (union_config prob_resolve).graph 3 := {
  nodes := fun i =>
    match i with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => 2
    | ⟨3, _⟩ => 0
    | ⟨n+4, h⟩ => absurd h (by omega)
  closes := by rfl
  adjacent := by
    intro i
    fin_cases i
    · -- 0 → 1
      unfold union_config prob_resolve X_C graph_union G_C
      left
      simp
    · -- 1 → 2
      unfold union_config prob_resolve X_C graph_union G_C
      left
      simp
    · -- 2 → 0
      unfold union_config prob_resolve X_C graph_union G_C
      left
      simp
  distinct_edges := by
    intro i j h_eq
    fin_cases i <;> fin_cases j <;> {
      simp [Fin.castSucc, Fin.succ] at h_eq
      try rfl
      try omega
    }
}

/-- Original holonomy in X_C is 30.0 (three edges with constraint 10.0 each) -/
theorem original_holonomy :
    cycle_holonomy X_C cycle_C = 30.0 := by
  unfold cycle_holonomy X_C
  rw [Fin.sum_univ_three]
  norm_num

-- Helper lemmas for merged constraints
lemma resolve_edge_01_constraint :
    (union_config prob_resolve).constraints 0 1 (cycle_resolve.adjacent 0) = 0.0 := by
  unfold union_config prob_resolve X_C X_D merge_constraints
  simp only [G_C, G_D]
  -- Both graphs have edge (0,1), so we average: (10.0 + (-10.0))/2 = 0.0
  norm_num

lemma resolve_edge_12_constraint :
    (union_config prob_resolve).constraints 1 2 (cycle_resolve.adjacent 1) = 10.0 := by
  unfold union_config prob_resolve X_C X_D merge_constraints
  simp only [G_C, G_D]
  -- Only G_C has edge (1,2), so constraint is 10.0
  rfl

lemma resolve_edge_20_constraint :
    (union_config prob_resolve).constraints 2 0 (cycle_resolve.adjacent 2) = 10.0 := by
  unfold union_config prob_resolve X_C X_D merge_constraints
  simp only [G_C, G_D]
  -- Only G_C has edge (2,0), so constraint is 10.0
  rfl

/--
Theorem 2: Merging a frustrated system with a counter-perspective reduces holonomy.
The union has lower holonomy (20.0) than the original frustrated system (30.0).
-/
theorem negotiation_resolves_holonomy :
    cycle_holonomy (union_config prob_resolve) cycle_resolve = 20.0 := by
  unfold cycle_holonomy
  rw [Fin.sum_univ_three]
  -- Simplify cycle_resolve.nodes to actual values
  show (union_config prob_resolve).constraints
    (cycle_resolve.nodes 0) (cycle_resolve.nodes 1) (cycle_resolve.adjacent 0) +
    (union_config prob_resolve).constraints
    (cycle_resolve.nodes 1) (cycle_resolve.nodes 2) (cycle_resolve.adjacent 1) +
    (union_config prob_resolve).constraints
    (cycle_resolve.nodes 2) (cycle_resolve.nodes 3) (cycle_resolve.adjacent 2) = 20.0
  simp only [cycle_resolve]
  -- Now nodes simplify to 0,1,2,0
  rw [resolve_edge_01_constraint, resolve_edge_12_constraint, resolve_edge_20_constraint]
  norm_num

/--
Corollary: Negotiation reduces holonomy from 30.0 to 20.0
-/
theorem negotiation_reduces_holonomy_value :
    cycle_holonomy (union_config prob_resolve) cycle_resolve < cycle_holonomy X_C cycle_C := by
  rw [negotiation_resolves_holonomy, original_holonomy]
  norm_num

end GaugeNegotiation
