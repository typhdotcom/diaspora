/-
# Holonomy Elimination via Constraint Cancellation

Proves that merge_constraints can completely eliminate holonomy when merging
systems with opposing frustration.

## Construction

Two 3-node triangles with equal and opposite holonomy:
- X_Frustrated: All constraints = +10.0, holonomy K = +30.0
- X_Opposed: All constraints = -10.0, holonomy K = -30.0

Merged system:
- All constraints become (10 + (-10))/2 = 0.0
- Final holonomy K_final = 0.0

## Result

Proves merge_constraints can completely eliminate holonomy through cancellation,
and that the merged system has lower cost bound than either parent system.
-/

import Diaspora.GaugeNegotiation

open GaugeTheoretic
open GaugeNegotiation

namespace IteratedNegotiation

/-! ## System 1: Frustrated Triangle -/

/-- Triangle graph (reuse from GaugeNegotiation) -/
def G_triangle : SimpleGraph (Fin 3) where
  Adj i j := i ≠ j
  symm _ _ h := Ne.symm h
  loopless _ h := h rfl

instance : DecidableRel G_triangle.Adj := fun i j => by
  unfold G_triangle
  infer_instance

/-- X_Frustrated: Triangle with all positive constraints -/
def X_Frustrated : ConfigSpace 3 := {
  graph := G_triangle
  adj_decidable := inferInstance
  node_phases := fun _ => 0
  constraints := fun _ _ _ => 10.0
}

/-! ## System 2: Opposingly Frustrated Triangle -/

/-- X_Opposed: Triangle with all negative constraints -/
def X_Opposed : ConfigSpace 3 := {
  graph := G_triangle
  adj_decidable := inferInstance
  node_phases := fun _ => 0
  constraints := fun _ _ _ => -10.0
}

/-! ## The Damping Problem -/

/-- Dummy task for damping negotiation -/
def task_damp : ExternalTask 3 := {
  measure_violation := fun _ => 0
  violation_nonneg := fun _ => le_refl 0
}

/-- Negotiation problem: merge frustrated with opposed -/
def prob_damp : NegotiationProblem 3 := {
  X_A := X_Frustrated
  X_B := X_Opposed
  task := task_damp
  lam := 1.0
  h_lam_pos := by norm_num
}

/-! ## The 3-cycle -/

/-- The 3-cycle in the union graph: 0 → 1 → 2 → 0 -/
def cycle_damp : Cycle 3 (union_config prob_damp).graph 3 := {
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
    · unfold union_config prob_damp X_Frustrated X_Opposed graph_union G_triangle
      left
      simp
    · unfold union_config prob_damp X_Frustrated X_Opposed graph_union G_triangle
      left
      simp
    · unfold union_config prob_damp X_Frustrated X_Opposed graph_union G_triangle
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

/-- The 3-cycle for the original frustrated system -/
def cycle_3_frustrated : Cycle 3 X_Frustrated.graph 3 := {
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
    · unfold X_Frustrated G_triangle; simp
    · unfold X_Frustrated G_triangle; simp
    · unfold X_Frustrated G_triangle; simp
  distinct_edges := by
    intro i j h_eq
    fin_cases i <;> fin_cases j <;> {
      simp [Fin.castSucc, Fin.succ] at h_eq
      try rfl
      try omega
    }
}

/-- The 3-cycle for the opposed system -/
def cycle_3_opposed : Cycle 3 X_Opposed.graph 3 := {
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
    · unfold X_Opposed G_triangle; simp
    · unfold X_Opposed G_triangle; simp
    · unfold X_Opposed G_triangle; simp
  distinct_edges := by
    intro i j h_eq
    fin_cases i <;> fin_cases j <;> {
      simp [Fin.castSucc, Fin.succ] at h_eq
      try rfl
      try omega
    }
}

/-! ## Holonomies of Input Systems -/

/-- X_Frustrated has holonomy +30.0 -/
theorem K_frustrated : cycle_holonomy X_Frustrated cycle_3_frustrated = 30.0 := by
  unfold cycle_holonomy X_Frustrated
  rw [Fin.sum_univ_three]
  norm_num

/-- X_Opposed has holonomy -30.0 -/
theorem K_opposed : cycle_holonomy X_Opposed cycle_3_opposed = -30.0 := by
  unfold cycle_holonomy X_Opposed
  rw [Fin.sum_univ_three]
  norm_num

/-! ## Main Results -/

-- No helper lemmas needed - we'll compute directly

/--
Merging two systems with equal and opposite holonomy results in
zero holonomy in the merged system.
-/
theorem negotiation_damps_holonomy :
    cycle_holonomy (union_config prob_damp) cycle_damp = 0.0 := by
  unfold cycle_holonomy union_config prob_damp X_Frustrated X_Opposed merge_constraints
  rw [Fin.sum_univ_three]
  simp only [G_triangle, cycle_damp]
  simp
  norm_num

/--
The merged system's cost bound (K² / n) is lower than either parent system's.
-/
theorem consensus_reduces_cost_bound :
    (cycle_holonomy (union_config prob_damp) cycle_damp)^2 / 3 <
    (cycle_holonomy X_Frustrated cycle_3_frustrated)^2 / 3 ∧
    (cycle_holonomy (union_config prob_damp) cycle_damp)^2 / 3 <
    (cycle_holonomy X_Opposed cycle_3_opposed)^2 / 3 := by
  rw [negotiation_damps_holonomy, K_frustrated, K_opposed]
  norm_num

/-- The merged system has zero holonomy. -/
theorem consensus_is_holonomy_free :
    cycle_holonomy (union_config prob_damp) cycle_damp = 0.0 := by
  exact negotiation_damps_holonomy

end IteratedNegotiation
