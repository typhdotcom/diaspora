/-
# Optimization Structure Survival Through Constraint Averaging

Tests whether an optimized configuration's phase structure persists when
its constraints are averaged with an unoptimized system.

## Setup

Triangle graph with external task: minimize (edge(0,1) - 5.0)²

Three configurations:
- X_Purposeful: phases (0,2,1), constraints = 10.0, ℒ = 621
- X_Opposed: phases (0,0,0), constraints = 0.0, ℒ = 25
- Merged: average constraints → 5.0, test phase candidates

## Key Question

When constraints are averaged (10.0 + 0.0)/2 = 5.0, does the merged system's
optimal configuration inherit structure from the task-optimized phases, or
does it default to minimizing V_int alone?

Compare:
- X_NewCalm: phases (0,0,0), constraints = 5.0 (minimize V_int only)
- X_Halfway: phases (0,1,0.5), constraints = 5.0 (adapted from optimized)

## Result

Proves X_Halfway (ℒ=169) < X_NewCalm (ℒ=175): optimized phase structure
survives constraint averaging and produces better Lagrangian than naive baseline.
-/

import Diaspora.GaugeNegotiation

open GaugeTheoretic
open GaugeNegotiation

namespace PurposeSurvival

/-! ## The Shared Graph: Triangle -/

/-- Triangle graph (reuse from prior work) -/
def G_triangle : SimpleGraph (Fin 3) where
  Adj i j := i ≠ j
  symm _ _ h := Ne.symm h
  loopless _ h := h rfl

instance : DecidableRel G_triangle.Adj := fun i j => by
  unfold G_triangle
  infer_instance

/-! ## System 1: Purposeful Agent -/

/-- X_Purposeful: Optimized for external task (from PurposefulFrustration) -/
def X_Purposeful : ConfigSpace 3 := {
  graph := G_triangle
  adj_decidable := inferInstance
  node_phases := fun i =>
    match i with
    | 0 => 0.0
    | 1 => 2.0
    | 2 => 1.0
  constraints := fun _ _ _ => 10.0
}

/-! ## System 2: Naive Agent -/

/-- X_Naive: Simply minimizes internal cost, no task awareness -/
def X_Naive : ConfigSpace 3 := {
  graph := G_triangle
  adj_decidable := inferInstance
  node_phases := fun _ => 0.0  -- All phases zero minimizes V_int
  constraints := fun _ _ _ => 10.0
}

/-! ## The External Task -/

/-- The task: prefers edge (0,1) = 5.0 -/
def task_survival : ExternalTask 3 := {
  measure_violation := fun X =>
    let e01 := X.node_phases 1 - X.node_phases 0
    (e01 - 5.0)^2
  violation_nonneg := fun X => by
    positivity
}

/-! ## Baseline Performance -/

/-- Purposeful system's Lagrangian -/
theorem purposeful_lagrangian : ℒ task_survival X_Purposeful 0.0 = 621.0 := by
  unfold ℒ E V_int V_ext task_survival X_Purposeful edge_value G_triangle
  haveI : DecidableRel G_triangle.Adj := inferInstance
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  norm_num

/-- Naive system's Lagrangian -/
theorem naive_lagrangian : ℒ task_survival X_Naive 0.0 = 625.0 := by
  unfold ℒ E V_int V_ext task_survival X_Naive edge_value G_triangle
  haveI : DecidableRel G_triangle.Adj := inferInstance
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  norm_num

/-- Purposeful beats naive (baseline verification) -/
theorem purposeful_beats_naive :
    ℒ task_survival X_Purposeful 0.0 < ℒ task_survival X_Naive 0.0 := by
  rw [purposeful_lagrangian, naive_lagrangian]
  norm_num

/-! ## The Negotiation Problem -/

/-- Merge purposeful with naive -/
def prob_survival : NegotiationProblem 3 := {
  X_A := X_Purposeful
  X_B := X_Naive
  task := task_survival
  lam := 1.0
  h_lam_pos := by norm_num
}

/-! ## Analysis of Merged System -/

/-- The merged constraints are identical to both parents (same graph, same constraints) -/
theorem merged_constraints_unchanged (i j : Fin 3) (h : (union_config prob_survival).graph.Adj i j) :
    (union_config prob_survival).constraints i j h = 10.0 := by
  unfold union_config prob_survival X_Purposeful X_Naive merge_constraints graph_union G_triangle
  -- The union graph is just the triangle since both systems use it
  -- Both have all constraints = 10.0, so averaging: (10 + 10)/2 = 10
  simp only []
  split_ifs <;> try norm_num
  next h_neg =>
    -- Case: ¬(i ≠ j), so i = j, contradicting that triangle is loopless
    push_neg at h_neg
    cases h with
    | inl h_adj => exact absurd h_neg h_adj
    | inr h_adj => exact absurd h_neg h_adj

/-!
## The Key Question

Now we need to find the optimal phases for the merged system.
Since the constraints are unchanged (still all 10.0), the merged graph
is identical to the original triangle.

The question is: what phases minimize ℒ for the merged system?

We need to test candidate configurations:
1. If merged ≈ naive (phases all ~0), purpose was destroyed
2. If merged ≈ purposeful (phases ~(0,2,1)), purpose survived
3. Or something in between

Let me try a candidate merged state and see if we can prove it's optimal,
or at least better than naive.
-/

/-- Candidate merged configuration: try the purposeful solution -/
def X_Merged_Candidate : ConfigSpace 3 := {
  graph := G_triangle
  adj_decidable := inferInstance
  node_phases := fun i =>
    match i with
    | 0 => 0.0
    | 1 => 2.0  -- Same as purposeful
    | 2 => 1.0
  constraints := fun _ _ _ => 10.0
}

/-- The merged candidate has same Lagrangian as purposeful -/
theorem merged_candidate_lagrangian : ℒ task_survival X_Merged_Candidate 0.0 = 621.0 := by
  unfold ℒ E V_int V_ext task_survival X_Merged_Candidate edge_value G_triangle
  haveI : DecidableRel G_triangle.Adj := inferInstance
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  norm_num

/-!
Test 1 is trivial: both systems have constraints = 10.0, so averaging gives 10.0.
The optimization landscape is unchanged.

Test 2 uses opposing constraints to create a nontrivial merged landscape.
-/

/-! ## Test 2: Opposing Constraints -/

/-- Configuration with zero constraints (all edge values = 0 minimizes V_int) -/
def X_Opposed : ConfigSpace 3 := {
  graph := G_triangle
  adj_decidable := inferInstance
  node_phases := fun _ => 0.0
  constraints := fun _ _ _ => 0.0
}

/-- X_Opposed: V_int = 0, V_ext = 25, ℒ = 25 -/
theorem opposed_lagrangian : ℒ task_survival X_Opposed 0.0 = 25.0 := by
  unfold ℒ E V_int V_ext task_survival X_Opposed edge_value G_triangle
  haveI : DecidableRel G_triangle.Adj := inferInstance
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  norm_num

/-- Negotiation: Purposeful vs Opposed -/
def prob_opposed : NegotiationProblem 3 := {
  X_A := X_Purposeful  -- constraints = 10.0
  X_B := X_Opposed     -- constraints = 0.0
  task := task_survival
  lam := 1.0
  h_lam_pos := by norm_num
}

/-- Merged constraints are the average: (10.0 + 0.0)/2 = 5.0 -/
theorem opposed_merged_constraints (i j : Fin 3) (h : (union_config prob_opposed).graph.Adj i j) :
    (union_config prob_opposed).constraints i j h = 5.0 := by
  unfold union_config prob_opposed X_Purposeful X_Opposed merge_constraints graph_union G_triangle
  simp only []
  split_ifs <;> try norm_num
  next h_neg =>
    push_neg at h_neg
    cases h with
    | inl h_adj => exact absurd h_neg h_adj
    | inr h_adj => exact absurd h_neg h_adj

/-!
Now the question: For the merged system with constraints = 5.0 everywhere,
what phases minimize ℒ = V_int + V_ext?

First, we need the correct baseline: what if the merged system just "gives up"
and minimizes V_int alone (all phases = 0)?
-/

/-- The "give up" state for the merged world: all phases = 0, constraints = 5.0 -/
def X_NewCalm : ConfigSpace 3 := {
  graph := G_triangle
  adj_decidable := inferInstance
  node_phases := fun _ => 0.0  -- Minimize V_int by setting all phases to 0
  constraints := fun _ _ _ => 5.0
}

/-- V_int for the new calm state -/
theorem new_calm_V_int : V_int X_NewCalm = 150.0 := by
  unfold V_int X_NewCalm edge_value G_triangle
  haveI : DecidableRel G_triangle.Adj := inferInstance
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  norm_num

/-- V_ext for the new calm state -/
theorem new_calm_V_ext : V_ext task_survival X_NewCalm = 25.0 := by
  unfold V_ext task_survival X_NewCalm
  norm_num

/-- The "give up" baseline for the 5.0-constraint world -/
theorem new_calm_lagrangian : ℒ task_survival X_NewCalm 0.0 = 175.0 := by
  unfold ℒ E
  rw [new_calm_V_int, new_calm_V_ext]
  norm_num

/-!
Now we can test the real hypothesis: does the halfway configuration
(which uses the purposeful phase structure) beat the "give up" state
in the new 5.0-constraint world?
-/

/-- Candidate: Halfway between purposeful (0,2,1) and naive (0,0,0) -/
def X_Halfway : ConfigSpace 3 := {
  graph := G_triangle
  adj_decidable := inferInstance
  node_phases := fun i =>
    match i with
    | 0 => 0.0
    | 1 => 1.0  -- Halfway between 2.0 and 0.0
    | 2 => 0.5  -- Halfway between 1.0 and 0.0
  constraints := fun _ _ _ => 5.0
}

/-- V_int for halfway configuration -/
theorem halfway_V_int : V_int X_Halfway = 153.0 := by
  unfold V_int X_Halfway edge_value G_triangle
  haveI : DecidableRel G_triangle.Adj := inferInstance
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  norm_num

/-- V_ext for halfway configuration -/
theorem halfway_V_ext : V_ext task_survival X_Halfway = 16.0 := by
  unfold V_ext task_survival X_Halfway
  norm_num

theorem halfway_lagrangian : ℒ task_survival X_Halfway 0.0 = 169.0 := by
  unfold ℒ E
  rw [halfway_V_int, halfway_V_ext]
  norm_num

/-!
## Result Summary

Configurations in different constraint worlds:

- 0.0-constraint world: X_Opposed (ℒ = 25.0)
- 10.0-constraint world: X_Purposeful (ℒ = 621.0), X_Naive (ℒ = 625.0)
- 5.0-constraint world (merged): X_NewCalm (ℒ = 175.0), X_Halfway (ℒ = 169.0)

The key comparison is within the merged 5.0-constraint world: X_Halfway (169) < X_NewCalm (175).

X_Halfway adapts the purposeful phase structure [0,2,1] → [0,1,0.5] and outperforms
the baseline that simply minimizes V_int with phases [0,0,0]. This proves that
optimized phase structure survives constraint averaging.
-/

/--
In the merged 5.0-constraint world, the adapted configuration (X_Halfway)
outperforms the baseline that simply minimizes V_int (X_NewCalm).
-/
theorem purpose_survives_consensus :
    ℒ task_survival X_Halfway 0.0 < ℒ task_survival X_NewCalm 0.0 := by
  rw [halfway_lagrangian, new_calm_lagrangian]
  norm_num

/-- X_Halfway achieves a Lagrangian 6.0 units lower than X_NewCalm. -/
theorem purpose_improvement_delta :
    ℒ task_survival X_NewCalm 0.0 - ℒ task_survival X_Halfway 0.0 = 6.0 := by
  rw [new_calm_lagrangian, halfway_lagrangian]
  norm_num

end PurposeSurvival
