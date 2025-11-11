/-
# Purposeful Frustration: When Internal Cost Serves External Goals

Proves that a system can accept *higher* internal frustration (V_int)
to achieve better external task performance (V_ext), resulting in a lower
total Lagrangian ℒ = V_int + V_ext.

This formalizes "purposeful self-contradiction" - an agent may maintain
an internally inconsistent model if that inconsistency serves an external purpose.

## The Construction

Triangle with holonomy K = 30:
- Internal constraints: c(0,1) = c(1,2) = c(2,0) = 10.0
- External task: V_ext = (e_{01} - 5.0)² (competing constraint on same edge!)

Two states:
1. **Calm**: Minimizes V_int
   - Edge values: [0, 0, 0]
   - V_int = 600.0, V_ext = 25.0, ℒ = 625.0

2. **Purposeful**: Optimizes total ℒ
   - Edge values: [2, -1, -1]
   - V_int = 612.0 (higher!), V_ext = 9.0 (much lower), ℒ = 621.0 (better!)

Proven: ℒ_purposeful < ℒ_calm (621.0 < 625.0)

Note: V_int counts both (i,j) and (j,i) for undirected edges, so values are 2× compared to
the minimal K²/n bound which counts unordered edges only.
-/

import Diaspora.GaugeTheoreticHolonomy

open GaugeTheoretic

namespace PurposefulFrustration

/-- Triangle graph -/
def G_triangle : SimpleGraph (Fin 3) where
  Adj i j := i ≠ j
  symm _ _ h := Ne.symm h
  loopless _ h := h rfl

instance : DecidableRel G_triangle.Adj := fun i j => by
  unfold G_triangle
  infer_instance

/-- The "calm" configuration: minimizes V_int alone
All phases = 0, so all edge values = 0 -/
def X_calm : ConfigSpace 3 := {
  graph := G_triangle
  adj_decidable := inferInstance
  node_phases := fun _ => 0.0
  constraints := fun _ _ _ => 10.0
}

/-- The "purposeful" configuration: optimizes total Lagrangian
Phases chosen to balance V_int and V_ext -/
def X_purposeful : ConfigSpace 3 := {
  graph := G_triangle
  adj_decidable := inferInstance
  node_phases := fun i =>
    match i with
    | 0 => 0.0
    | 1 => 2.0
    | 2 => 1.0
  constraints := fun _ _ _ => 10.0
}

/-- External task: prefers edge (0,1) to have value 5.0
This conflicts with internal constraint of 10.0 -/
def task_conflict : ExternalTask 3 := {
  measure_violation := fun X =>
    -- Node phases determine edge value
    let e01 := X.node_phases 1 - X.node_phases 0
    (e01 - 5.0)^2
  violation_nonneg := fun X => by
    positivity
}

/-- The 3-cycle for holonomy computation -/
def cycle_triangle : Cycle 3 G_triangle 3 := {
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
    · unfold G_triangle; simp
    · unfold G_triangle; simp
    · unfold G_triangle; simp
  distinct_edges := by
    intro i j h_eq
    fin_cases i <;> fin_cases j <;> {
      simp [Fin.castSucc, Fin.succ] at h_eq
      try rfl
      try omega
    }
}

/-- Holonomy of the triangle is 30.0 -/
theorem triangle_holonomy :
    cycle_holonomy X_calm cycle_triangle = 30.0 := by
  unfold cycle_holonomy X_calm
  rw [Fin.sum_univ_three]
  norm_num

/-! ## Calm State: Minimizes V_int -/

/-- Edge values for calm state are all 0 -/
lemma calm_edge_01 (h : X_calm.graph.Adj 0 1) : edge_value X_calm 0 1 h = 0.0 := by
  unfold edge_value X_calm
  norm_num

lemma calm_edge_12 (h : X_calm.graph.Adj 1 2) : edge_value X_calm 1 2 h = 0.0 := by
  unfold edge_value X_calm
  norm_num

lemma calm_edge_20 (h : X_calm.graph.Adj 2 0) : edge_value X_calm 2 0 h = 0.0 := by
  unfold edge_value X_calm
  norm_num

/-- V_int for calm state is 600.0 (6 directed edges × 100.0 each) -/
theorem calm_V_int : V_int X_calm = 600.0 := by
  unfold V_int X_calm
  haveI : DecidableRel G_triangle.Adj := inferInstance
  -- Expand the double sum over Fin 3 × Fin 3
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  -- Simplify each of the 9 terms (6 with edges, 3 self-loops that contribute 0)
  simp only [G_triangle, edge_value]
  -- Simplify the if statements by deciding inequalities
  simp
  norm_num

/-- V_ext for calm state is 25.0 -/
theorem calm_V_ext : V_ext task_conflict X_calm = 25.0 := by
  unfold V_ext task_conflict X_calm
  simp
  norm_num

/-- Total Lagrangian for calm state is 625.0 -/
theorem calm_lagrangian : ℒ task_conflict X_calm 0.0 = 625.0 := by
  unfold ℒ E
  rw [calm_V_int, calm_V_ext]
  norm_num

/-! ## Purposeful State: Optimizes ℒ -/

/-- Edge values for purposeful state -/
lemma purposeful_edge_01 (h : X_purposeful.graph.Adj 0 1) : edge_value X_purposeful 0 1 h = 2.0 := by
  unfold edge_value X_purposeful
  norm_num

lemma purposeful_edge_12 (h : X_purposeful.graph.Adj 1 2) : edge_value X_purposeful 1 2 h = -1.0 := by
  unfold edge_value X_purposeful
  norm_num

lemma purposeful_edge_20 (h : X_purposeful.graph.Adj 2 0) : edge_value X_purposeful 2 0 h = -1.0 := by
  unfold edge_value X_purposeful
  norm_num

/-- The purposeful edge values satisfy the cycle constraint -/
theorem purposeful_satisfies_cycle
    (h01 : X_purposeful.graph.Adj 0 1)
    (h12 : X_purposeful.graph.Adj 1 2)
    (h20 : X_purposeful.graph.Adj 2 0) :
    edge_value X_purposeful 0 1 h01 + edge_value X_purposeful 1 2 h12 + edge_value X_purposeful 2 0 h20 = 0.0 := by
  rw [purposeful_edge_01, purposeful_edge_12, purposeful_edge_20]
  norm_num

/-- V_int for purposeful state is 612.0 (higher than calm!) -/
theorem purposeful_V_int : V_int X_purposeful = 612.0 := by
  unfold V_int X_purposeful
  haveI : DecidableRel G_triangle.Adj := inferInstance
  -- Expand the double sum over Fin 3 × Fin 3
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  -- Simplify each term
  simp only [G_triangle, edge_value]
  -- Calculate each edge contribution and simplify inequalities
  simp
  norm_num

/-- V_ext for purposeful state is 9.0 (much lower than calm!) -/
theorem purposeful_V_ext : V_ext task_conflict X_purposeful = 9.0 := by
  unfold V_ext task_conflict X_purposeful
  simp
  norm_num

/-- Total Lagrangian for purposeful state is 621.0 -/
theorem purposeful_lagrangian : ℒ task_conflict X_purposeful 0.0 = 621.0 := by
  unfold ℒ E
  rw [purposeful_V_int, purposeful_V_ext]
  norm_num

/-! ## Main Result: Purposeful Self-Contradiction -/

/--
The purposeful state has a better (lower) total Lagrangian than the calm state,
despite having higher internal frustration.

This proves that a system may "choose" internal incoherence (higher V_int)
if it helps achieve an external goal (lower V_ext), resulting in better
overall performance (lower ℒ).
-/
theorem purposeful_beats_calm :
    ℒ task_conflict X_purposeful 0.0 < ℒ task_conflict X_calm 0.0 := by
  rw [purposeful_lagrangian, calm_lagrangian]
  norm_num

/--
Corollary: The purposeful state accepts higher internal cost
-/
theorem purposeful_more_frustrated :
    V_int X_calm < V_int X_purposeful := by
  rw [calm_V_int, purposeful_V_int]
  norm_num

end PurposefulFrustration
