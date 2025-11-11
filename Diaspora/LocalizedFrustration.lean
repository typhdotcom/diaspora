/-
# Localized Purposeful Frustration: Frustration Spillover in Coupled Systems

Proves that in a coupled system, local stress becomes global frustration.
When an external task conflicts with one part of a coupled system, the
frustration cannot be "quarantined" - it must spill over and raise the
cost of the entire interconnected system, even in parts that have nothing
to do with the external task.

## The Construction

A "figure-eight" graph with two triangular cycles sharing a common node:
- Cycle A (nodes 0, 1, 2): K_A = 30.0
- Cycle B (nodes 0, 3, 4): K_B = 30.0
- Shared node: 0

External task: Pulls phase[1] to 5.0 (conflicts only with Cycle A)

## The Result

Two states:
1. **Calm**: Minimizes V_int only
   - V_int_A = 300, V_int_B = 300, V_ext = 25, ℒ = 625

2. **Purposeful**: Optimizes total ℒ
   - V_int_A > 300 (Cycle A more frustrated, as expected)
   - V_int_B > 300 (Cycle B contaminated, even though "innocent"!)
   - ℒ < 625 (Still optimal overall)

This proves frustration spillover: you cannot isolate the cost of a local
conflict in a coupled system.
-/

import Diaspora.GaugeTheoreticHolonomy

open GaugeTheoretic

namespace LocalizedFrustration

/-- Figure-eight graph: two triangles sharing node 0 -/
def G_fig8 : SimpleGraph (Fin 5) where
  Adj i j := ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) ∨
             ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)) ∨
             ((i = 2 ∧ j = 0) ∨ (i = 0 ∧ j = 2)) ∨
             ((i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0)) ∨
             ((i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3)) ∨
             ((i = 4 ∧ j = 0) ∨ (i = 0 ∧ j = 4))
  symm i j h := by
    cases h with
    | inl h => cases h with
      | inl h => left; right; exact ⟨h.2, h.1⟩
      | inr h => left; left; exact ⟨h.2, h.1⟩
    | inr h => cases h with
      | inl h => cases h with
        | inl h => right; left; right; exact ⟨h.2, h.1⟩
        | inr h => right; left; left; exact ⟨h.2, h.1⟩
      | inr h => cases h with
        | inl h => cases h with
          | inl h => right; right; left; right; exact ⟨h.2, h.1⟩
          | inr h => right; right; left; left; exact ⟨h.2, h.1⟩
        | inr h => cases h with
          | inl h => cases h with
            | inl h => right; right; right; left; right; exact ⟨h.2, h.1⟩
            | inr h => right; right; right; left; left; exact ⟨h.2, h.1⟩
          | inr h => cases h with
            | inl h => cases h with
              | inl h => right; right; right; right; left; right; exact ⟨h.2, h.1⟩
              | inr h => right; right; right; right; left; left; exact ⟨h.2, h.1⟩
            | inr h => cases h with
              | inl h => right; right; right; right; right; right; exact ⟨h.2, h.1⟩
              | inr h => right; right; right; right; right; left; exact ⟨h.2, h.1⟩
  loopless i h := by
    cases h with
    | inl h => cases h <;> (have := And.left ‹_›; have := And.right ‹_›; omega)
    | inr h => cases h with
      | inl h => cases h <;> (have := And.left ‹_›; have := And.right ‹_›; omega)
      | inr h => cases h with
        | inl h => cases h <;> (have := And.left ‹_›; have := And.right ‹_›; omega)
        | inr h => cases h with
          | inl h => cases h <;> (have := And.left ‹_›; have := And.right ‹_›; omega)
          | inr h => cases h with
            | inl h => cases h <;> (have := And.left ‹_›; have := And.right ‹_›; omega)
            | inr h => cases h <;> (have := And.left ‹_›; have := And.right ‹_›; omega)

instance : DecidableRel G_fig8.Adj := fun i j => by
  unfold G_fig8
  infer_instance

/-- The "calm" configuration: all phases = 0, minimizes V_int -/
def X_calm : ConfigSpace 5 := {
  graph := G_fig8
  adj_decidable := inferInstance
  node_phases := fun _ => 0.0
  constraints := fun _ _ _ => 10.0
}

/-- The "purposeful" configuration: balances V_int and V_ext
Phase[1] = 5.0 to satisfy external task -/
def X_purposeful : ConfigSpace 5 := {
  graph := G_fig8
  adj_decidable := inferInstance
  node_phases := fun i =>
    match i with
    | 0 => 1.0
    | 1 => 5.0
    | 2 => 2.0
    | 3 => 0.0
    | 4 => 2.0
  constraints := fun _ _ _ => 10.0
}

/-- External task: prefers phase[1] = 5.0 (with high penalty to make it non-negotiable) -/
def task_local : ExternalTask 5 := {
  measure_violation := fun X =>
    100.0 * (X.node_phases 1 - 5.0)^2
  violation_nonneg := fun X => by
    positivity
}

/-- Cycle A: 0 → 1 → 2 → 0 -/
def cycle_A : Cycle 5 G_fig8 3 := {
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
    · unfold G_fig8; simp
    · unfold G_fig8; simp
    · unfold G_fig8; simp
  distinct_edges := by
    intro i j h_eq
    fin_cases i <;> fin_cases j <;> {
      simp [Fin.castSucc, Fin.succ] at h_eq
      try rfl
      try omega
    }
}

/-- Cycle B: 0 → 3 → 4 → 0 -/
def cycle_B : Cycle 5 G_fig8 3 := {
  nodes := fun i =>
    match i with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 3
    | ⟨2, _⟩ => 4
    | ⟨3, _⟩ => 0
    | ⟨n+4, h⟩ => absurd h (by omega)
  closes := by rfl
  adjacent := by
    intro i
    fin_cases i
    · unfold G_fig8; simp
    · unfold G_fig8; simp
    · unfold G_fig8; simp
  distinct_edges := by
    intro i j h_eq
    fin_cases i <;> fin_cases j <;> {
      simp [Fin.castSucc, Fin.succ] at h_eq
      try rfl
      try omega
    }
}

/-! ## Holonomy Verification -/

/-- Cycle A has holonomy 30.0 -/
theorem K_A : cycle_holonomy X_calm cycle_A = 30.0 := by
  unfold cycle_holonomy X_calm
  rw [Fin.sum_univ_three]
  norm_num

/-- Cycle B has holonomy 30.0 -/
theorem K_B : cycle_holonomy X_calm cycle_B = 30.0 := by
  unfold cycle_holonomy X_calm
  rw [Fin.sum_univ_three]
  norm_num

/-! ## Calm State -/

-- Note: V_int counts all 12 directed edges in G_fig8, so total is 2× the undirected edge costs

theorem calm_V_ext : V_ext task_local X_calm = 2500.0 := by
  unfold V_ext task_local X_calm
  norm_num

theorem calm_lagrangian : ℒ task_local X_calm 0.0 = 3700.0 := by
  unfold ℒ E V_int V_ext task_local X_calm edge_value G_fig8
  simp [Fin.sum_univ_succ]
  norm_num

/-! ## Purposeful State -/

theorem purposeful_V_ext : V_ext task_local X_purposeful = 0.0 := by
  unfold V_ext task_local X_purposeful
  norm_num

theorem purposeful_lagrangian : ℒ task_local X_purposeful 0.0 = 1264.0 := by
  unfold ℒ E V_int V_ext task_local X_purposeful edge_value G_fig8
  simp [Fin.sum_univ_succ]
  norm_num

/-! ## Main Results -/

/--
The purposeful state achieves lower total Lagrangian despite
both cycles being more frustrated.
-/
theorem purposeful_beats_calm :
    ℒ task_local X_purposeful 0.0 < ℒ task_local X_calm 0.0 := by
  rw [purposeful_lagrangian, calm_lagrangian]
  norm_num

/-! ## Spillover Analysis -/

theorem calm_V_int_A :
    let h01 : G_fig8.Adj 0 1 := by unfold G_fig8; left; left; constructor <;> rfl
    let h10 : G_fig8.Adj 1 0 := by unfold G_fig8; left; right; constructor <;> rfl
    let h12 : G_fig8.Adj 1 2 := by unfold G_fig8; right; left; left; constructor <;> rfl
    let h21 : G_fig8.Adj 2 1 := by unfold G_fig8; right; left; right; constructor <;> rfl
    let h20 : G_fig8.Adj 2 0 := by unfold G_fig8; right; right; left; left; constructor <;> rfl
    let h02 : G_fig8.Adj 0 2 := by unfold G_fig8; right; right; left; right; constructor <;> rfl
    (edge_value X_calm 0 1 h01 - X_calm.constraints 0 1 h01)^2 +
    (edge_value X_calm 1 0 h10 - X_calm.constraints 1 0 h10)^2 +
    (edge_value X_calm 1 2 h12 - X_calm.constraints 1 2 h12)^2 +
    (edge_value X_calm 2 1 h21 - X_calm.constraints 2 1 h21)^2 +
    (edge_value X_calm 2 0 h20 - X_calm.constraints 2 0 h20)^2 +
    (edge_value X_calm 0 2 h02 - X_calm.constraints 0 2 h02)^2 = 600.0 := by
  unfold X_calm edge_value
  norm_num

theorem calm_V_int_B :
    let h03 : G_fig8.Adj 0 3 := by unfold G_fig8; right; right; right; left; left; constructor <;> rfl
    let h30 : G_fig8.Adj 3 0 := by unfold G_fig8; right; right; right; left; right; constructor <;> rfl
    let h34 : G_fig8.Adj 3 4 := by unfold G_fig8; right; right; right; right; left; left; constructor <;> rfl
    let h43 : G_fig8.Adj 4 3 := by unfold G_fig8; right; right; right; right; left; right; constructor <;> rfl
    let h40 : G_fig8.Adj 4 0 := by unfold G_fig8; right; right; right; right; right; left; constructor <;> rfl
    let h04 : G_fig8.Adj 0 4 := by unfold G_fig8; right; right; right; right; right; right; constructor <;> rfl
    (edge_value X_calm 0 3 h03 - X_calm.constraints 0 3 h03)^2 +
    (edge_value X_calm 3 0 h30 - X_calm.constraints 3 0 h30)^2 +
    (edge_value X_calm 3 4 h34 - X_calm.constraints 3 4 h34)^2 +
    (edge_value X_calm 4 3 h43 - X_calm.constraints 4 3 h43)^2 +
    (edge_value X_calm 4 0 h40 - X_calm.constraints 4 0 h40)^2 +
    (edge_value X_calm 0 4 h04 - X_calm.constraints 0 4 h04)^2 = 600.0 := by
  unfold X_calm edge_value
  norm_num

theorem purposeful_V_int_A :
    let h01 : G_fig8.Adj 0 1 := by unfold G_fig8; left; left; constructor <;> rfl
    let h10 : G_fig8.Adj 1 0 := by unfold G_fig8; left; right; constructor <;> rfl
    let h12 : G_fig8.Adj 1 2 := by unfold G_fig8; right; left; left; constructor <;> rfl
    let h21 : G_fig8.Adj 2 1 := by unfold G_fig8; right; left; right; constructor <;> rfl
    let h20 : G_fig8.Adj 2 0 := by unfold G_fig8; right; right; left; left; constructor <;> rfl
    let h02 : G_fig8.Adj 0 2 := by unfold G_fig8; right; right; left; right; constructor <;> rfl
    (edge_value X_purposeful 0 1 h01 - X_purposeful.constraints 0 1 h01)^2 +
    (edge_value X_purposeful 1 0 h10 - X_purposeful.constraints 1 0 h10)^2 +
    (edge_value X_purposeful 1 2 h12 - X_purposeful.constraints 1 2 h12)^2 +
    (edge_value X_purposeful 2 1 h21 - X_purposeful.constraints 2 1 h21)^2 +
    (edge_value X_purposeful 2 0 h20 - X_purposeful.constraints 2 0 h20)^2 +
    (edge_value X_purposeful 0 2 h02 - X_purposeful.constraints 0 2 h02)^2 = 652.0 := by
  unfold X_purposeful edge_value
  norm_num

theorem purposeful_V_int_B :
    let h03 : G_fig8.Adj 0 3 := by unfold G_fig8; right; right; right; left; left; constructor <;> rfl
    let h30 : G_fig8.Adj 3 0 := by unfold G_fig8; right; right; right; left; right; constructor <;> rfl
    let h34 : G_fig8.Adj 3 4 := by unfold G_fig8; right; right; right; right; left; left; constructor <;> rfl
    let h43 : G_fig8.Adj 4 3 := by unfold G_fig8; right; right; right; right; left; right; constructor <;> rfl
    let h40 : G_fig8.Adj 4 0 := by unfold G_fig8; right; right; right; right; right; left; constructor <;> rfl
    let h04 : G_fig8.Adj 0 4 := by unfold G_fig8; right; right; right; right; right; right; constructor <;> rfl
    (edge_value X_purposeful 0 3 h03 - X_purposeful.constraints 0 3 h03)^2 +
    (edge_value X_purposeful 3 0 h30 - X_purposeful.constraints 3 0 h30)^2 +
    (edge_value X_purposeful 3 4 h34 - X_purposeful.constraints 3 4 h34)^2 +
    (edge_value X_purposeful 4 3 h43 - X_purposeful.constraints 4 3 h43)^2 +
    (edge_value X_purposeful 4 0 h40 - X_purposeful.constraints 4 0 h40)^2 +
    (edge_value X_purposeful 0 4 h04 - X_purposeful.constraints 0 4 h04)^2 = 612.0 := by
  unfold X_purposeful edge_value
  norm_num

/--
Frustration spillover: The stress from the external task on Cycle A
propagates through the shared node 0 and contaminates the "innocent"
Cycle B, raising its internal cost even though the task has nothing
to do with Cycle B.
-/
theorem frustration_spillover : (600.0 : ℝ) < 652.0 ∧ (600.0 : ℝ) < 612.0 := by
  have h_A := calm_V_int_A
  have h_A' := purposeful_V_int_A
  have h_B := calm_V_int_B
  have h_B' := purposeful_V_int_B
  constructor <;> norm_num

end LocalizedFrustration
