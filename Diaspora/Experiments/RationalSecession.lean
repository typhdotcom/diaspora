/-
# Rational Secession: When Disconnection Becomes Optimal

Proves that there exists a tipping point λ* where it becomes rational to sever
a connection to an "innocent but contaminated" subsystem rather than continue
paying the cost of frustration spillover.

## Construction

Extends LocalizedFrustration setup:
- Figure-eight: Cycle A (0,1,2) and Cycle B (0,3,4) share node 0
- External task affects only Cycle A
- Spillover: Cycle B becomes frustrated despite being "innocent"

Three configurations:
1. **Coupled**: Full figure-eight (6 edges)
   - Both cycles frustrated via spillover

2. **Severed**: Delete edges (0,3) and (0,4), making two separate paths
   - Cycle A remains as path 0→1→2
   - Cycle B becomes path 3→4 (2 edges, no holonomy)
   - No more spillover to Cycle B

## Result

Proves ∃λ* such that:
- Below λ*: endure spillover, stay coupled (coordination worth the cost)
- Above λ*: sever connection (complexity cost exceeds spillover benefit)

This formalizes rational disconnection: divorce, forgetting, neural pruning, schism.
-/

import Diaspora.GaugeTheoreticHolonomy

open GaugeTheoretic

namespace Experiments.RationalSecession

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

/-- Severed graph: remove edges (0,3) and (0,4), leaving two separate paths -/
def G_severed : SimpleGraph (Fin 5) where
  Adj i j := ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) ∨
             ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)) ∨
             ((i = 2 ∧ j = 0) ∨ (i = 0 ∧ j = 2)) ∨
             ((i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3))
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
          | inl h => right; right; right; right; exact ⟨h.2, h.1⟩
          | inr h => right; right; right; left; exact ⟨h.2, h.1⟩
  loopless i h := by
    cases h with
    | inl h => cases h <;> (have := And.left ‹_›; have := And.right ‹_›; omega)
    | inr h => cases h with
      | inl h => cases h <;> (have := And.left ‹_›; have := And.right ‹_›; omega)
      | inr h => cases h with
        | inl h => cases h <;> (have := And.left ‹_›; have := And.right ‹_›; omega)
        | inr h => cases h <;> (have := And.left ‹_›; have := And.right ‹_›; omega)

instance : DecidableRel G_severed.Adj := fun i j => by
  unfold G_severed
  infer_instance

/-- External task: prefers phase[1] = 5.0 AND global coordination -/
def task_secession : ExternalTask 5 := {
  measure_violation := fun X =>
    100.0 * (X.node_phases 1 - 5.0)^2 +
    100.0 * ((X.node_phases 0 + X.node_phases 1 + X.node_phases 2 +
      X.node_phases 3 + X.node_phases 4) - 10.0)^2
  violation_nonneg := fun X => by
    positivity
}

/-! ## Coupled Configuration -/

def X_coupled : ConfigSpace 5 := {
  graph := G_fig8
  adj_decidable := inferInstance
  node_phases := fun i =>
    match i with
    | 0 => 1.0
    | 1 => 5.0
    | 2 => 2.0
    | 3 => 1.0
    | 4 => 2.0
  constraints := fun _ _ _ => 10.0
}

-- Manual adjacency proofs for coupled graph
lemma adj_c_01 : G_fig8.Adj 0 1 := by unfold G_fig8; left; left; constructor <;> rfl
lemma adj_c_10 : G_fig8.Adj 1 0 := by unfold G_fig8; left; right; constructor <;> rfl
lemma adj_c_12 : G_fig8.Adj 1 2 := by unfold G_fig8; right; left; left; constructor <;> rfl
lemma adj_c_21 : G_fig8.Adj 2 1 := by unfold G_fig8; right; left; right; constructor <;> rfl
lemma adj_c_20 : G_fig8.Adj 2 0 := by unfold G_fig8; right; right; left; left; constructor <;> rfl
lemma adj_c_02 : G_fig8.Adj 0 2 := by unfold G_fig8; right; right; left; right; constructor <;> rfl
lemma adj_c_03 : G_fig8.Adj 0 3 := by unfold G_fig8; right; right; right; left; left; constructor <;> rfl
lemma adj_c_30 : G_fig8.Adj 3 0 := by unfold G_fig8; right; right; right; left; right; constructor <;> rfl
lemma adj_c_34 : G_fig8.Adj 3 4 := by unfold G_fig8; right; right; right; right; left; left; constructor <;> rfl
lemma adj_c_43 : G_fig8.Adj 4 3 := by unfold G_fig8; right; right; right; right; left; right; constructor <;> rfl
lemma adj_c_40 : G_fig8.Adj 4 0 := by unfold G_fig8; right; right; right; right; right; left; constructor <;> rfl
lemma adj_c_04 : G_fig8.Adj 0 4 := by unfold G_fig8; right; right; right; right; right; right; constructor <;> rfl

theorem coupled_V_int : V_int X_coupled = 1302.0 := by
  unfold V_int X_coupled edge_value
  conv_lhs =>
    arg 1
    ext i
    arg 1
    ext j
    rw [Finset.sum_ite_irrel]
  rw [Fin.sum_univ_five, Fin.sum_univ_five, Fin.sum_univ_five, Fin.sum_univ_five, Fin.sum_univ_five, Fin.sum_univ_five]
  simp [adj_c_01, adj_c_10, adj_c_12, adj_c_21, adj_c_20, adj_c_02,
        adj_c_03, adj_c_30, adj_c_34, adj_c_43, adj_c_40, adj_c_04]
  norm_num

theorem coupled_V_ext : V_ext task_secession X_coupled = 100.0 := by
  unfold V_ext task_secession X_coupled
  norm_num

theorem coupled_E : E X_coupled = 6 := by
  unfold E X_coupled G_fig8
  rfl

/-! ## Severed Configuration -/

def X_severed : ConfigSpace 5 := {
  graph := G_severed
  adj_decidable := inferInstance
  node_phases := fun i =>
    match i with
    | 0 => 1.0
    | 1 => 5.0
    | 2 => 2.0
    | 3 => 0.0
    | 4 => 10.0
  constraints := fun _ _ _ => 10.0
}

-- Manual adjacency proofs for severed graph
lemma adj_s_01 : G_severed.Adj 0 1 := by unfold G_severed; left; left; constructor <;> rfl
lemma adj_s_10 : G_severed.Adj 1 0 := by unfold G_severed; left; right; constructor <;> rfl
lemma adj_s_12 : G_severed.Adj 1 2 := by unfold G_severed; right; left; left; constructor <;> rfl
lemma adj_s_21 : G_severed.Adj 2 1 := by unfold G_severed; right; left; right; constructor <;> rfl
lemma adj_s_20 : G_severed.Adj 2 0 := by unfold G_severed; right; right; left; left; constructor <;> rfl
lemma adj_s_02 : G_severed.Adj 0 2 := by unfold G_severed; right; right; left; right; constructor <;> rfl
lemma adj_s_34 : G_severed.Adj 3 4 := by unfold G_severed; right; right; right; left; constructor <;> rfl
lemma adj_s_43 : G_severed.Adj 4 3 := by unfold G_severed; right; right; right; right; constructor <;> rfl

theorem severed_V_int : V_int X_severed = 652.0 := by
  unfold V_int X_severed edge_value
  conv_lhs =>
    arg 1
    ext i
    arg 1
    ext j
    rw [Finset.sum_ite_irrel]
  rw [Fin.sum_univ_five, Fin.sum_univ_five, Fin.sum_univ_five, Fin.sum_univ_five, Fin.sum_univ_five, Fin.sum_univ_five]
  simp [adj_s_01, adj_s_10, adj_s_12, adj_s_21, adj_s_20, adj_s_02, adj_s_34, adj_s_43]
  norm_num

theorem severed_V_ext : V_ext task_secession X_severed = 6400.0 := by
  unfold V_ext task_secession X_severed
  norm_num

theorem severed_E : E X_severed = 4 := by
  unfold E X_severed G_severed
  rfl

/-! ## Main Results -/

theorem coupled_better_at_zero :
    ℒ task_secession X_coupled 0.0 < ℒ task_secession X_severed 0.0 := by
  unfold ℒ
  rw [coupled_V_int, coupled_V_ext, coupled_E, severed_V_int, severed_V_ext, severed_E]
  norm_num

theorem secession_tipping_point :
    ∃ (lam_star : ℝ), lam_star = 2825.0 ∧
    (∀ lam, lam < lam_star →
      ℒ task_secession X_coupled lam < ℒ task_secession X_severed lam) ∧
    (∀ lam, lam > lam_star →
      ℒ task_secession X_severed lam < ℒ task_secession X_coupled lam) := by
  use 2825.0
  constructor
  · rfl
  constructor
  · intro lam h_lt
    unfold ℒ
    rw [coupled_V_int, coupled_V_ext, coupled_E, severed_V_int, severed_V_ext, severed_E]
    simp
    linarith
  · intro lam h_gt
    unfold ℒ
    rw [coupled_V_int, coupled_V_ext, coupled_E, severed_V_int, severed_V_ext, severed_E]
    simp
    linarith

end Experiments.RationalSecession
