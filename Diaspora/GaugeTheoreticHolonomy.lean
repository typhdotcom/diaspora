/-
# Gauge-Theoretic Proof of Holonomy

Proves that cycles create holonomy via gauge structure: edge values derived from node phases.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Basic
import Diaspora.HolonomyLagrangeProof

open BigOperators HolonomyProof

namespace GaugeTheoretic

/-! ## Gauge-Theoretic ConfigSpace -/

/-- Configuration space with node phases (gauge-theoretic formulation) -/
structure ConfigSpace (n : ℕ) where
  /-- The underlying graph -/
  graph : SimpleGraph (Fin n)
  /-- Adjacency is decidable -/
  adj_decidable : DecidableRel graph.Adj
  /-- Node phases (the gauge degrees of freedom) -/
  node_phases : Fin n → ℝ
  /-- Constraint value for each edge (from external tasks) -/
  constraints : ∀ (i j : Fin n), graph.Adj i j → ℝ

/-! ## Edge Values Derived from Node Phases -/

/-- Edge value is the phase difference (automatic from gauge structure) -/
def edge_value {n : ℕ} (X : ConfigSpace n) (i j : Fin n) (_h : X.graph.Adj i j) : ℝ :=
  X.node_phases j - X.node_phases i

/-! ## Cost Functions -/

/-- Number of edges in configuration -/
noncomputable def E {n : ℕ} (X : ConfigSpace n) : ℕ :=
  X.graph.edgeSet.ncard

/-- Internal cost: sum of squared constraint violations -/
noncomputable def V_int {n : ℕ} (X : ConfigSpace n) : ℝ :=
  haveI : DecidableRel X.graph.Adj := X.adj_decidable
  ∑ i : Fin n, ∑ j : Fin n,
    if h : X.graph.Adj i j then
      (edge_value X i j h - X.constraints i j h)^2
    else
      0

theorem V_int_nonneg {n : ℕ} (X : ConfigSpace n) : 0 ≤ V_int X := by
  unfold V_int
  haveI : DecidableRel X.graph.Adj := X.adj_decidable
  apply Finset.sum_nonneg'
  intro i
  apply Finset.sum_nonneg'
  intro j
  by_cases h : X.graph.Adj i j
  · simp [h]
    exact sq_nonneg _
  · simp [h]

/-- External task structure -/
structure ExternalTask (n : ℕ) where
  /-- Measure how well a configuration satisfies the task -/
  measure_violation : ConfigSpace n → ℝ
  /-- Tasks have non-negative violation -/
  violation_nonneg : ∀ X, 0 ≤ measure_violation X

/-- External cost: task violation -/
noncomputable def V_ext {n : ℕ} (task : ExternalTask n) (X : ConfigSpace n) : ℝ :=
  task.measure_violation X

/-- V_ext is non-negative -/
theorem V_ext_nonneg {n : ℕ} (task : ExternalTask n) (X : ConfigSpace n) :
    0 ≤ V_ext task X :=
  task.violation_nonneg X

/-- Lagrangian: weighted combination of costs -/
noncomputable def ℒ {n : ℕ} (task : ExternalTask n) (X : ConfigSpace n) (lam : ℝ) : ℝ :=
  V_int X + V_ext task X + lam * (E X : ℝ)

/-! ## Cycles and Holonomy -/

/-- A cycle: k edges with consecutive nodes forming a loop -/
structure Cycle (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) where
  /-- The nodes in the cycle (length k+1, with first = last) -/
  nodes : Fin (k+1) → Fin n
  /-- Cycle property: first node equals last -/
  closes : nodes 0 = nodes ⟨k, Nat.lt_succ_self k⟩
  /-- Consecutive nodes are adjacent -/
  adjacent : ∀ (i : Fin k), G.Adj (nodes i.castSucc) (nodes i.succ)
  /-- Edges are distinct (no edge is traversed twice) -/
  distinct_edges : ∀ (i j : Fin k), (nodes i.castSucc, nodes i.succ) = (nodes j.castSucc, nodes j.succ) → i = j

/-- Sum of edge values around a cycle (from node phases) -/
noncomputable def cycle_edge_sum {n k : ℕ} (X : ConfigSpace n) (c : Cycle n X.graph k) : ℝ :=
  ∑ i : Fin k, edge_value X (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i)

/-- Holonomy defect: sum of constraints around cycle -/
noncomputable def cycle_holonomy {n k : ℕ} (X : ConfigSpace n) (c : Cycle n X.graph k) : ℝ :=
  ∑ i : Fin k, X.constraints (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i)

/-! ## Telescoping Sum -/

/-- Edge values sum to zero around any cycle -/
theorem cycle_edge_sum_zero {n k : ℕ} (X : ConfigSpace n) (c : Cycle n X.graph k) :
    cycle_edge_sum X c = 0 := by
  unfold cycle_edge_sum edge_value
  simp only [Finset.sum_sub_distrib]
  suffices ∑ i : Fin k, X.node_phases (c.nodes i.succ) =
           ∑ i : Fin k, X.node_phases (c.nodes i.castSucc) by linarith
  let f : Fin (k+1) → ℝ := fun i => X.node_phases (c.nodes i)
  show ∑ i : Fin k, f i.succ = ∑ i : Fin k, f i.castSucc
  have h_succ : ∑ i : Fin k, f i.succ = (∑ i : Fin (k+1), f i) - f 0 := by
    rw [Fin.sum_univ_succ]
    ring
  have h_castSucc : ∑ i : Fin k, f i.castSucc = (∑ i : Fin (k+1), f i) - f (Fin.last k) := by
    rw [Fin.sum_univ_castSucc]
    ring
  rw [h_succ, h_castSucc]
  have h_cycle : f 0 = f (Fin.last k) := by
    simp only [f]
    exact congr_arg X.node_phases c.closes

  rw [h_cycle]

/-! ## V_int Lower Bound -/

/-- For a cycle with holonomy K, minimum V_int is K²/k -/
theorem V_int_bounded_by_holonomy_simple (k : ℕ) (h_k : 3 ≤ k) (constraints : Fin k → ℝ) :
    let K := ∑ i : Fin k, constraints i
    ∃ (edge_vals : Fin k → ℝ),
      (∑ i : Fin k, edge_vals i = 0) ∧
      (∀ (other_vals : Fin k → ℝ), ∑ i : Fin k, other_vals i = 0 →
        ∑ i : Fin k, (edge_vals i - constraints i)^2 ≤
        ∑ i : Fin k, (other_vals i - constraints i)^2) ∧
      ∑ i : Fin k, (edge_vals i - constraints i)^2 = K^2 / k := by
  intro K
  use fun i => constraints i - K / k
  have h := general_cycle_holonomy k h_k constraints
  constructor
  · exact h.1
  constructor
  · intro other_vals h_constraint
    calc ∑ i : Fin k, ((fun i => constraints i - K / k) i - constraints i)^2
        = K^2 / k := h.2
      _ ≤ ∑ i : Fin k, (other_vals i - constraints i)^2 :=
          general_cycle_optimal k h_k constraints other_vals h_constraint
  · exact h.2

/-- Configuration with a cycle has V_int bounded below by cycle holonomy -/
theorem V_int_lower_bound {n k : ℕ} (X : ConfigSpace n) (c : Cycle n X.graph k) (h_k : 3 ≤ k) :
    let K := cycle_holonomy X c
    K^2 / k ≤ V_int X := by
  intro K
  let v_cycle : Fin k → ℝ := fun i => edge_value X (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i)
  let c_cycle : Fin k → ℝ := fun i => X.constraints (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i)
  have h_cycle_constraint : ∑ i : Fin k, v_cycle i = 0 := cycle_edge_sum_zero X c
  have h_K_def : K = ∑ i : Fin k, c_cycle i := rfl
  have h_cycle_cost : K^2 / k ≤ ∑ i : Fin k, (v_cycle i - c_cycle i)^2 := by
    rw [h_K_def]
    exact general_cycle_optimal k h_k c_cycle v_cycle h_cycle_constraint
  calc V_int X
      ≥ ∑ i : Fin k, (v_cycle i - c_cycle i)^2 := by
        unfold V_int
        haveI : DecidableRel X.graph.Adj := X.adj_decidable
        conv_lhs => rw [← Finset.sum_product']
        let cycle_edges : Finset (Fin n × Fin n) :=
          Finset.image (fun (i : Fin k) => (c.nodes i.castSucc, c.nodes i.succ)) Finset.univ
        have h_product_eq : (Finset.univ : Finset (Fin n × Fin n)) = Finset.univ ×ˢ Finset.univ := by
          ext p
          simp
        have h_subset : cycle_edges ⊆ Finset.univ := Finset.subset_univ _
        suffices ∑ i : Fin k, (v_cycle i - c_cycle i)^2 =
                 ∑ p ∈ cycle_edges, if h : X.graph.Adj p.1 p.2 then
                   (edge_value X p.1 p.2 h - X.constraints p.1 p.2 h)^2 else 0 by
          rw [ge_iff_le, this, ← h_product_eq]
          convert Finset.sum_le_sum_of_subset_of_nonneg h_subset _ using 1
          case h.e'_4 =>
            congr 1
            funext x
            congr 1
          case convert_5 =>
            infer_instance
          case convert_6 =>
            intro p _ hp_not_cycle
            by_cases h : X.graph.Adj p.1 p.2
            · simp only [h]; exact sq_nonneg _
            · simp only [h]; rfl
        calc ∑ i : Fin k, (v_cycle i - c_cycle i)^2
            = ∑ i : Fin k, (edge_value X (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i) -
                           X.constraints (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i))^2 := by
              simp only [v_cycle, c_cycle]
          _ = ∑ p ∈ Finset.image (fun (i : Fin k) => (c.nodes i.castSucc, c.nodes i.succ)) Finset.univ,
                if h : X.graph.Adj p.1 p.2 then
                  (edge_value X p.1 p.2 h - X.constraints p.1 p.2 h)^2
                else 0 := by
              conv_lhs => arg 2; ext i; rw [show (edge_value X (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i) -
                                              X.constraints (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i))^2 =
                                            (if h : X.graph.Adj (c.nodes i.castSucc) (c.nodes i.succ) then
                                              (edge_value X (c.nodes i.castSucc) (c.nodes i.succ) h -
                                               X.constraints (c.nodes i.castSucc) (c.nodes i.succ) h)^2
                                            else 0) by rw [dif_pos (c.adjacent i)]]
              have h_inj : Set.InjOn (fun (i : Fin k) => (c.nodes i.castSucc, c.nodes i.succ))
                                     (Finset.univ : Finset (Fin k)) := by
                intro i _ j _ h_eq
                exact c.distinct_edges i j h_eq
              rw [Finset.sum_image h_inj]
    _ ≥ K^2 / k := h_cycle_cost

/-! ## Main Theorem -/

/-- Configurations with cycles have positive V_int -/
theorem cycle_creates_holonomy {n k : ℕ} (X : ConfigSpace n)
    (c : Cycle n X.graph k) (h_k : 3 ≤ k)
    (h_generic : cycle_holonomy X c ≠ 0) :
    0 < V_int X := by
  let K := cycle_holonomy X c
  -- K ≠ 0 by genericity assumption
  have h_K_sq_pos : 0 < K^2 := by
    rw [sq_pos_iff]
    exact h_generic
  -- k ≥ 3 > 0
  have h_k_pos : (0 : ℝ) < k := by
    have : 0 < 3 := by norm_num
    exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le this h_k)
  -- Therefore K²/k > 0
  have h_lower_pos : 0 < K^2 / k := div_pos h_K_sq_pos h_k_pos
  -- V_int ≥ K²/k by V_int_lower_bound
  calc V_int X
      ≥ K^2 / k := V_int_lower_bound X c h_k
    _ > 0 := h_lower_pos

/-- Existential form of holonomy theorem -/
theorem proves_axiomatized_version {n k : ℕ} (X : ConfigSpace n)
    (c : Cycle n X.graph k) (h_k : 3 ≤ k)
    (h_generic : cycle_holonomy X c ≠ 0) :
    ∃ ε > 0, ε ≤ V_int X := by
  use cycle_holonomy X c ^ 2 / k
  constructor
  · -- ε > 0 because K ≠ 0
    have h_sq_pos : 0 < (cycle_holonomy X c) ^ 2 := by
      rw [sq_pos_iff]
      exact h_generic
    have h_k_pos : (0 : ℝ) < k := by
      have : 0 < 3 := by norm_num
      exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le this h_k)
    exact div_pos h_sq_pos h_k_pos
  · exact V_int_lower_bound X c h_k

/-! ## Graph Union and Negotiation -/

/-- Union of two graphs -/
def graph_union {n : ℕ} (G1 G2 : SimpleGraph (Fin n)) : SimpleGraph (Fin n) where
  Adj i j := G1.Adj i j ∨ G2.Adj i j
  symm i j h := by
    cases h with
    | inl h1 => exact Or.inl (G1.symm h1)
    | inr h2 => exact Or.inr (G2.symm h2)
  loopless i h := by
    cases h with
    | inl h1 => exact G1.loopless i h1
    | inr h2 => exact G2.loopless i h2

/-- Decidability for union graph adjacency -/
instance {n : ℕ} (G1 G2 : SimpleGraph (Fin n))
    [DecidableRel G1.Adj] [DecidableRel G2.Adj] :
    DecidableRel (graph_union G1 G2).Adj :=
  fun _ _ => instDecidableOr

/-- Merge constraints: for overlapping edges, take the average -/
noncomputable def merge_constraints {n : ℕ}
    (G1 G2 : SimpleGraph (Fin n))
    [DecidableRel G1.Adj] [DecidableRel G2.Adj]
    (c1 : ∀ (i j : Fin n), G1.Adj i j → ℝ)
    (c2 : ∀ (i j : Fin n), G2.Adj i j → ℝ)
    (i j : Fin n) (_h : (graph_union G1 G2).Adj i j) : ℝ :=
  if h1 : G1.Adj i j then
    if h2 : G2.Adj i j then
      (c1 i j h1 + c2 i j h2) / 2  -- Both: average
    else
      c1 i j h1                     -- Only G1
  else
    if h2 : G2.Adj i j then
      c2 i j h2                     -- Only G2
    else
      0                             -- Neither (impossible given _h)

/-- A negotiation problem: find optimal node_phases for the union graph -/
structure NegotiationProblem (n : ℕ) where
  /-- First configuration -/
  X_A : ConfigSpace n
  /-- Second configuration -/
  X_B : ConfigSpace n
  /-- External task both are solving -/
  task : ExternalTask n
  /-- Negotiation parameter (complexity cost weight) -/
  lam : ℝ
  /-- Parameter must be positive -/
  h_lam_pos : 0 < lam

/-- The union configuration for a negotiation problem -/
noncomputable def union_config {n : ℕ} (prob : NegotiationProblem n) : ConfigSpace n :=
  haveI : DecidableRel prob.X_A.graph.Adj := prob.X_A.adj_decidable
  haveI : DecidableRel prob.X_B.graph.Adj := prob.X_B.adj_decidable
  { graph := graph_union prob.X_A.graph prob.X_B.graph
    adj_decidable := inferInstance
    node_phases := prob.X_A.node_phases  -- Initial phases (to be optimized)
    constraints := merge_constraints prob.X_A.graph prob.X_B.graph prob.X_A.constraints prob.X_B.constraints }

/-- A negotiated solution: configuration with optimized phases on the union graph -/
def is_negotiated_solution {n : ℕ} (prob : NegotiationProblem n) (X_N : ConfigSpace n) : Prop :=
  haveI : DecidableRel prob.X_A.graph.Adj := prob.X_A.adj_decidable
  haveI : DecidableRel prob.X_B.graph.Adj := prob.X_B.adj_decidable
  -- Must use the union graph structure with merged constraints
  (∃ (h_graph : X_N.graph = graph_union prob.X_A.graph prob.X_B.graph),
    ∀ (i j : Fin n) (h_adj : X_N.graph.Adj i j),
      X_N.constraints i j h_adj = merge_constraints prob.X_A.graph prob.X_B.graph
        prob.X_A.constraints prob.X_B.constraints i j (h_graph ▸ h_adj)) ∧
  -- Phases minimize the Lagrangian among all possible phase assignments
  ∀ (phases : Fin n → ℝ),
    let X_test : ConfigSpace n := { X_N with node_phases := phases }
    ℒ prob.task X_N prob.lam ≤ ℒ prob.task X_test prob.lam

/-! ## Properties of Negotiation -/

/-- The negotiation framework is well-defined: we can construct union configurations -/
theorem negotiation_framework_defined {n : ℕ} (prob : NegotiationProblem n) :
    ∃ (X_union : ConfigSpace n),
      X_union.graph = graph_union prob.X_A.graph prob.X_B.graph := by
  use union_config prob
  rfl

end GaugeTheoretic
