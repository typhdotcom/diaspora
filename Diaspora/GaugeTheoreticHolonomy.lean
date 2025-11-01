/-
# Gauge-Theoretic Proof of Holonomy

Proves that cycles create holonomy as a THEOREM, not an axiom.

Key insight: Edge values must come from node phases (gauge structure).
This makes cycle constraints automatic, forcing V_int > 0 for generic tasks.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Basic
import PerspectivalMonism.HolonomyLagrangeProof

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

/-! ## Cost Function -/

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

/-! ## Key Theorem 1: Telescoping Sum -/

/-- Edge values from node phases sum to zero around any cycle -/
theorem cycle_edge_sum_zero {n k : ℕ} (X : ConfigSpace n) (c : Cycle n X.graph k) :
    cycle_edge_sum X c = 0 := by
  unfold cycle_edge_sum edge_value
  -- The sum is: Σᵢ (φ[i+1] - φ[i])
  -- Expanding: (φ₁-φ₀) + (φ₂-φ₁) + ... + (φₖ-φₖ₋₁)
  -- This telescopes to: φₖ - φ₀
  -- But by cycle property: φₖ = φ₀, so the sum = 0

  -- Expand using sum_sub_distrib
  simp only [Finset.sum_sub_distrib]

  -- Show ∑ node_phases(nodes(i.succ)) = ∑ node_phases(nodes(i.castSucc))
  suffices ∑ i : Fin k, X.node_phases (c.nodes i.succ) =
           ∑ i : Fin k, X.node_phases (c.nodes i.castSucc) by linarith

  -- Abstract the function: f i = node_phases(nodes(i))
  let f : Fin (k+1) → ℝ := fun i => X.node_phases (c.nodes i)

  -- Rewrite using f
  show ∑ i : Fin k, f i.succ = ∑ i : Fin k, f i.castSucc

  -- Use Fin.sum_univ_succ: ∑ᵢ f i = f 0 + ∑ᵢ f i.succ
  -- So: ∑ᵢ f i.succ = (∑ᵢ f i) - f 0
  have h_succ : ∑ i : Fin k, f i.succ = (∑ i : Fin (k+1), f i) - f 0 := by
    rw [Fin.sum_univ_succ]
    ring

  -- Use Fin.sum_univ_castSucc: ∑ᵢ f i = (∑ᵢ f i.castSucc) + f (last k)
  -- So: ∑ᵢ f i.castSucc = (∑ᵢ f i) - f (last k)
  have h_castSucc : ∑ i : Fin k, f i.castSucc = (∑ i : Fin (k+1), f i) - f (Fin.last k) := by
    rw [Fin.sum_univ_castSucc]
    ring

  -- Combine: need to show f 0 = f (last k)
  rw [h_succ, h_castSucc]

  -- This follows from cycle property
  have h_cycle : f 0 = f (Fin.last k) := by
    simp only [f]
    exact congr_arg X.node_phases c.closes

  rw [h_cycle]

/-! ## Key Theorem 2: V_int Lower Bound -/

/-- Helper: For a cycle of length k with holonomy K, minimum V_int is K²/k -/
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
    -- From h.2: ∑(v_opt i - c i)² = K²/k
    -- From general_cycle_optimal: K²/k ≤ ∑(other_vals i - c i)²
    -- Therefore: ∑(v_opt i - c i)² ≤ ∑(other_vals i - c i)²
    calc ∑ i : Fin k, ((fun i => constraints i - K / k) i - constraints i)^2
        = K^2 / k := h.2
      _ ≤ ∑ i : Fin k, (other_vals i - constraints i)^2 :=
          general_cycle_optimal k h_k constraints other_vals h_constraint
  · exact h.2

/-- Any configuration with a cycle has V_int bounded below by cycle holonomy -/
theorem V_int_lower_bound {n k : ℕ} (X : ConfigSpace n) (c : Cycle n X.graph k) (h_k : 3 ≤ k) :
    let K := cycle_holonomy X c
    K^2 / k ≤ V_int X := by
  intro K
  -- Strategy: V_int sums over ALL edges, cycle edges are a subset
  -- Define cycle edge values and constraints
  let v_cycle : Fin k → ℝ := fun i => edge_value X (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i)
  let c_cycle : Fin k → ℝ := fun i => X.constraints (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i)

  -- Cycle edge values sum to 0 (gauge constraint)
  have h_cycle_constraint : ∑ i : Fin k, v_cycle i = 0 := cycle_edge_sum_zero X c

  -- K is the sum of cycle constraints
  have h_K_def : K = ∑ i : Fin k, c_cycle i := rfl

  -- By general_cycle_optimal: cost on cycle edges ≥ K²/k
  have h_cycle_cost : K^2 / k ≤ ∑ i : Fin k, (v_cycle i - c_cycle i)^2 := by
    rw [h_K_def]
    exact general_cycle_optimal k h_k c_cycle v_cycle h_cycle_constraint

  -- V_int includes cycle edges plus others (all ≥ 0)
  -- So V_int ≥ cycle cost ≥ K²/k
  calc V_int X
      ≥ ∑ i : Fin k, (v_cycle i - c_cycle i)^2 := by
        unfold V_int
        haveI : DecidableRel X.graph.Adj := X.adj_decidable

        -- Rewrite V_int as sum over product Fin n × Fin n
        conv_lhs => rw [← Finset.sum_product']

        -- Define cycle edges as a finset
        let cycle_edges : Finset (Fin n × Fin n) :=
          Finset.image (fun (i : Fin k) => (c.nodes i.castSucc, c.nodes i.succ)) Finset.univ

        -- Show cycle edges ⊆ all edges (as product)
        have h_product_eq : (Finset.univ : Finset (Fin n × Fin n)) = Finset.univ ×ˢ Finset.univ := by
          ext p
          simp
        have h_subset : cycle_edges ⊆ Finset.univ := Finset.subset_univ _

        -- Show LHS = sum over cycle_edges, then apply subset lemma
        suffices ∑ i : Fin k, (v_cycle i - c_cycle i)^2 =
                 ∑ p ∈ cycle_edges, if h : X.graph.Adj p.1 p.2 then
                   (edge_value X p.1 p.2 h - X.constraints p.1 p.2 h)^2 else 0 by
          rw [ge_iff_le, this, ← h_product_eq]
          -- Both sums are now over subsets of Finset.univ (for Fin n × Fin n)
          -- LHS: cycle_edges ⊆ RHS: Finset.univ
          -- Apply subset lemma
          convert Finset.sum_le_sum_of_subset_of_nonneg h_subset _ using 1
          case h.e'_4 =>
            -- Sums are equal modulo decidability instance (proof irrelevance)
            congr 1
            funext x
            congr 1
          case convert_5 =>
            -- AddLeftMono for ℝ
            infer_instance
          case convert_6 =>
            -- Nonnegativity of terms outside cycle_edges
            intro p _ hp_not_cycle
            by_cases h : X.graph.Adj p.1 p.2
            · simp only [h]; exact sq_nonneg _
            · simp only [h]; rfl

        -- Reindex: Each term on LHS corresponds to a term in cycle_edges sum
        calc ∑ i : Fin k, (v_cycle i - c_cycle i)^2
            = ∑ i : Fin k, (edge_value X (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i) -
                           X.constraints (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i))^2 := by
              simp only [v_cycle, c_cycle]
          _ = ∑ p ∈ Finset.image (fun (i : Fin k) => (c.nodes i.castSucc, c.nodes i.succ)) Finset.univ,
                if h : X.graph.Adj p.1 p.2 then
                  (edge_value X p.1 p.2 h - X.constraints p.1 p.2 h)^2
                else 0 := by
              -- Each i contributes the cost of edge (nodes[i.castSucc], nodes[i.succ])
              -- Since all cycle edges are adjacent (c.adjacent i), the `if` is always true
              conv_lhs => arg 2; ext i; rw [show (edge_value X (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i) -
                                              X.constraints (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i))^2 =
                                            (if h : X.graph.Adj (c.nodes i.castSucc) (c.nodes i.succ) then
                                              (edge_value X (c.nodes i.castSucc) (c.nodes i.succ) h -
                                               X.constraints (c.nodes i.castSucc) (c.nodes i.succ) h)^2
                                            else 0) by rw [dif_pos (c.adjacent i)]]
              -- Now use Finset.sum_image to reindex
              have h_inj : Set.InjOn (fun (i : Fin k) => (c.nodes i.castSucc, c.nodes i.succ))
                                     (Finset.univ : Finset (Fin k)) := by
                intro i _ j _ h_eq
                exact c.distinct_edges i j h_eq
              rw [Finset.sum_image h_inj]
    _ ≥ K^2 / k := h_cycle_cost

/-! ## Key Theorem 3: Generic Tasks Have Non-Zero Holonomy -/

/-- An external task structure -/
structure ExternalTask (n : ℕ) where
  /-- Required edges (pairs that must be connected) -/
  required_edges : List (Fin n × Fin n)
  /-- Constraint values for required edges -/
  edge_constraints : ∀ (e : Fin n × Fin n), e ∈ required_edges → ℝ
  /-- Non-triviality: at least one constraint is non-zero -/
  nontrivial : ∃ (e : Fin n × Fin n) (h : e ∈ required_edges),
    edge_constraints e h ≠ 0

/-- A configuration satisfies a task if it has all required edges with given constraints -/
def satisfies_task {n : ℕ} (X : ConfigSpace n) (task : ExternalTask n) : Prop :=
  ∀ (e : Fin n × Fin n) (h : e ∈ task.required_edges),
    ∃ (h_adj : X.graph.Adj e.1 e.2),
      X.constraints e.1 e.2 h_adj = task.edge_constraints e h

/-! ## Main Theorem: Cycles Create Holonomy -/

/-- The main result: configurations with cycles must have positive V_int -/
theorem cycle_creates_holonomy {n k : ℕ} (X : ConfigSpace n)
    (_task : ExternalTask n) (_h_sat : satisfies_task X _task)
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

/-! ## Connection to Original Axioms

Specific numerical bounds (e.g. 0.1 ≤ V_int for certain task geometries) can be
proven case-by-case based on the structure of specific tasks. The general result
is that V_int ≥ K²/k where K is the holonomy defect.
-/

/-- This proves the axiomatized version in HolonomyProof.lean -/
theorem proves_axiomatized_version {n k : ℕ} (X : ConfigSpace n)
    (_task : ExternalTask n) (_h_sat : satisfies_task X _task)
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

end GaugeTheoretic
