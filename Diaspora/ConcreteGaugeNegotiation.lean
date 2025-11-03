/-
# Concrete Gauge Negotiation

Translates GaugeNegotiation.lean axioms to use Concrete.ConfigSpace n
instead of abstract ConfigSpace. This allows proving properties by
construction rather than axiomatization.

Strategy (from Gemini's analysis):
1. Parameterize everything by n : ℕ and task : ExternalTask n
2. Replace ConfigSpace with Concrete.ConfigSpace n
3. Replace axioms with theorems proven from concrete 8-node case
4. Weaken universal claims to existential ones
-/

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Diaspora.Concrete
import Diaspora.NoPrivilegedFrame
import Diaspora.MathematicalStructure
import Diaspora.GaugeNegotiationVerified
import Diaspora.GaugeNegotiationExplicit
import Diaspora.GaugeNegotiationProofs

open Concrete
open Diaspora.GaugeNegotiationVerified (DiGraph G_A G_B G_N)
open Diaspora.GaugeNegotiationProofs

namespace ConcreteGaugeNegotiation

/-! ## Concrete Negotiation Structure -/

/-- A negotiation between two concrete perspectives with parameter λ -/
structure ConcreteNegotiation (n : ℕ) where
  /-- External task both perspectives are solving -/
  task : ExternalTask n
  /-- First perspective's configuration -/
  perspective_A : ConfigSpace n
  /-- Second perspective's configuration -/
  perspective_B : ConfigSpace n
  /-- Negotiation parameter (complexity cost) -/
  negotiation_param : ℝ
  /-- Parameter must be positive -/
  h_param_pos : 0 < negotiation_param

/-- The concrete negotiation cost: weighted sum of distances from both perspectives -/
noncomputable def concrete_negotiation_cost {n : ℕ} (neg : ConcreteNegotiation n) (X : ConfigSpace n) : ℝ :=
  ℒ neg.task X neg.negotiation_param +
  (V_int X - V_int neg.perspective_A)^2 +
  (V_ext neg.task X - V_ext neg.task neg.perspective_B)^2

/-- A configuration minimizes concrete negotiation cost -/
def minimizes_concrete_negotiation {n : ℕ} (neg : ConcreteNegotiation n) (C : ConfigSpace n) : Prop :=
  ∀ Y, concrete_negotiation_cost neg C ≤ concrete_negotiation_cost neg Y

/-! ## Proving Axioms by Construction: 8-Node Case -/

/-- There exist graphs where negotiation creates novelty

    PROOF: By citing the 8-node DiGraph case.
    GaugeNegotiationProofs proves G_N ≠ G_A and G_N ≠ G_B.

    Note: This uses DiGraph, not Concrete.ConfigSpace, due to type mismatch.
    The 8-node proof works with directed graphs from GaugeNegotiationVerified.
    Converting between DiGraph and ConfigSpace n requires an embedding that
    doesn't currently exist. -/
theorem negotiation_creates_novelty_exists_digraph :
    ∃ (G_A_ex G_B_ex G_N_ex : DiGraph),
    G_A_ex ≠ G_B_ex ∧
    G_N_ex ≠ G_A_ex ∧
    G_N_ex ≠ G_B_ex := by
  -- Use graphs from GaugeNegotiationVerified
  use G_A, G_B, G_N
  constructor
  · -- G_A ≠ G_B: different edge counts (20 vs 37)
    intro h
    have h_count : G_A.edgeCount = G_B.edgeCount := by rw [h]
    rw [G_A_edge_count, G_B_edge_count] at h_count
    norm_num at h_count
  constructor
  · -- G_N ≠ G_A: proven in GaugeNegotiationProofs
    exact G_N_ne_G_A
  · -- G_N ≠ G_B: proven in GaugeNegotiationProofs
    exact G_N_ne_G_B

/-- There exist graphs where negotiation produces intermediate complexity

    PROOF: By citing the 8-node DiGraph case.
    The case proves min(20, 37) = 20 ≤ 34 ≤ 57. -/
theorem negotiation_intermediate_complexity_exists_digraph :
    ∃ (G_A_ex G_B_ex G_N_ex : DiGraph),
    min G_A_ex.edgeCount G_B_ex.edgeCount ≤ G_N_ex.edgeCount ∧
    G_N_ex.edgeCount ≤ G_A_ex.edgeCount + G_B_ex.edgeCount := by
  -- Use graphs from GaugeNegotiationVerified
  use G_A, G_B, G_N
  -- Cite the proven result
  exact negotiation_intermediate_complexity_concrete

/-! ## Coercivity Analysis for Convergence

Gemini identified that negotiation_convergence requires either:
1. Restricting to compact domain
2. Proving coercivity: cost → ∞ as ||X|| → ∞

Let's analyze the cost function structure.
-/

/-- The negotiation cost is unbounded: for any M, there exists X with cost > M

    This demonstrates the space is non-compact.

    Assumes the graph has at least one edge (otherwise all configs have V_int = 0
    and boundedness depends on V_ext and E terms).

    Proof: Set all constraints to 0 and all edge values to large k.
    Then V_int = k² * (number of edges), which grows without bound. -/
theorem negotiation_cost_unbounded {n : ℕ} (neg : ConcreteNegotiation n)
    (h_has_edge : 0 < E neg.perspective_A) :
    ∀ M : ℝ, ∃ X : ConfigSpace n,
    concrete_negotiation_cost neg X > M := by
  intro M
  -- Choose k large enough so k² * (number of edges) > M
  let k := max (Real.sqrt (max (M + 1) 0)) 1
  -- Construct X with same graph as A but all constraints 0 and all values k
  let X : ConfigSpace n := {
    graph := neg.perspective_A.graph
    adj_decidable := neg.perspective_A.adj_decidable
    constraints := fun _ _ _ => 0  -- All constraints zero
    edge_values := fun _ _ _ => k  -- All edge values k
  }
  use X
  unfold concrete_negotiation_cost Concrete.ℒ

  -- Since graph has edges, Concrete.V_int X ≥ k²
  have h_vint_large : k^2 ≤ Concrete.V_int X := by
    -- E X > 0 means there exists at least one edge
    unfold Concrete.E at h_has_edge

    -- Since E > 0, edgeSet is nonempty, so ∃ i j with Adj i j
    have h_exists_edge : ∃ i j, X.graph.Adj i j := by
      by_contra h_no_edge
      push_neg at h_no_edge
      -- If no edges, then edgeSet is empty
      have h_empty : X.graph.edgeSet = ∅ := by
        ext e
        simp only [Set.mem_empty_iff_false, iff_false]
        intro h_mem
        -- e ∈ edgeSet means Adj on the two vertices of e
        induction e using Sym2.ind
        exact h_no_edge _ _ h_mem
      rw [h_empty, Set.ncard_empty] at h_has_edge
      omega

    obtain ⟨i, j, h_ij⟩ := h_exists_edge

    -- Unfold V_int to work with the double sum
    unfold Concrete.V_int
    haveI : DecidableRel X.graph.Adj := X.adj_decidable

    -- All edge values are k and all constraints are 0
    -- This follows from the definition of X
    have h_all_edges_k : ∀ a b (h : X.graph.Adj a b),
        (X.edge_values a b h - X.constraints a b h)^2 = k^2 := by
      intros a b hab
      -- X.edge_values = fun _ _ _ => k and X.constraints = fun _ _ _ => 0
      show (k - 0)^2 = k^2
      ring

    -- The double sum ≥ the term for (i,j), which equals k²
    have h_term_ij : (if h : X.graph.Adj i j then (X.edge_values i j h - X.constraints i j h)^2 else 0) = k^2 := by
      simp only [h_ij]
      exact h_all_edges_k i j h_ij

    -- The inner sum at i contains the term for j
    have h_inner : k^2 ≤ ∑ j' : Fin n, if h : X.graph.Adj i j' then (X.edge_values i j' h - X.constraints i j' h)^2 else 0 := by
      rw [←h_term_ij]
      have : ∀ j' ∈ Finset.univ, 0 ≤ (if h : X.graph.Adj i j' then (X.edge_values i j' h - X.constraints i j' h)^2 else 0) := by
        intros; split <;> [exact sq_nonneg _; norm_num]
      exact Finset.single_le_sum this (Finset.mem_univ j)

    -- The outer sum contains the inner sum at i
    have h_outer : (∑ j' : Fin n, if h : X.graph.Adj i j' then (X.edge_values i j' h - X.constraints i j' h)^2 else 0) ≤
        (∑ i' : Fin n, ∑ j' : Fin n, if h : X.graph.Adj i' j' then (X.edge_values i' j' h - X.constraints i' j' h)^2 else 0) := by
      have : ∀ i' ∈ Finset.univ, 0 ≤ ∑ j' : Fin n, if h : X.graph.Adj i' j' then (X.edge_values i' j' h - X.constraints i' j' h)^2 else 0 := by
        intros; apply Finset.sum_nonneg; intros; split <;> [exact sq_nonneg _; norm_num]
      exact Finset.single_le_sum this (Finset.mem_univ i)

    convert le_trans h_inner h_outer

  -- k² ≥ M + 1 by choice of k (k ≥ 1 always, and k ≥ sqrt(M+1) when M+1 > 0)
  have h_k_large : M + 1 ≤ k^2 := by
    have h_k_ge_1 : 1 ≤ k := le_max_right _ _
    by_cases h_pos : 0 < M + 1
    · -- M + 1 > 0: k ≥ sqrt(M+1), so k² ≥ M+1
      have h_max_pos : max (M + 1) 0 = M + 1 := max_eq_left (le_of_lt h_pos)
      have h_k_ge_sqrt : Real.sqrt (M + 1) ≤ k := by
        have : Real.sqrt (M + 1) = Real.sqrt (max (M + 1) 0) := by rw [h_max_pos]
        rw [this]
        exact le_max_left _ _
      calc M + 1 = Real.sqrt (M + 1) ^ 2 := by rw [Real.sq_sqrt (le_of_lt h_pos)]
          _ ≤ k ^ 2 := by
            apply sq_le_sq'
            · have : Real.sqrt (M + 1) ≥ 0 := Real.sqrt_nonneg _
              linarith
            · exact h_k_ge_sqrt
    · -- M + 1 ≤ 0: k ≥ 1 so k² ≥ 1 > M+1
      push_neg at h_pos
      have : M + 1 < k^2 := by
        calc M + 1 ≤ 0 := h_pos
            _ < 1 := by norm_num
            _ ≤ k := h_k_ge_1
            _ ≤ k^2 := by nlinarith [sq_nonneg k]
      linarith

  -- Combine: cost ≥ V_int X ≥ k² ≥ M + 1 > M
  have h1 : 0 ≤ Concrete.V_ext neg.task X := Concrete.V_ext_nonneg neg.task X
  have h2 : 0 ≤ neg.negotiation_param * (Concrete.E X : ℝ) :=
    mul_nonneg (le_of_lt neg.h_param_pos) (Nat.cast_nonneg (Concrete.E X))
  have h3 : 0 ≤ (Concrete.V_int X - Concrete.V_int neg.perspective_A)^2 := sq_nonneg _
  have h4 : 0 ≤ (Concrete.V_ext neg.task X - Concrete.V_ext neg.task neg.perspective_B)^2 := sq_nonneg _

  calc Concrete.V_int X + Concrete.V_ext neg.task X + neg.negotiation_param * (Concrete.E X : ℝ) +
        (Concrete.V_int X - Concrete.V_int neg.perspective_A)^2 +
        (Concrete.V_ext neg.task X - Concrete.V_ext neg.task neg.perspective_B)^2
      ≥ Concrete.V_int X := by linarith
    _ ≥ k^2 := h_vint_large
    _ ≥ M + 1 := h_k_large
    _ > M := by linarith

/-! ## The Compactness Challenge

The space ConfigSpace n is NOT compact because edge_values : ... → ℝ is unbounded.
To prove convergence, we need to show the minimizer exists in some bounded region.

Potential approach:
1. Show that for any ε > 0, the set {X | cost(X) ≤ cost(X₀) + ε} is bounded
2. This gives a compact sublevel set
3. Continuous function on compact set has minimum (Weierstrass)
-/

/-! ## Connection to Abstract Axioms

The abstract GaugeNegotiation.lean makes universal claims like:
  ∀ A B C : ConfigSpace, ... → property(A, B, C)

We're converting these to existential claims:
  ∃ n task (A B C : ConfigSpace n), ... ∧ property(A, B, C)

This is weaker but provable by construction from concrete examples.
-/

/-! ## Future Work: Embedding Concrete in Abstract

Abstract ConfigSpace can embed concrete instances.

TODO: This requires defining how to lift Concrete.ConfigSpace n
to the abstract ConfigSpace from Axioms.lean.

The challenge: abstract ConfigSpace has no parameter n.
May need to add such a parameterization or use a different approach.
-/

end ConcreteGaugeNegotiation
