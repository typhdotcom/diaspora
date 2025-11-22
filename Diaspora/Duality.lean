/-
# Duality.lean

Discrete Hodge star duality between primal and dual graph structures.

We construct an explicit duality transformation between:
1. A triangular loop (3 vertices, 3 edges)
2. A star graph (1 center, 3 outer nodes)

We prove that the circulation (holonomy) around the primal loop equals
the divergence from the center of the dual star graph.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

open BigOperators

namespace DiscreteHodge

/-! ## 1. Primal Graph -/

/--
A triangular loop graph.
Vertices: 0, 1, 2.
Edges: (0,1), (1,2), (2,0).
-/
abbrev n_primal : ℕ := 3
abbrev PrimalNode := Fin n_primal

/-- A skew-symmetric 1-cochain on the primal graph. -/
structure PrimalForm where
  val : PrimalNode → PrimalNode → ℝ
  skew : ∀ i j, val i j = -val j i

/-- Circulation around the triangular loop. -/
def primal_holonomy (σ : PrimalForm) : ℝ :=
  σ.val 0 1 + σ.val 1 2 + σ.val 2 0

/-! ## 2. Dual Graph -/

/--
A star graph with center and three spokes.
Center node: 0.
Outer nodes: 1, 2, 3.
-/
abbrev n_dual : ℕ := 4
abbrev DualNode := Fin n_dual

/-- The center node of the dual graph. -/
def Center : DualNode := 0

/-- A skew-symmetric 1-cochain on the dual graph. -/
structure DualForm where
  val : DualNode → DualNode → ℝ
  skew : ∀ i j, val i j = -val j i

/-- Net divergence at a node (sum of outgoing flows). -/
def dual_divergence (σ_star : DualForm) (p : DualNode) : ℝ :=
  ∑ neighbor : DualNode, σ_star.val p neighbor

/-! ## 3. Hodge Star Operator -/

/--
Maps each primal edge to a dual edge radiating from the center.
- Primal (0→1) ↦ Dual (0→1)
- Primal (1→2) ↦ Dual (0→2)
- Primal (2→0) ↦ Dual (0→3)
-/
noncomputable def hodge_star (σ : PrimalForm) : DualForm := {
  val := fun u v =>
    if u = 0 ∧ v = 1 then σ.val 0 1
    else if u = 1 ∧ v = 0 then -σ.val 0 1
    else if u = 0 ∧ v = 2 then σ.val 1 2
    else if u = 2 ∧ v = 0 then -σ.val 1 2
    else if u = 0 ∧ v = 3 then σ.val 2 0
    else if u = 3 ∧ v = 0 then -σ.val 2 0
    else 0,
  skew := by
    intro u v
    fin_cases u <;> fin_cases v <;> simp <;> try split_ifs <;> try ring
}

/-! ## 4. Duality Theorem -/

/--
The circulation around the primal loop equals the divergence from the dual center.
This is a discrete version of Stokes' theorem / Poincaré duality.
-/
theorem primal_dual_identity (σ : PrimalForm) :
  primal_holonomy σ = dual_divergence (hodge_star σ) Center := by

  unfold primal_holonomy dual_divergence Center
  rw [Fin.sum_univ_four]
  have h0 : (hodge_star σ).val 0 0 = 0 := by unfold hodge_star; simp
  have h1 : (hodge_star σ).val 0 1 = σ.val 0 1 := by unfold hodge_star; simp
  have h2 : (hodge_star σ).val 0 2 = σ.val 1 2 := by unfold hodge_star; simp
  have h3 : (hodge_star σ).val 0 3 = σ.val 2 0 := by unfold hodge_star; simp
  rw [h0, h1, h2, h3]
  ring

end DiscreteHodge
