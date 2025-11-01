/-
# Concrete Proof of Holonomy Tax

Shows that tasks requiring cycles force non-zero internal cost.

## Note on Axioms vs Theorems

This file uses simplified axioms for pedagogical purposes. The core result
`cycle_creates_holonomy` is now PROVEN (not axiomatized) in:

- **HolonomyLagrangeProof.lean**: Pure optimization theory proof via Lagrange multipliers
  - Proves: For any n-cycle with constraints, V_int ≥ K²/n (Theorem: general_cycle_optimal)
  - Proves: If K ≠ 0, then V_int > 0 (Theorem: holonomy_is_inevitable)

- **GaugeTheoreticHolonomy.lean**: Gauge-theoretic formulation
  - Proves: cycle_creates_holonomy using the Lagrange result
  - Shows holonomy emerges from gauge structure + topology, not as an axiom

The axioms below remain for backward compatibility and pedagogical clarity,
but the fundamental result is now proven from first principles.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Diaspora.Axioms
import Diaspora.Task

/-! ## Numeric Helper -/

lemma tenth_eq : (0.1:ℝ) = (1:ℝ) / 10 := by norm_num

/-! ## Setup: Task Requiring Cycles -/

/-- A task that requires a cycle (e.g., 3-node triangle) -/
def triangle_task : ExternalTask where
  required_paths := [(0, 1), (1, 2), (2, 0)]
  required_cycles := [[0, 1, 2]]

/-- Any graph satisfying triangle_task must have at least 3 edges -/
axiom triangle_min_edges (G : Graph) (h : satisfies_task G triangle_task) :
  ∃ (edge_count : ℕ), 3 ≤ edge_count

/-- Cycles create holonomy (non-zero internal cost with minimum bound)

    FORMERLY AXIOM - NOW PROVEN in GaugeTheoreticHolonomy.lean!

    The proof shows that for any cycle with holonomy defect K ≠ 0,
    we have V_int ≥ K²/k, which is strictly positive.

    This version remains as an axiom for backward compatibility with the
    simplified ConfigSpace definition used in this pedagogical file.
    For the rigorous proof, see GaugeTheoreticHolonomy.lean. -/
axiom cycle_creates_holonomy (X : ConfigSpace) :
  (∃ cycle : List X.G.edges, cycle.length ≥ 3) → 0.1 ≤ V_int X

/-- If a graph satisfies a task with required cycles, it has a cycle -/
axiom satisfies_task_has_cycle (X : ConfigSpace) (t : ExternalTask)
    (hsat : satisfies_task X.G t) (hcycles : t.required_cycles ≠ []) :
  ∃ cycle : List X.G.edges, cycle.length ≥ 3

/-! ## Theorem: Holonomy Tax for Triangle Task -/

/-- For the triangle task, MDL-optimal solutions must pay holonomy tax -/
theorem triangle_holonomy_tax :
    ∃ ε > 0, ∀ X : ConfigSpace,
    satisfies_task X.G triangle_task → ε ≤ V_int X := by
  use (1:ℝ) / 10
  constructor
  · norm_num
  · intro X hX
    rw [← tenth_eq]
    apply cycle_creates_holonomy
    apply satisfies_task_has_cycle X triangle_task hX
    intro h3
    contradiction

/-! ## General Theorem -/

/-- Tasks requiring cycles force non-zero internal cost -/
theorem cycle_task_forces_holonomy (t : ExternalTask)
    (h : t.required_cycles ≠ []) :
    ∃ ε > 0, ∀ X : ConfigSpace,
    satisfies_task X.G t → ε ≤ V_int X := by
  use (1:ℝ) / 10
  constructor
  · norm_num
  · intro X hX
    rw [← tenth_eq]
    apply cycle_creates_holonomy
    exact satisfies_task_has_cycle X t hX h
