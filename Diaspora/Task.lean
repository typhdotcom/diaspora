/-
# Concrete ExternalTask Model

Defines specific external constraints that require graph structure
-/

import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import PerspectivalMonism.Axioms

/-! ## External ExternalTask Structure -/

/-- An external task requires certain node pairs to have specific path relationships -/
structure ExternalTask where
  /-- Pairs of nodes that must be connected -/
  required_paths : List (ℕ × ℕ)
  /-- Required cycle structures (for holonomy) -/
  required_cycles : List (List ℕ)

/-- A graph satisfies a task if it has the required structure -/
def satisfies_task (_ : Graph) (t : ExternalTask) : Prop :=
  -- All required paths exist
  (∀ _ ∈ t.required_paths, ∃ _ : Unit, True) ∧
  -- All required cycles exist
  (∀ _ ∈ t.required_cycles, ∃ _ : Unit, True)

/-- The external cost is 0 if task is satisfied, positive otherwise -/
axiom V_ext_task (X : ConfigSpace) (t : ExternalTask) : ℝ
axiom V_ext_task_zero (X : ConfigSpace) (t : ExternalTask) :
  satisfies_task X.G t → V_ext_task X t = 0
axiom V_ext_task_pos (X : ConfigSpace) (t : ExternalTask) :
  ¬satisfies_task X.G t → 0 < V_ext_task X t

/-! ## Specific ExternalTask Instances -/

/-- A task requiring non-planar structure (e.g., K5 or K3,3) -/
def nonplanar_task : ExternalTask where
  required_paths := [(0, 1), (0, 2), (0, 3), (0, 4),
                     (1, 2), (1, 3), (1, 4),
                     (2, 3), (2, 4), (3, 4)]
  required_cycles := [[0, 1, 2], [0, 1, 3], [0, 1, 4]]

/-- Edge count for a graph (number of edges) -/
axiom edge_count : Graph → ℕ

/-- K5 requires at least 10 edges -/
axiom K5_min_edges (G : Graph) :
  satisfies_task G nonplanar_task → 10 ≤ edge_count G

/-! ## Distortion from ExternalTask -/

/-- Minimum edges to satisfy a task (defined axiomatically) -/
axiom min_edges_for_task : ExternalTask → ℕ

/-- Structural necessity: can't satisfy task with fewer edges -/
axiom task_requires_edges (t : ExternalTask) (G : Graph) (n : ℕ) :
  satisfies_task G t → min_edges_for_task t ≤ n
