/-
Mass as holonomy: defines mass from the constraint structure.
-/

import Diaspora.GaugeTheoreticHolonomy

open GaugeTheoretic

namespace MassDefinition

/-- Mass is the total holonomy of the system. -/
noncomputable def mass {n k : ℕ} (X : ConfigSpace n) (c : Cycle n X.graph k) : ℝ :=
  cycle_holonomy X c

/-- Ground-state energy: E_0 = K² -/
noncomputable def E_ground_state {n k : ℕ} (X : ConfigSpace n) (c : Cycle n X.graph k) : ℝ :=
  ((cycle_holonomy X c)^2 / k) * k

theorem ground_state_energy_law {n k : ℕ} (X : ConfigSpace n)
    (c : Cycle n X.graph k) (h_k : 3 ≤ k) :
    E_ground_state X c = (cycle_holonomy X c)^2 := by
  unfold E_ground_state
  have h_k_pos : (k : ℝ) ≠ 0 := by
    have : 0 < 3 := by norm_num
    have : 0 < k := Nat.lt_of_lt_of_le this h_k
    exact Nat.cast_ne_zero.mpr (ne_of_gt this)
  field_simp [h_k_pos]

/-- Source theorem: M = K holds with β = 1. -/
theorem source_theorem {n k : ℕ} (X : ConfigSpace n) (c : Cycle n X.graph k) :
    ∃ β : ℝ, β = 1 ∧ mass X c = β * cycle_holonomy X c := by
  use 1
  simp [mass]

/-- Mass is proportional to holonomy. -/
theorem mass_proportional_to_holonomy {n k : ℕ} (X : ConfigSpace n)
    (c : Cycle n X.graph k) :
    mass X c = cycle_holonomy X c := rfl

/-- E₀ = M² in natural units. -/
theorem mass_energy_relation {n k : ℕ} (X : ConfigSpace n)
    (c : Cycle n X.graph k) (h_k : 3 ≤ k) :
    E_ground_state X c = (mass X c)^2 := by
  unfold mass
  exact ground_state_energy_law X c h_k

/-- Mass is non-zero for systems with non-zero holonomy. -/
theorem mass_pos_of_holonomy_ne_zero {n k : ℕ} (X : ConfigSpace n)
    (c : Cycle n X.graph k) (h : cycle_holonomy X c ≠ 0) :
    mass X c ≠ 0 := by
  unfold mass
  exact h

/-- Mass can be negative. -/
theorem mass_allows_negative {n k : ℕ} (X : ConfigSpace n)
    (c : Cycle n X.graph k)
    (h_pos : 0 < cycle_holonomy X c) :
    ∃ X' : ConfigSpace n, ∃ c' : Cycle n X'.graph k, mass X' c' < 0 := by
  -- Negate all constraints to flip the sign of mass
  let X' : ConfigSpace n := {
    graph := X.graph
    node_phases := X.node_phases
    constraints := fun i j h => -(X.constraints i j h)
    adj_decidable := X.adj_decidable
  }
  let c' : Cycle n X'.graph k := c
  use X', c'

  unfold mass cycle_holonomy
  have : (∑ i : Fin k, X'.constraints (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i)) =
         -(∑ i : Fin k, X.constraints (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i)) := by
    rw [← Finset.sum_neg_distrib]
  calc ∑ i : Fin k, X'.constraints (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i)
      = -(∑ i : Fin k, X.constraints (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i)) := this
    _ = -(cycle_holonomy X c) := rfl
    _ < 0 := by linarith


end MassDefinition
