/-
Mass as holonomy: defines mass from the constraint structure.
-/

import Diaspora.GaugeTheoreticHolonomy
import Diaspora.Experiments.SchwarzschildDerivation

open GaugeTheoretic

namespace MassDefinition

/-- Mass is the total holonomy of the system. -/
noncomputable def mass {n k : ℕ} (X : ConfigSpace n) (c : Cycle n X.graph k) : ℝ :=
  cycle_holonomy X c

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
    SchwarzschildDerivation.E_ground_state X c = (mass X c)^2 := by
  unfold mass
  exact SchwarzschildDerivation.ground_state_energy_law X c h_k

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

/-- Schwarzschild relationship using mass definition. -/
theorem schwarzschild_with_mass_definition {n k : ℕ} (X : ConfigSpace n)
    (c : Cycle n X.graph k) (h_k : 3 ≤ k)
    (R S A : ℝ) (h_M_pos : 0 < mass X c) (h_R_pos : 0 < R)
    (h_entropy : ∃ α > 0, S = α * SchwarzschildDerivation.E_ground_state X c)
    (h_BH : ∃ κ > 0, S = κ * A)
    (h_geom : ∃ π > 0, A = π * R^2) :
    ∃ δ > 0, mass X c = δ * R := by
  -- Use the proven Schwarzschild derivation
  have h_energy := SchwarzschildDerivation.ground_state_energy_law X c h_k
  -- S ∝ E₀ and E₀ = M² gives S ∝ M²
  have h_S_M : ∃ γ > 0, S = γ * (mass X c)^2 := by
    obtain ⟨α, h_α_pos, h_S_eq⟩ := h_entropy
    use α
    constructor
    · exact h_α_pos
    · rw [h_S_eq, h_energy]
      unfold mass
      rfl
  -- Apply Schwarzschild derivation
  exact SchwarzschildDerivation.schwarzschild_linear_law
    (mass X c) R S A h_M_pos h_R_pos h_S_M h_BH h_geom

end MassDefinition
