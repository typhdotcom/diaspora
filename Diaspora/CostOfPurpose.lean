/-
# Cost of Purpose and Holonomy Closure

Connects the inheritance theorem's "cost of purpose" to holonomy closure work.

The cost of purpose (V_int(original) - Σc²) measures work paid beyond baseline
to optimize. For optimally closed cycles, this equals K²/k - Σc².
-/

import Diaspora.InheritanceTheorem
import Diaspora.ConservationOfHolonomy
import Diaspora.GaugeTheoreticHolonomy

open GaugeTheoretic InheritanceTheorem ConservationOfHolonomy

namespace CostOfPurpose

/-- Optimal holonomy redistribution beats baseline when holonomy is dispersed. -/
theorem optimal_beats_baseline_when_dispersed {n k : ℕ} (X : ConfigSpace n)
    (c : Cycle n X.graph k) (_h_k : 3 ≤ k)
    (h_optimal : V_int X = (cycle_holonomy X c)^2 / k) :
    let K := cycle_holonomy X c
    let baseline := ∑ i : Fin k,
      (X.constraints (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i))^2
    K^2 < k * baseline → V_int X < baseline := by
  intro K baseline h_dispersed
  rw [h_optimal]
  have h_k_pos : (0 : ℝ) < k := by norm_cast; omega
  calc (cycle_holonomy X c)^2 / k
      = K^2 / k := by rfl
    _ < k * baseline / k := by exact div_lt_div_of_pos_right h_dispersed h_k_pos
    _ = baseline := by field_simp

/-- For optimally closed cycles, cost of purpose equals K²/k - Σc². -/
theorem inheritance_is_path_closure {n k : ℕ} (scen : InheritanceTheorem.InheritanceScenario n k)
    (h_orig_optimal : V_int (InheritanceTheorem.original_config scen) =
      (cycle_holonomy (InheritanceTheorem.original_config scen) scen.cycle)^2 / k) :
    InheritanceTheorem.cost_of_purpose scen =
      (cycle_holonomy (InheritanceTheorem.original_config scen) scen.cycle)^2 / k -
      InheritanceTheorem.sum_squared_constraints scen := by
  unfold InheritanceTheorem.cost_of_purpose InheritanceTheorem.baseline_cost
  rw [h_orig_optimal]

/-- **Main Result**: When a cycle achieves optimal V_int = K²/k, the cost of purpose
    (work beyond baseline) equals the holonomy closure work K²/k minus the baseline.

    This connects:
    - Topology: holonomy K (sum of constraints around cycle)
    - Thermodynamics: work K²/k to optimally redistribute
    - Optimization: cost of purpose = departure from baseline needed for optimality
-/
theorem cost_equals_closure_work {n k : ℕ} (X : ConfigSpace n) (c : Cycle n X.graph k)
    (_h_k : 3 ≤ k)
    (h_optimal : V_int X = (cycle_holonomy X c)^2 / k) :
    let K := cycle_holonomy X c
    let baseline := ∑ i : Fin k, (X.constraints (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i))^2
    V_int X - baseline = K^2 / k - baseline := by
  intro K baseline
  rw [h_optimal]

end CostOfPurpose
