/-
Spacetime geometry from ConfigSpace: correspondence with Riemannian geometry.
-/

import Diaspora.GaugeTheoreticHolonomy
import Diaspora.MassDefinition
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.Instances.Real

open GaugeTheoretic MassDefinition

namespace SpacetimeGeometry

/-- Discrete metric: assigns a length to each edge based on constraint. -/
noncomputable def discrete_metric {n : ℕ} (X : ConfigSpace n)
    (i j : Fin n) (h : X.graph.Adj i j) : ℝ :=
  |edge_value X i j h - X.constraints i j h|

/-- Induced distance between nodes. -/
noncomputable def induced_distance {n : ℕ} (X : ConfigSpace n)
    (i j : Fin n) (h : X.graph.Adj i j) : ℝ :=
  (discrete_metric X i j h)^2

/-- Discrete metric is non-negative. -/
theorem discrete_metric_nonneg {n : ℕ} (X : ConfigSpace n)
    (i j : Fin n) (h : X.graph.Adj i j) :
    0 ≤ discrete_metric X i j h := by
  unfold discrete_metric
  exact abs_nonneg _

/-- Induced distance equals squared metric deviation. -/
theorem induced_distance_eq {n : ℕ} (X : ConfigSpace n)
    (i j : Fin n) (h : X.graph.Adj i j) :
    induced_distance X i j h = (edge_value X i j h - X.constraints i j h)^2 := by
  unfold induced_distance discrete_metric
  exact sq_abs _

theorem V_int_is_sum_of_distances {n : ℕ} (X : ConfigSpace n) :
    haveI := X.adj_decidable
    V_int X = ∑ i : Fin n, ∑ j : Fin n,
      if h : X.graph.Adj i j then induced_distance X i j h else 0 := by
  unfold V_int induced_distance discrete_metric
  congr 1
  ext i
  congr 1
  ext j
  by_cases h : X.graph.Adj i j
  · simp only [h, dite_true]
    rw [sq_abs]
  · simp only [h, dite_false]

/-- Curvature density on a cycle. -/
noncomputable def curvature_density {n k : ℕ} (X : ConfigSpace n)
    (c : Cycle n X.graph k) : ℝ :=
  (cycle_holonomy X c)^2 / k

/-- Curvature density is bounded by V_int. -/
theorem curvature_is_minimal_V_int {n k : ℕ} (X : ConfigSpace n)
    (c : Cycle n X.graph k) (h_k : 3 ≤ k) :
    curvature_density X c ≤ V_int X := by
  unfold curvature_density
  exact V_int_lower_bound X c h_k

/-- Discrete Ricci scalar: total curvature. -/
noncomputable def discrete_ricci_scalar {n : ℕ} (X : ConfigSpace n) : ℝ :=
  V_int X

/-- Ricci scalar bounded for single-cycle configuration. -/
theorem ricci_scalar_single_cycle {n k : ℕ} (X : ConfigSpace n)
    (c : Cycle n X.graph k) (h_k : 3 ≤ k)
    (_h_single : (E X : ℝ) = k) :
    (cycle_holonomy X c)^2 / k ≤ discrete_ricci_scalar X := by
  unfold discrete_ricci_scalar
  exact V_int_lower_bound X c h_k

/-- Discrete stress-energy: constraint value on each edge. -/
noncomputable def discrete_stress_energy {n : ℕ} (X : ConfigSpace n)
    (i j : Fin n) (h : X.graph.Adj i j) : ℝ :=
  X.constraints i j h

/-- Total energy equals cycle holonomy. -/
theorem total_energy_is_mass {n k : ℕ} (X : ConfigSpace n)
    (c : Cycle n X.graph k) :
    (∑ i : Fin k, discrete_stress_energy X (c.nodes i.castSucc) (c.nodes i.succ)
      (c.adjacent i)) = cycle_holonomy X c := by
  unfold discrete_stress_energy cycle_holonomy
  rfl

/-- Total energy equals mass. -/
theorem total_energy_equals_mass {n k : ℕ} (X : ConfigSpace n)
    (c : Cycle n X.graph k) :
    cycle_holonomy X c = mass X c := by
  unfold mass
  rfl

/-- Discrete Einstein equation: V_int = K²/k at optimality. -/
theorem discrete_einstein_equation {n k : ℕ} (X : ConfigSpace n)
    (c : Cycle n X.graph k) (h_k : 3 ≤ k) :
    (∃ (X_opt : ConfigSpace n) (c_opt : Cycle n X_opt.graph k),
      (X_opt.graph = X.graph) ∧
      V_int_on_cycle X_opt c_opt = (cycle_holonomy X_opt c_opt)^2 / k) := by
  let K := cycle_holonomy X c
  let c_constraints : Fin k → ℝ := fun i => X.constraints (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i)

  have h_opt : ∃ (e_opt : Fin k → ℝ),
      (∑ i : Fin k, e_opt i = 0) ∧
      (∑ i : Fin k, (e_opt i - c_constraints i)^2 = K^2 / k) := by
    use fun i => c_constraints i - K / k
    constructor
    · calc ∑ i : Fin k, (c_constraints i - K / k)
          = ∑ i : Fin k, c_constraints i - ∑ i : Fin k, (K / k) := by rw [Finset.sum_sub_distrib]
        _ = K - k * (K / k) := by simp [Finset.sum_const]; rfl
        _ = 0 := by field_simp; ring
    · calc ∑ i : Fin k, ((c_constraints i - K / k) - c_constraints i)^2
          = ∑ i : Fin k, (-K / k)^2 := by congr 1; ext i; ring
        _ = ∑ i : Fin k, (K / k)^2 := by congr 1; ext i; ring
        _ = k * (K / k)^2 := by simp [Finset.sum_const]
        _ = K^2 / k := by field_simp

  obtain ⟨e_opt, h_sum_zero, h_achieves_bound⟩ := h_opt
  obtain ⟨ω_optimal, h_ω_optimal⟩ := phases_exist_for_edge_values X c h_k e_opt h_sum_zero

  let X_opt := { X with node_phases := ω_optimal }
  let c_opt := c
  use X_opt, c_opt

  constructor
  · rfl
  · unfold V_int_on_cycle
    calc ∑ i : Fin k, (edge_value X_opt (c_opt.nodes i.castSucc) (c_opt.nodes i.succ) (c_opt.adjacent i) -
                      X_opt.constraints (c_opt.nodes i.castSucc) (c_opt.nodes i.succ) (c_opt.adjacent i))^2
        = ∑ i : Fin k, (e_opt i - c_constraints i)^2 := by
            congr 1; ext i
            simp only [edge_value]
            rw [h_ω_optimal i]
      _ = K^2 / k := h_achieves_bound
      _ = (cycle_holonomy X_opt c_opt)^2 / k := by
            have : cycle_holonomy X_opt c_opt = K := by
              unfold cycle_holonomy K
              rfl
            rw [this]

end SpacetimeGeometry
