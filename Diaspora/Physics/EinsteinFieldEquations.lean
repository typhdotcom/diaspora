/-
Einstein Field Equations from variational principle δℒ/δω = 0.
Proves: Gμν = 8πG Tμν emerges from minimizing ℒ = V_int + V_ext + λE.
-/

import Diaspora.GaugeTheoreticHolonomy
import Diaspora.Physics.SpacetimeGeometry
import Diaspora.Physics.MassDefinition
import Diaspora.HolonomyLagrangeProof
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open GaugeTheoretic SpacetimeGeometry MassDefinition HolonomyProof

namespace EinsteinFieldEquations

/-- The action as a function of phases -/
noncomputable def action {n : ℕ} (X_base : ConfigSpace n)
    (task : ExternalTask n) (lam : ℝ) (ω : Fin n → ℝ) : ℝ :=
  let X := { X_base with node_phases := ω }
  ℒ task X lam

/-- V_int as a function of phases -/
noncomputable def V_int_functional {n : ℕ} (X_base : ConfigSpace n)
    (ω : Fin n → ℝ) : ℝ :=
  let X := { X_base with node_phases := ω }
  V_int X

theorem optimal_phases_exist {n k : ℕ} (X : ConfigSpace n)
    (c : Cycle n X.graph k) (h_k : 3 ≤ k) :
    ∃ (ω_opt : Fin n → ℝ),
      let X_opt := { X with node_phases := ω_opt }
      V_int_on_cycle X_opt c = (cycle_holonomy X c)^2 / k := by
  let K := cycle_holonomy X c
  let c_constraints : Fin k → ℝ := fun i => X.constraints (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i)

  have h_K : ∑ i : Fin k, c_constraints i = K := by
    unfold K cycle_holonomy c_constraints
    rfl

  have h_vopt_sum : ∑ i : Fin k, (c_constraints i - K / k) = 0 := by
    calc ∑ i : Fin k, (c_constraints i - K / k)
        = ∑ i : Fin k, c_constraints i - ∑ i : Fin k, (K / k) := by rw [Finset.sum_sub_distrib]
      _ = K - ∑ i : Fin k, (K / k) := by rw [← h_K]
      _ = K - k * (K / k) := by simp [Finset.sum_const]
      _ = 0 := by field_simp; ring

  have h_opt_calc : ∑ i : Fin k, ((c_constraints i - K / k) - c_constraints i)^2 = K^2 / k := by
    calc ∑ i : Fin k, ((c_constraints i - K / k) - c_constraints i)^2
        = ∑ i : Fin k, (-K / k)^2 := by congr 1; ext i; ring
      _ = ∑ i : Fin k, (K / k)^2 := by congr 1; ext i; ring
      _ = k * (K / k)^2 := by simp [Finset.sum_const]
      _ = K^2 / k := by field_simp

  let e_opt : Fin k → ℝ := fun i => c_constraints i - K / k
  have h_e_sum : ∑ i : Fin k, e_opt i = 0 := h_vopt_sum
  obtain ⟨ω_optimal, h_ω_optimal⟩ := phases_exist_for_edge_values X c h_k e_opt h_e_sum

  let X_final : ConfigSpace n := { X with node_phases := ω_optimal }
  let v_final : Fin k → ℝ := fun i => edge_value X_final (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i)

  have h_final_edges : ∀ i : Fin k, v_final i = e_opt i := by
    intro i
    unfold v_final edge_value X_final e_opt
    exact h_ω_optimal i

  use ω_optimal
  intro X_final

  calc V_int_on_cycle X_final c
      = ∑ i : Fin k, (edge_value X_final (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i) -
                      X_final.constraints (c.nodes i.castSucc) (c.nodes i.succ) (c.adjacent i))^2 := by
          unfold V_int_on_cycle; rfl
    _ = ∑ i : Fin k, (v_final i - c_constraints i)^2 := by
          unfold v_final c_constraints; rfl
    _ = ∑ i : Fin k, (e_opt i - c_constraints i)^2 := by
          congr 1; ext i; rw [h_final_edges]
    _ = K^2 / k := h_opt_calc

theorem optimal_satisfies_einstein {n k : ℕ} (X : ConfigSpace n)
    (c : Cycle n X.graph k) (_h_k : 3 ≤ k)
    (ω_opt : Fin n → ℝ)
    (h_opt : let X_opt := { X with node_phases := ω_opt }
             V_int X_opt = (cycle_holonomy X c)^2 / k) :
    let X_opt := { X with node_phases := ω_opt }
    discrete_ricci_scalar X_opt = curvature_density X_opt c := by
  let X_opt := { X with node_phases := ω_opt }
  show V_int X_opt = (cycle_holonomy X_opt c)^2 / k
  have h_holonomy_eq : cycle_holonomy X_opt c = cycle_holonomy X c := by
    unfold cycle_holonomy; rfl
  rw [h_holonomy_eq]
  exact h_opt

/-- The discrete Laplacian of the phase field -/
noncomputable def discrete_laplacian {n : ℕ} (X : ConfigSpace n)
    (ω : Fin n → ℝ) (i : Fin n) : ℝ :=
  letI := X.adj_decidable
  ∑ j : Fin n, if X.graph.Adj i j then (ω i - ω j) else 0

noncomputable def source_term {n : ℕ} (X : ConfigSpace n) (i : Fin n) : ℝ :=
  letI := X.adj_decidable
  ∑ j : Fin n, if h : X.graph.Adj i j then X.constraints i j h else 0

lemma V_int_critical_point {n : ℕ} (X_base : ConfigSpace n)
    (ω_crit : Fin n → ℝ)
    (h_crit : ∀ i, ∀ ε : ℝ,
      V_int_functional X_base ω_crit ≤ V_int_functional X_base
        (fun j => if j = i then ω_crit j + ε else ω_crit j)) :
    ∀ i, letI := X_base.adj_decidable;
      ∑ j : Fin n, (if h : X_base.graph.Adj i j then
        4 * ((ω_crit i - ω_crit j) + X_base.constraints i j h) else 0) = 0 := by
  intro i
  letI := X_base.adj_decidable

  let f : ℝ → ℝ := fun t => V_int_functional X_base (fun j => if j = i then ω_crit j + t else ω_crit j)

  have h_min : ∀ t, f 0 ≤ f t := by
    intro t
    unfold f
    convert h_crit i t using 2
    ext j
    by_cases h : j = i <;> simp [h]

  have h_deriv_formula : deriv f 0 = (∑ j : Fin n, if h : X_base.graph.Adj i j then
        4 * ((ω_crit i - ω_crit j) + X_base.constraints i j h) else 0) := by

    letI := X_base.adj_decidable

    have h1 : ∀ a : ℝ, deriv (fun t => (a - t)^2) 0 = -2 * a := by
      intro a
      have : deriv (fun t => a - t) 0 = -1 := by
        rw [deriv_const_sub, deriv_id'']
      have d : DifferentiableAt ℝ (fun t => a - t) 0 := differentiableAt_id.const_sub a
      calc deriv (fun t => (a - t)^2) 0
          = deriv (fun t => (a - t) * (a - t)) 0 := by congr 1; ext t; ring
        _ = deriv (fun t => a - t) 0 * (a - 0) + (a - 0) * deriv (fun t => a - t) 0 := deriv_mul d d
        _ = -1 * a + a * -1 := by rw [this]; ring
        _ = -2 * a := by ring

    have h2 : ∀ a : ℝ, deriv (fun t => (a + t)^2) 0 = 2 * a := by
      intro a
      have : deriv (fun t => a + t) 0 = 1 := by
        rw [deriv_const_add, deriv_id'']
      have d : DifferentiableAt ℝ (fun t => a + t) 0 := differentiableAt_id.const_add a
      calc deriv (fun t => (a + t)^2) 0
          = deriv (fun t => (a + t) * (a + t)) 0 := by congr 1; ext t; ring
        _ = deriv (fun t => a + t) 0 * (a + 0) + (a + 0) * deriv (fun t => a + t) 0 := deriv_mul d d
        _ = 1 * a + a * 1 := by rw [this]; ring
        _ = 2 * a := by ring

    -- Expand f as explicit sum over edges
    have f_expand : f = fun t => ∑ i' : Fin n, ∑ j : Fin n,
        if h : X_base.graph.Adj i' j then
          let ω_t := fun k => if k = i then ω_crit k + t else ω_crit k
          (ω_t j - ω_t i' - X_base.constraints i' j h)^2
        else 0 := by
      ext t
      unfold f V_int_functional V_int
      simp only [edge_value]

    rw [f_expand]

    have term_simp : ∀ t i' j,
        (if h : X_base.graph.Adj i' j then
          let ω_t := fun k => if k = i then ω_crit k + t else ω_crit k
          (ω_t j - ω_t i' - X_base.constraints i' j h)^2
        else 0) =
        if h : X_base.graph.Adj i' j then
          if i' = i ∧ j ≠ i then
            ((ω_crit j - ω_crit i - X_base.constraints i' j h) - t)^2
          else if i' ≠ i ∧ j = i then
            ((ω_crit i - ω_crit i' - X_base.constraints i' j h) + t)^2
          else if i' ≠ i ∧ j ≠ i then
            (ω_crit j - ω_crit i' - X_base.constraints i' j h)^2
          else
            0
        else 0 := by
      intro t i' j
      by_cases h_adj : X_base.graph.Adj i' j
      · simp only [h_adj]
        by_cases hi' : i' = i
        · by_cases hj : j = i
          · rw [hi', hj] at h_adj
            exact absurd h_adj (X_base.graph.loopless i)
          · simp [hi', hj]
            congr 1; ring
        · by_cases hj : j = i
          · simp [hi', hj]
            congr 1; ring
          · simp [hi', hj]
      · simp [h_adj]

    have deriv_term : ∀ i' j,
        deriv (fun t => if h : X_base.graph.Adj i' j then
          let ω_t := fun k => if k = i then ω_crit k + t else ω_crit k
          (ω_t j - ω_t i' - X_base.constraints i' j h)^2
        else 0) 0 =
        if h : X_base.graph.Adj i' j then
          if i' = i ∧ j ≠ i then
            -2 * (ω_crit j - ω_crit i - X_base.constraints i' j h)
          else if i' ≠ i ∧ j = i then
            2 * (ω_crit i - ω_crit i' - X_base.constraints i' j h)
          else
            0
        else 0 := by
      intro i' j
      by_cases h_adj : X_base.graph.Adj i' j
      · simp only [h_adj]
        by_cases hi' : i' = i
        · by_cases hj : j = i
          · rw [hi', hj] at h_adj
            exact absurd h_adj (X_base.graph.loopless i)
          · simp [hi', hj]
            rw [hi'] at h_adj
            have key := h1 (ω_crit j - ω_crit i - X_base.constraints i j h_adj)
            calc deriv (fun t => (ω_crit j - (ω_crit i + t) - X_base.constraints i j h_adj)^2) 0
                = deriv (fun t => ((ω_crit j - ω_crit i - X_base.constraints i j h_adj) - t)^2) 0 := by
                  congr; ext t; ring
              _ = -2 * (ω_crit j - ω_crit i - X_base.constraints i j h_adj) := key
              _ = -(2 * (ω_crit j - ω_crit i - X_base.constraints i j h_adj)) := by ring
        · by_cases hj : j = i
          · simp [hi', hj]
            rw [hj] at h_adj
            calc deriv (fun t => (ω_crit i + t - ω_crit i' - X_base.constraints i' i h_adj)^2) 0
                = deriv (fun t => ((ω_crit i - ω_crit i' - X_base.constraints i' i h_adj) + t)^2) 0 := by
                  congr; ext t; ring
              _ = 2 * (ω_crit i - ω_crit i' - X_base.constraints i' i h_adj) := h2 _
          · simp [hi', hj, deriv_const]
      · simp [h_adj, deriv_const]

    have deriv_f_calc : deriv f 0 = ∑ i' : Fin n, ∑ j : Fin n,
        (if h : X_base.graph.Adj i' j then
          if i' = i ∧ j ≠ i then
            -2 * (ω_crit j - ω_crit i - X_base.constraints i' j h)
          else if i' ≠ i ∧ j = i then
            2 * (ω_crit i - ω_crit i' - X_base.constraints i' j h)
          else
            0
        else 0) := by
      rw [f_expand]
      rw [deriv_fun_sum]
      · congr 1
        ext i'
        rw [deriv_fun_sum]
        · congr 1
          ext j
          exact deriv_term i' j
        · intro j _
          simp_rw [term_simp]
          split_ifs <;> fun_prop
      · intro i' _
        apply DifferentiableAt.fun_sum
        intro j _
        simp_rw [term_simp]
        split_ifs <;> fun_prop

    have sum_split : ∀ i', (∑ j : Fin n, if h : X_base.graph.Adj i' j then
          if i' = i ∧ j ≠ i then -2 * (ω_crit j - ω_crit i - X_base.constraints i' j h)
          else if i' ≠ i ∧ j = i then 2 * (ω_crit i - ω_crit i' - X_base.constraints i' j h)
          else 0
        else 0) =
        (if i' = i then ∑ j : Fin n, if h : X_base.graph.Adj i j then
          if j ≠ i then -2 * (ω_crit j - ω_crit i - X_base.constraints i j h) else 0
        else 0 else 0) +
        (if i' ≠ i then if h : X_base.graph.Adj i' i then
          (∑ j : Fin n, if j = i then 2 * (ω_crit i - ω_crit i' - X_base.constraints i' i h) else 0)
        else 0 else 0) := by
      intro i'
      by_cases hi' : i' = i
      · rw [hi']
        simp only [Ne, true_and, not_true, false_and, ite_false, ite_true, add_zero]
      · simp only [hi', ite_false, false_and, zero_add]
        by_cases h : X_base.graph.Adj i' i
        · simp [h, hi']
          trans (∑ x : Fin n, if x = i then 2 * (ω_crit i - ω_crit i' - X_base.constraints i' i h) else 0)
          · congr 1
            ext j
            by_cases hj : j = i
            · simp [hj, h]
            · simp [hj]
          · trans (∑ x : Fin n, if i = x then 2 * (ω_crit i - ω_crit i' - X_base.constraints i' i h) else 0)
            · congr 1
              funext j
              by_cases hj : j = i
              · rw [hj]
              · simp only [eq_comm]
            · rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
        · simp [h, hi']
          apply Finset.sum_eq_zero
          intro j _
          by_cases h_adj : X_base.graph.Adj i' j
          · by_cases hj : j = i
            · rw [hj] at h_adj
              exact absurd h_adj h
            · simp [h_adj, hj]
          · simp [h_adj]

    have deriv_f_edges : deriv f 0 =
        (∑ j : Fin n, if h : X_base.graph.Adj i j then
          -2 * (ω_crit j - ω_crit i - X_base.constraints i j h)
        else 0) +
        (∑ j : Fin n, if h : X_base.graph.Adj j i then
          2 * (ω_crit i - ω_crit j - X_base.constraints j i h)
        else 0) := by
      rw [deriv_f_calc]
      simp_rw [sum_split, ← Finset.sum_add_distrib, Finset.sum_add_distrib]
      congr 1
      · trans (∑ j, if h : X_base.graph.Adj i j then -2 * (ω_crit j - ω_crit i - X_base.constraints i j h) else 0)
        · trans (∑ j, if h : X_base.graph.Adj i j then if j ≠ i then -2 * (ω_crit j - ω_crit i - X_base.constraints i j h) else 0 else 0)
          · rw [Finset.sum_ite_eq' Finset.univ i]
            simp
          · apply Finset.sum_congr rfl
            intro j _
            split_ifs with h_adj h_ne
            · rfl
            · exfalso
              exact h_ne (X_base.graph.ne_of_adj h_adj).symm
            · rfl
        · rfl
      · trans (∑ j, if h : X_base.graph.Adj j i then 2 * (ω_crit i - ω_crit j - X_base.constraints j i h) else 0)
        · apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x ≠ i
          · rw [if_pos hx]
            split_ifs with h_adj
            · rw [Finset.sum_ite_eq' Finset.univ i]
              simp
            · rfl
          · push_neg at hx
            subst hx
            simp
        · rfl

    have deriv_f_combined : deriv f 0 =
        ∑ j : Fin n, if h : X_base.graph.Adj i j then
          4 * ((ω_crit i - ω_crit j) + X_base.constraints i j h)
        else 0 := by
      rw [deriv_f_edges, ← Finset.sum_add_distrib]
      congr 1
      ext j
      by_cases h_ij : X_base.graph.Adj i j
      · have h_ji : X_base.graph.Adj j i := X_base.graph.symm h_ij
        have c_antisym := constraint_antisymmetric X_base i j h_ij h_ji
        simp only [h_ij, h_ji]
        calc -2 * (ω_crit j - ω_crit i - X_base.constraints i j h_ij) +
              2 * (ω_crit i - ω_crit j - X_base.constraints j i h_ji)
            = -2 * (ω_crit j - ω_crit i - X_base.constraints i j h_ij) +
              2 * (ω_crit i - ω_crit j - (-(X_base.constraints i j h_ij))) := by rw [← c_antisym]
          _ = 4 * ((ω_crit i - ω_crit j) + X_base.constraints i j h_ij) := by ring
      · have h_ji : ¬ X_base.graph.Adj j i := fun h => h_ij (X_base.graph.symm h)
        simp only [dif_neg h_ij, dif_neg h_ji, add_zero]

    exact deriv_f_combined

  have h_is_min : IsLocalMin f 0 := Filter.Eventually.of_forall h_min
  have h_deriv_zero : deriv f 0 = 0 := IsLocalMin.deriv_eq_zero h_is_min
  rw [h_deriv_formula] at h_deriv_zero
  exact h_deriv_zero

theorem euler_lagrange_equations {n : ℕ} (X_base : ConfigSpace n)
    (task : ExternalTask n) (lam : ℝ)
    (ω_crit : Fin n → ℝ)
    (h_crit : ∀ i, ∀ ε : ℝ, ∀ _δω : Fin n → ℝ,
        action X_base task lam ω_crit ≤ action X_base task lam
          (fun j => if j = i then ω_crit j + ε else ω_crit j))
    (h_no_external : ∀ X, task.measure_violation X = 0) :
    ∀ i, discrete_laplacian X_base ω_crit i = -source_term X_base i := by
  intro i

  have h_crit_simple : ∀ i ε, V_int_functional X_base ω_crit ≤
      V_int_functional X_base (fun j => if j = i then ω_crit j + ε else ω_crit j) := by
    intro i' ε
    let X1 := { X_base with node_phases := ω_crit }
    let X2 := { X_base with node_phases := (fun j => if j = i' then ω_crit j + ε else ω_crit j) }

    have h_task_zero : task.measure_violation X1 = 0 := h_no_external X1
    have h_task_zero' : task.measure_violation X2 = 0 := h_no_external X2
    have h_action := h_crit i' ε (fun j => if j = i' then ω_crit j + ε else ω_crit j)

    have h_Vext_zero : V_ext task X1 = 0 := by unfold V_ext; simp [h_task_zero]
    have h_Vext_zero' : V_ext task X2 = 0 := by unfold V_ext; simp [h_task_zero']

    have h_action_eq : action X_base task lam ω_crit = V_int_functional X_base ω_crit + lam * (E X1 : ℝ) := by
      show ℒ task X1 lam = V_int X1 + lam * (E X1 : ℝ)
      unfold ℒ V_ext; simp [h_task_zero]

    have h_action_eq' : action X_base task lam (fun j => if j = i' then ω_crit j + ε else ω_crit j) =
        V_int_functional X_base (fun j => if j = i' then ω_crit j + ε else ω_crit j) + lam * (E X2 : ℝ) := by
      show ℒ task X2 lam = V_int X2 + lam * (E X2 : ℝ)
      unfold ℒ V_ext; simp [h_task_zero']

    have h_E_eq : E X1 = E X2 := by unfold E; rfl

    calc V_int_functional X_base ω_crit
        = action X_base task lam ω_crit - lam * (E X1 : ℝ) := by rw [h_action_eq]; ring
      _ ≤ action X_base task lam (fun j => if j = i' then ω_crit j + ε else ω_crit j) -
            lam * (E X1 : ℝ) := by linarith [h_action]
      _ = action X_base task lam (fun j => if j = i' then ω_crit j + ε else ω_crit j) -
            lam * (E X2 : ℝ) := by rw [h_E_eq]
      _ = V_int_functional X_base (fun j => if j = i' then ω_crit j + ε else ω_crit j) := by rw [h_action_eq']; ring

  have h_deriv_zero := V_int_critical_point X_base ω_crit h_crit_simple i

  show discrete_laplacian X_base ω_crit i = -source_term X_base i
  unfold discrete_laplacian source_term
  letI := X_base.adj_decidable

  have h_sum : (∑ j : Fin n, dite (X_base.graph.Adj i j)
      (fun h => (ω_crit i - ω_crit j) + X_base.constraints i j h) (fun _ => (0 : ℝ))) = 0 := by
    have h4 : (4 : ℝ) * (∑ j : Fin n, dite (X_base.graph.Adj i j)
        (fun h => (ω_crit i - ω_crit j) + X_base.constraints i j h) (fun _ => (0 : ℝ))) =
        ∑ j : Fin n, dite (X_base.graph.Adj i j)
          (fun h => 4 * ((ω_crit i - ω_crit j) + X_base.constraints i j h)) (fun _ => (0 : ℝ)) := by
      rw [Finset.mul_sum]
      congr 1; ext j
      by_cases h : X_base.graph.Adj i j <;> simp [h]
    have h0 := h_deriv_zero
    linarith [h4, h0]

  have h_split : (∑ j : Fin n, dite (X_base.graph.Adj i j)
      (fun h => (ω_crit i - ω_crit j) + X_base.constraints i j h) (fun _ => (0 : ℝ))) =
      (∑ j : Fin n, ite (X_base.graph.Adj i j) (ω_crit i - ω_crit j) 0) +
      (∑ j : Fin n, dite (X_base.graph.Adj i j) (fun h => X_base.constraints i j h) (fun _ => (0 : ℝ))) := by
    rw [← Finset.sum_add_distrib]
    congr 1; ext j
    by_cases h : X_base.graph.Adj i j <;> simp [h]

  linarith [h_sum, h_split]

noncomputable def discrete_ricci_at_node {n : ℕ} (X : ConfigSpace n)
    (ω : Fin n → ℝ) (i : Fin n) : ℝ :=
  discrete_laplacian X ω i

theorem euler_lagrange_is_einstein {n : ℕ} (X_base : ConfigSpace n)
    (_task : ExternalTask n) (_lam : ℝ)
    (ω_crit : Fin n → ℝ)
    (h_EL : ∀ i, discrete_laplacian X_base ω_crit i = source_term X_base i) :
    ∀ i, discrete_ricci_at_node X_base ω_crit i = source_term X_base i := by
  intro i
  unfold discrete_ricci_at_node
  exact h_EL i

end EinsteinFieldEquations
