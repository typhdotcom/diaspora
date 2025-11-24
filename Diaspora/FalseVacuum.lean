import Diaspora.TopologyDynamics
import Diaspora.Universe
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

set_option maxHeartbeats 500000

namespace DiscreteHodge

open BigOperators

abbrev n_theta : ℕ := 4
@[simp] lemma fin_0 : (0 : Fin n_theta) = ⟨0, by decide⟩ := rfl
@[simp] lemma fin_1 : (1 : Fin n_theta) = ⟨1, by decide⟩ := rfl
@[simp] lemma fin_2 : (2 : Fin n_theta) = ⟨2, by decide⟩ := rfl
@[simp] lemma fin_3 : (3 : Fin n_theta) = ⟨3, by decide⟩ := rfl

def theta_active : Finset (Fin n_theta × Fin n_theta) := {
    (0,1), (1,0), (1,2), (2,1), (2,0), (0,2),
    (1,3), (3,1), (3,2), (2,3)
  }

def theta_graph : DynamicGraph n_theta where
  active_edges := theta_active
  symmetric := by
    intro i j
    simp [theta_active]
    tauto
  no_loops := by
    intro i
    simp [theta_active]
    fin_cases i <;> decide

/-- Constraint field from flux parameters: Ft (trap), Fs (smart), Fa (anchor). -/
def make_sigma (Ft Fs Fa : ℝ) : C1 n_theta := {
  val := fun i j =>
    if (i=1 ∧ j=2) then Ft else if (i=2 ∧ j=1) then -Ft
    else if (i=1 ∧ j=3) then Fs else if (i=3 ∧ j=1) then -Fs
    else if (i=3 ∧ j=2) then Fs else if (i=2 ∧ j=3) then -Fs
    else if (i=0 ∧ j=1) then -Fa else if (i=1 ∧ j=0) then Fa
    else if (i=0 ∧ j=2) then Fa else if (i=2 ∧ j=0) then -Fa
    else 0
  skew := by intro i j; fin_cases i <;> fin_cases j <;> simp
}

/-- Relaxation potential: node 1 lowers by P, node 2 raises by P. -/
noncomputable def make_phi (P : ℝ) : C0 n_theta :=
  fun i =>
    if i = 0 then 0
    else if i = 1 then -P
    else if i = 2 then P
    else 0

lemma greedy_strain_is_flux_sq (Ft Fs Fa : ℝ) (i j : Fin n_theta) :
  edge_strain (fun _ => 0) (make_sigma Ft Fs Fa) i j = ((make_sigma Ft Fs Fa).val i j)^2 := by
  unfold edge_strain d0; simp

/-- Without relaxation, the edge with highest flux has highest strain. -/
theorem quenched_instability (Ft Fs Fa : ℝ)
  (h_trap_dominant : Ft > Fs ∧ Ft > Fa)
  (h_pos : Ft > 0 ∧ Fs > 0 ∧ Fa > 0) :
  let σ := make_sigma Ft Fs Fa
  let ϕ := fun (_ : Fin n_theta) => (0 : ℝ)
  edge_strain ϕ σ 1 2 > edge_strain ϕ σ 1 3 ∧
  edge_strain ϕ σ 1 2 > edge_strain ϕ σ 0 1 := by
  intro σ ϕ
  rw [greedy_strain_is_flux_sq, greedy_strain_is_flux_sq, greedy_strain_is_flux_sq]
  simp only [make_sigma]
  norm_num
  simp
  constructor
  · apply sq_lt_sq.mpr; rw [abs_of_pos h_pos.1, abs_of_pos h_pos.2.1]; exact h_trap_dominant.1
  · apply sq_lt_sq.mpr; rw [abs_of_pos h_pos.1, abs_of_pos h_pos.2.2]; exact h_trap_dominant.2

set_option linter.unusedSimpArgs false in
/-- Relaxation can invert which edge fails first. -/
theorem annealed_crossover (Ft Fs Fa : ℝ) (P : ℝ)
  (h_relax : P = Ft / 2 + 1)
  (h_smart_weak : Fs < P - 2) :
  let σ := make_sigma Ft Fs Fa
  let ϕ := make_phi P
  edge_strain ϕ σ 1 2 < edge_strain ϕ σ 1 3 := by
  intro σ ϕ
  unfold edge_strain d0
  simp only [C1.val]
  have hϕ1 : ϕ 1 = -P := rfl
  have hϕ2 : ϕ 2 = P := rfl
  have hϕ3 : ϕ 3 = 0 := rfl
  have hσ12 : σ.val 1 2 = Ft := rfl
  have hσ13 : σ.val 1 3 = Fs := rfl
  rw [hϕ2, hϕ1, hϕ3, hσ12, hσ13]
  simp only [sub_neg_eq_add, zero_add]
  rw [h_relax]
  have lhs : (Ft / 2 + 1 + (Ft / 2 + 1) - Ft) ^ 2 = 4 := by field_simp; ring
  rw [lhs]
  have : (4:ℝ) = 2^2 := by norm_num
  rw [this, sq_lt_sq]
  rw [abs_of_pos (by norm_num : (2:ℝ) > 0)]
  have h_ineq : Ft / 2 + 1 - Fs > 2 := by
    rw [h_relax] at h_smart_weak
    linarith
  rw [abs_of_pos (by linarith)]
  exact h_ineq

lemma theta_has_12 : (1, 2) ∈ theta_graph.active_edges := by simp [theta_graph, theta_active]
lemma theta_has_13 : (1, 3) ∈ theta_graph.active_edges := by simp [theta_graph, theta_active]

/-- Trap decay: breaking the high-flux edge (1,2). -/
def trap_decay_chain (σ : C1 n_theta) : EvolutionChain n_theta σ (remove_edge theta_graph 1 2) :=
  EvolutionChain.step (EvolutionChain.genesis theta_graph) 1 2 theta_has_12

/-- Smart decay: breaking the lower-flux edge (1,3). -/
def smart_decay_chain (σ : C1 n_theta) : EvolutionChain n_theta σ (remove_edge theta_graph 1 3) :=
  EvolutionChain.step (EvolutionChain.genesis theta_graph) 1 3 theta_has_13

/-- Trap decay releases more latent capacity than smart decay under quenched conditions. -/
theorem quenched_path_preference (Ft Fs Fa : ℝ)
  (h_trap_dominant : Ft > Fs ∧ Ft > Fa)
  (h_pos : Ft > 0 ∧ Fs > 0 ∧ Fa > 0) :
  let σ := make_sigma Ft Fs Fa
  (trap_decay_chain σ).origin = (smart_decay_chain σ).origin ∧
  latent_capacity (remove_edge theta_graph 1 2) σ > latent_capacity (remove_edge theta_graph 1 3) σ := by
  intro σ
  constructor
  · rfl
  · rw [step_entropy_growth 1 2 theta_has_12]
    rw [step_entropy_growth 1 3 theta_has_13]
    simp only [σ, make_sigma]
    norm_num
    apply sq_lt_sq.mpr
    rw [abs_of_pos h_pos.1, abs_of_pos h_pos.2.1]
    exact h_trap_dominant.1

lemma remove_edge_comm (G : DynamicGraph n_theta) (i j : Fin n_theta) :
    remove_edge G i j = remove_edge G j i := by
  simp only [remove_edge, DynamicGraph.mk.injEq]
  ext ⟨a, b⟩
  simp only [Finset.mem_erase, ne_eq, Prod.mk.injEq]
  constructor
  · intro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, h3⟩
    · intro ⟨ha, hb⟩; subst ha hb; exact h2 ⟨rfl, rfl⟩
    · intro ⟨ha, hb⟩; subst ha hb; exact h1 ⟨rfl, rfl⟩
  · intro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, h3⟩
    · intro ⟨ha, hb⟩; subst ha hb; exact h2 ⟨rfl, rfl⟩
    · intro ⟨ha, hb⟩; subst ha hb; exact h1 ⟨rfl, rfl⟩

/-- evolve_step selects the trap edge (1,2) when it has dominant strain. -/
theorem simulation_selects_trap (Ft Fs Fa C_max : ℝ)
  (h_trap_dominant : Ft > Fs ∧ Ft > Fa)
  (h_pos : Ft > 0 ∧ Fs > 0 ∧ Fa > 0)
  (h_break : Ft^2 > C_max) :
  let σ := make_sigma Ft Fs Fa
  let ϕ := fun (_ : Fin n_theta) => (0 : ℝ)
  evolve_step theta_graph ϕ σ C_max = remove_edge theta_graph 1 2 := by
  intro σ ϕ
  have h12_strain : edge_strain ϕ σ 1 2 = Ft^2 := greedy_strain_is_flux_sq Ft Fs Fa 1 2
  have h12_over : edge_strain ϕ σ 1 2 > C_max := by rw [h12_strain]; exact h_break
  unfold evolve_step
  split
  case h_1 i j heq =>
    have h_spec := find_overstressed_edge_spec theta_graph ϕ σ C_max i j heq
    have h_active := h_spec.1
    fin_cases i <;> fin_cases j
    · exfalso; simp only [theta_graph, theta_active, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h_active; simp_all
    · exfalso
      have h01_strain : edge_strain ϕ σ 0 1 = Fa^2 := by simp only [edge_strain, d0]; simp [σ, ϕ, make_sigma]
      have hFt_sq_gt_Fa : Ft^2 > Fa^2 := sq_lt_sq.mpr (by rw [abs_of_pos h_pos.1, abs_of_pos h_pos.2.2]; exact h_trap_dominant.2)
      have h_max := find_overstressed_edge_max theta_graph ϕ σ C_max 0 1 heq 1 2 theta_has_12 h12_over
      rw [h01_strain, h12_strain] at h_max
      linarith
    · exfalso
      have h02_strain : edge_strain ϕ σ 0 2 = Fa^2 := by simp only [edge_strain, d0]; simp [σ, ϕ, make_sigma]
      have hFt_sq_gt_Fa : Ft^2 > Fa^2 := sq_lt_sq.mpr (by rw [abs_of_pos h_pos.1, abs_of_pos h_pos.2.2]; exact h_trap_dominant.2)
      have h_max := find_overstressed_edge_max theta_graph ϕ σ C_max 0 2 heq 1 2 theta_has_12 h12_over
      rw [h02_strain, h12_strain] at h_max
      linarith
    · exfalso; simp only [theta_graph, theta_active, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h_active; simp_all
    · exfalso
      have h10_strain : edge_strain ϕ σ 1 0 = Fa^2 := by simp only [edge_strain, d0]; simp [σ, ϕ, make_sigma]
      have hFt_sq_gt_Fa : Ft^2 > Fa^2 := sq_lt_sq.mpr (by rw [abs_of_pos h_pos.1, abs_of_pos h_pos.2.2]; exact h_trap_dominant.2)
      have h_max := find_overstressed_edge_max theta_graph ϕ σ C_max 1 0 heq 1 2 theta_has_12 h12_over
      rw [h10_strain, h12_strain] at h_max
      linarith
    · exfalso; simp only [theta_graph, theta_active, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h_active; simp_all
    · rfl
    · exfalso
      have h13_strain : edge_strain ϕ σ 1 3 = Fs^2 := by simp only [edge_strain, d0]; simp [σ, ϕ, make_sigma]
      have hFt_sq_gt_Fs : Ft^2 > Fs^2 := sq_lt_sq.mpr (by rw [abs_of_pos h_pos.1, abs_of_pos h_pos.2.1]; exact h_trap_dominant.1)
      have h_max := find_overstressed_edge_max theta_graph ϕ σ C_max 1 3 heq 1 2 theta_has_12 h12_over
      rw [h13_strain, h12_strain] at h_max
      linarith
    · exfalso
      have h20_strain : edge_strain ϕ σ 2 0 = Fa^2 := by simp only [edge_strain, d0]; simp [σ, ϕ, make_sigma]
      have hFt_sq_gt_Fa : Ft^2 > Fa^2 := sq_lt_sq.mpr (by rw [abs_of_pos h_pos.1, abs_of_pos h_pos.2.2]; exact h_trap_dominant.2)
      have h_max := find_overstressed_edge_max theta_graph ϕ σ C_max 2 0 heq 1 2 theta_has_12 h12_over
      rw [h20_strain, h12_strain] at h_max
      linarith
    · exact remove_edge_comm theta_graph 1 2
    · exfalso; simp only [theta_graph, theta_active, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h_active; simp_all
    · exfalso
      have h23_strain : edge_strain ϕ σ 2 3 = Fs^2 := by simp only [edge_strain, d0]; simp [σ, ϕ, make_sigma]
      have hFt_sq_gt_Fs : Ft^2 > Fs^2 := sq_lt_sq.mpr (by rw [abs_of_pos h_pos.1, abs_of_pos h_pos.2.1]; exact h_trap_dominant.1)
      have h_max := find_overstressed_edge_max theta_graph ϕ σ C_max 2 3 heq 1 2 theta_has_12 h12_over
      rw [h23_strain, h12_strain] at h_max
      linarith
    · exfalso; simp only [theta_graph, theta_active, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h_active; simp_all
    · exfalso
      have h31_strain : edge_strain ϕ σ 3 1 = Fs^2 := by simp only [edge_strain, d0]; simp [σ, ϕ, make_sigma]
      have hFt_sq_gt_Fs : Ft^2 > Fs^2 := sq_lt_sq.mpr (by rw [abs_of_pos h_pos.1, abs_of_pos h_pos.2.1]; exact h_trap_dominant.1)
      have h_max := find_overstressed_edge_max theta_graph ϕ σ C_max 3 1 heq 1 2 theta_has_12 h12_over
      rw [h31_strain, h12_strain] at h_max
      linarith
    · exfalso
      have h32_strain : edge_strain ϕ σ 3 2 = Fs^2 := by simp only [edge_strain, d0]; simp [σ, ϕ, make_sigma]
      have hFt_sq_gt_Fs : Ft^2 > Fs^2 := sq_lt_sq.mpr (by rw [abs_of_pos h_pos.1, abs_of_pos h_pos.2.1]; exact h_trap_dominant.1)
      have h_max := find_overstressed_edge_max theta_graph ϕ σ C_max 3 2 heq 1 2 theta_has_12 h12_over
      rw [h32_strain, h12_strain] at h_max
      linarith
    · exfalso; simp only [theta_graph, theta_active, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h_active; simp_all
  case h_2 heq =>
    exfalso
    unfold find_overstressed_edge at heq
    have h12_active : (1, 2) ∈ theta_graph.active_edges := theta_has_12
    have h12_in_filter : (1, 2) ∈ List.filter (fun x => decide (edge_strain ϕ σ x.1 x.2 > C_max)) theta_graph.active_edges.toList := by
      simp only [List.mem_filter, Finset.mem_toList]
      exact ⟨h12_active, by simp only [decide_eq_true_iff]; exact h12_over⟩
    have h_ne : List.filter (fun x => decide (edge_strain ϕ σ x.1 x.2 > C_max)) theta_graph.active_edges.toList ≠ [] :=
      List.ne_nil_of_mem h12_in_filter
    simp only [select_max_strain] at heq
    cases h_list : List.filter (fun x => decide (edge_strain ϕ σ x.1 x.2 > C_max)) theta_graph.active_edges.toList with
    | nil => exact h_ne h_list
    | cons hd tl =>
      rw [h_list] at heq
      simp only [List.foldl_cons, select_max_strain_fn] at heq
      have h_isSome : (List.foldl (select_max_strain_fn ϕ σ) (some hd) tl).isSome := by
        clear heq h_list h_ne h12_in_filter h12_active h12_over h12_strain h_break h_pos h_trap_dominant
        induction tl generalizing hd with
        | nil => simp
        | cons h t ih =>
          simp only [List.foldl_cons]
          have h_step : ∃ x, select_max_strain_fn ϕ σ (some hd) h = some x := by
            simp only [select_max_strain_fn]; split_ifs <;> exact ⟨_, rfl⟩
          obtain ⟨x, hx⟩ := h_step; rw [hx]; exact ih x
      rw [heq] at h_isSome; simp at h_isSome

end DiscreteHodge
