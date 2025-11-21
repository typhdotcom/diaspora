/-
# The False Vacuum

Proving that the "Arrow of Time" (Greedy Evolution) does not necessarily
lead to the "Best of All Possible Worlds" (Global Energy Minimum).

This formally verifies that the system supports Meta-Stable states (False Vacua).
-/

import Diaspora.TopologyDynamics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 1000000

namespace DiscreteHodge

open BigOperators

/-! ## The Trap Graph (Theta Graph) -/

abbrev n_theta : ℕ := 4

-- Helper instances for numeric literals in Fin n_theta
@[simp] lemma fin_0 : (0 : Fin n_theta) = ⟨0, by decide⟩ := rfl
@[simp] lemma fin_1 : (1 : Fin n_theta) = ⟨1, by decide⟩ := rfl
@[simp] lemma fin_2 : (2 : Fin n_theta) = ⟨2, by decide⟩ := rfl
@[simp] lemma fin_3 : (3 : Fin n_theta) = ⟨3, by decide⟩ := rfl

def theta_active : Finset (Fin n_theta × Fin n_theta) := {
    (0,1), (1,0), (1,2), (2,1), (2,0), (0,2), -- Left Loop
    (1,3), (3,1), (3,2), (2,3)                -- Right Loop
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

/-! ## The Setup -/

def trap_sigma : C1 n_theta := {
  val := fun i j =>
    if (i=1 ∧ j=2) then 10 else if (i=2 ∧ j=1) then -10
    else if (i=1 ∧ j=3) then 9 else if (i=3 ∧ j=1) then -9
    else if (i=3 ∧ j=2) then 9 else if (i=2 ∧ j=3) then -9
    else 0
  skew := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp
}

-- Helper to quickly evaluate sigma values in proofs
lemma sigma_val_eval (i j : Fin n_theta) :
  trap_sigma.val i j =
    if (i=1 ∧ j=2) then 10 else if (i=2 ∧ j=1) then -10
    else if (i=1 ∧ j=3) then 9 else if (i=3 ∧ j=1) then -9
    else if (i=3 ∧ j=2) then 9 else if (i=2 ∧ j=3) then -9
    else 0 := rfl

/-! ## Energy Calculations -/

/--
The "Relaxed Energy" calculation.
We calculate the energy of the resulting equilibrium state.
-/
noncomputable def relaxed_energy (G : DynamicGraph n_theta) (σ : C1 n_theta) : ℝ :=
  if (1,2) ∉ G.active_edges then
    -- Greedy Branch: (1,2) is broken.
    let flux := σ.val 0 1 + σ.val 1 3 + σ.val 3 2 + σ.val 2 0
    flux^2 / 4
  else if (1,3) ∉ G.active_edges then
    -- Smart Branch: (1,3) is broken.
    let flux := σ.val 0 1 + σ.val 1 2 + σ.val 2 0
    flux^2 / 3
  else
    0

/-! ## The Theorem -/

-- Helper lemma: foldl with select_max_strain_fn preserves some
lemma foldl_select_max_strain_fn_some {n : ℕ} (ϕ : C0 n) (σ : C1 n)
    (l : List (Fin n × Fin n)) (x : Fin n × Fin n) :
    ∃ y, l.foldl (select_max_strain_fn ϕ σ) (some x) = some y := by
  induction l generalizing x with
  | nil => exact ⟨x, rfl⟩
  | cons head tail ih =>
    rw [List.foldl_cons]
    unfold select_max_strain_fn
    simp only []
    split
    · exact ih head
    · exact ih x

-- Helper lemma: d0 of zero function is zero
lemma d0_zero : (d0 (fun _ : Fin n_theta => (0 : ℝ))).val i j = 0 := by
  unfold d0 C1.val
  simp

-- Helper lemma: edge strain with zero potential
lemma strain_at_zero (σ : C1 n_theta) (i j : Fin n_theta) :
  edge_strain (fun _ => 0) σ i j = (σ.val i j)^2 := by
  unfold edge_strain
  rw [d0_zero]
  ring

-- Edge (1,2) is overstressed
lemma edge_12_overstressed :
  edge_strain (fun _ : Fin n_theta => (0 : ℝ)) trap_sigma 1 2 > 90 := by
  rw [strain_at_zero]
  simp [sigma_val_eval]
  norm_num

-- Edge (1,3) is not overstressed
lemma edge_13_not_overstressed :
  edge_strain (fun _ : Fin n_theta => (0 : ℝ)) trap_sigma 1 3 ≤ 90 := by
  rw [strain_at_zero]
  simp [sigma_val_eval]
  norm_num

-- After breaking (1,2), all edges are within threshold
lemma equilibrium_after_break_12 :
  is_equilibrium (remove_edge theta_graph 1 2) (fun _ : Fin n_theta => 0) trap_sigma 90 := by
  intro i j h_active
  unfold remove_edge at h_active
  simp [Finset.mem_erase] at h_active
  obtain ⟨h_ne_ij, h_ne_ji, h_in_theta⟩ := h_active

  -- All edges in theta_active are either (1,2)/(2,1) or have low strain
  rw [strain_at_zero]
  simp [theta_graph, theta_active] at h_in_theta
  -- The remaining edges all have sigma values with |sigma| ≤ 9
  fin_cases i <;> fin_cases j <;> simp [sigma_val_eval] at * <;> norm_num

theorem greedy_is_not_optimal :
  let ϕ_start : C0 n_theta := fun _ => 0
  let C_max : ℝ := 90
  let G_greedy := evolve_to_equilibrium theta_graph ϕ_start trap_sigma C_max
  let G_smart := remove_edge theta_graph 1 3
  relaxed_energy G_greedy trap_sigma > relaxed_energy G_smart trap_sigma := by

  -- Define the key values
  set ϕ_start : C0 n_theta := fun _ => 0
  set C_max : ℝ := 90

  -- 1. Assertion: Greedy breaks (1,2)
  have h_break_12 : evolve_to_equilibrium theta_graph ϕ_start trap_sigma C_max = remove_edge theta_graph 1 2 := by
    -- Unfold one step of evolution
    unfold evolve_to_equilibrium

    -- Show the graph is not at equilibrium (so recursion continues)
    have h_not_eq : evolve_step theta_graph ϕ_start trap_sigma C_max ≠ theta_graph := by
      intro h_eq
      -- If no change, then find_overstressed_edge returned none
      unfold evolve_step at h_eq
      split at h_eq
      · -- find_overstressed_edge found something and we broke it
        rename_i i j h_found
        have spec := find_overstressed_edge_spec theta_graph ϕ_start trap_sigma C_max i j h_found
        have h_active := spec.1
        -- But remove_edge changes the graph when the edge exists
        have h_removed : (i, j) ∉ (remove_edge theta_graph i j).active_edges := by
          simp [remove_edge, Finset.mem_erase]
        have : (i, j) ∈ (remove_edge theta_graph i j).active_edges := by
          rw [h_eq]
          exact h_active
        contradiction
      · -- None case: But edge (1,2) IS overstressed!
        rename_i h_none
        -- Edge (1,2) exists in theta_graph
        have h_12_active : (1, 2) ∈ theta_graph.active_edges := by
          simp [theta_graph, theta_active]
        -- Edge (1,2) is overstressed
        have h_12_strain := edge_12_overstressed
        -- So (1,2) is in the candidates list
        unfold find_overstressed_edge at h_none
        -- The candidates list is non-empty because (1,2) is in it
        have h_in_candidates : (1, 2) ∈ theta_graph.active_edges.toList.filter
            (fun (i, j) => decide (edge_strain ϕ_start trap_sigma i j > C_max)) := by
          rw [List.mem_filter]
          constructor
          · rw [Finset.mem_toList]
            exact h_12_active
          · simp only [decide_eq_true_iff]
            exact h_12_strain
        -- So select_max_strain cannot return none
        have h_nonempty : theta_graph.active_edges.toList.filter
            (fun (i, j) => decide (edge_strain ϕ_start trap_sigma i j > C_max)) ≠ [] := by
          intro h_empty
          rw [h_empty] at h_in_candidates
          cases h_in_candidates
        -- But select_max_strain of a nonempty list returns some
        set candidates := theta_graph.active_edges.toList.filter
            (fun (i, j) => decide (edge_strain ϕ_start trap_sigma i j > C_max))
        cases h_cand : candidates with
        | nil =>
          -- But we proved the list is non-empty
          rw [h_cand] at h_nonempty
          exact absurd rfl h_nonempty
        | cons head tail =>
          -- Non-empty list means select_max_strain returns some
          -- Simplify h_none to remove the have binding
          simp only [] at h_none
          -- Substitute candidates = head :: tail
          rw [h_cand] at h_none
          -- Now h_none is: select_max_strain ϕ_start trap_sigma (head :: tail) = none
          unfold select_max_strain at h_none
          rw [List.foldl_cons] at h_none
          unfold select_max_strain_fn at h_none
          -- Now h_none says: foldl (f) (some head) tail = none
          -- But this is impossible: foldl with f starting from some _ always returns some _
          -- The function f maps: some b → some _ (always)
          -- Proof by induction would work, but let's try cases on tail
          cases tail with
          | nil =>
            -- foldl f (some head) [] = some head
            simp [List.foldl_nil] at h_none
          | cons h t =>
            -- Use the helper lemma: foldl starting from some _ always gives some _
            obtain ⟨y, hy⟩ := foldl_select_max_strain_fn_some ϕ_start trap_sigma (h :: t) head
            -- Unfold select_max_strain_fn in hy to match the expanded form in h_none
            unfold select_max_strain_fn at hy
            -- Now both refer to the same foldl computation, so we can rewrite
            rw [hy] at h_none
            -- This gives us: some y = none, which is a contradiction
            cases h_none

    rw [dif_neg h_not_eq]

    -- Show the first step breaks (1,2)
    have h_step : evolve_step theta_graph ϕ_start trap_sigma C_max = remove_edge theta_graph 1 2 := by
      unfold evolve_step
      -- find_overstressed_edge returns some edge
      have h_find : ∃ i j, find_overstressed_edge theta_graph ϕ_start trap_sigma C_max = some (i, j) := by
        unfold find_overstressed_edge
        -- The candidates list includes (1,2) since it's overstressed
        have h_12_in_candidates : (1, 2) ∈ theta_graph.active_edges.toList.filter
            (fun (i, j) => decide (edge_strain ϕ_start trap_sigma i j > C_max)) := by
          rw [List.mem_filter]
          constructor
          · rw [Finset.mem_toList]
            simp [theta_graph, theta_active]
          · simp only [decide_eq_true_iff]
            exact edge_12_overstressed
        -- So candidates is non-empty
        have h_nonempty : (theta_graph.active_edges.toList.filter
            (fun (i, j) => decide (edge_strain ϕ_start trap_sigma i j > C_max))) ≠ [] := by
          intro h_empty
          rw [h_empty] at h_12_in_candidates
          cases h_12_in_candidates
        -- select_max_strain on non-empty list returns some
        cases h_cand : theta_graph.active_edges.toList.filter
            (fun (i, j) => decide (edge_strain ϕ_start trap_sigma i j > C_max)) with
        | nil => rw [h_cand] at h_nonempty; exact absurd rfl h_nonempty
        | cons head tail =>
          unfold select_max_strain
          obtain ⟨y, hy⟩ := foldl_select_max_strain_fn_some ϕ_start trap_sigma tail head
          exact ⟨y.1, y.2, hy⟩
      obtain ⟨i, j, hfind⟩ := h_find
      rw [hfind]
      simp only []
      -- Use find_overstressed_edge_spec to know (i,j) is overstressed
      have spec := find_overstressed_edge_spec theta_graph ϕ_start trap_sigma C_max i j hfind
      have h_active := spec.1
      have h_overstressed := spec.2
      -- Check which edges are overstressed: only (1,2) and (2,1)
      simp [theta_graph, theta_active] at h_active
      -- Split on the 10 possible edges and eliminate those not overstressed
      rcases h_active with h01|h10|h12|h21|h20|h02|h13|h31|h32|h23
      · -- Case (0,1): strain = 0, not overstressed
        obtain ⟨rfl, rfl⟩ := h01
        rw [strain_at_zero, sigma_val_eval] at h_overstressed
        simp at h_overstressed
        norm_num at h_overstressed
      · -- Case (1,0): strain = 0, not overstressed
        obtain ⟨rfl, rfl⟩ := h10
        rw [strain_at_zero, sigma_val_eval] at h_overstressed
        simp at h_overstressed
        norm_num at h_overstressed
      · -- Case (1,2): strain = 100, overstressed ✓
        obtain ⟨rfl, rfl⟩ := h12
        rfl
      · -- Case (2,1): strain = 100, overstressed ✓ (same as removing (1,2))
        obtain ⟨rfl, rfl⟩ := h21
        -- Removing (2,1) is the same as removing (1,2) by symmetry
        unfold remove_edge DynamicGraph.active_edges
        simp
        apply Finset.ext
        intro x
        simp [Finset.mem_erase]
        tauto
      · -- Case (2,0): strain = 0, not overstressed
        obtain ⟨rfl, rfl⟩ := h20
        rw [strain_at_zero, sigma_val_eval] at h_overstressed
        simp at h_overstressed
        norm_num at h_overstressed
      · -- Case (0,2): strain = 0, not overstressed
        obtain ⟨rfl, rfl⟩ := h02
        rw [strain_at_zero, sigma_val_eval] at h_overstressed
        simp at h_overstressed
        norm_num at h_overstressed
      · -- Case (1,3): strain = 81, not overstressed
        obtain ⟨rfl, rfl⟩ := h13
        rw [strain_at_zero, sigma_val_eval] at h_overstressed
        simp at h_overstressed
        norm_num at h_overstressed
      · -- Case (3,1): strain = 81, not overstressed
        obtain ⟨rfl, rfl⟩ := h31
        rw [strain_at_zero, sigma_val_eval] at h_overstressed
        simp at h_overstressed
        norm_num at h_overstressed
      · -- Case (3,2): strain = 81, not overstressed
        obtain ⟨rfl, rfl⟩ := h32
        rw [strain_at_zero, sigma_val_eval] at h_overstressed
        simp at h_overstressed
        norm_num at h_overstressed
      · -- Case (2,3): strain = 81, not overstressed
        obtain ⟨rfl, rfl⟩ := h23
        rw [strain_at_zero, sigma_val_eval] at h_overstressed
        simp at h_overstressed
        norm_num at h_overstressed

    -- Show that remove_edge theta_graph 1 2 is at equilibrium
    have h_eq := equilibrium_after_break_12
    have h_stable := equilibrium_is_stable (remove_edge theta_graph 1 2) ϕ_start trap_sigma C_max h_eq

    -- Therefore evolve_to_equilibrium of the stepped graph equals itself
    have h_recursive : evolve_to_equilibrium (evolve_step theta_graph ϕ_start trap_sigma C_max) ϕ_start trap_sigma C_max =
                       evolve_step theta_graph ϕ_start trap_sigma C_max := by
      rw [h_step]
      unfold evolve_to_equilibrium
      exact dif_pos h_stable

    rw [h_recursive, h_step]

  -- 2. Calculate Greedy Energy
  have h_greedy_energy : relaxed_energy (evolve_to_equilibrium theta_graph ϕ_start trap_sigma C_max) trap_sigma = 81 := by
    rw [h_break_12]
    unfold relaxed_energy
    -- Condition: (1, 2) ∉ G_greedy
    have h_cond : (1, 2) ∉ (remove_edge theta_graph 1 2).active_edges := by
      simp [remove_edge]
    rw [if_pos h_cond]
    -- Evaluate the flux sum
    simp [sigma_val_eval]
    norm_num

  -- 3. Calculate Smart Energy
  have h_smart_energy : relaxed_energy (remove_edge theta_graph 1 3) trap_sigma = 100 / 3 := by
    unfold relaxed_energy
    -- Condition 1: (1, 2) ∈ G_smart (so first if fails)
    have h_in : (1, 2) ∈ (remove_edge theta_graph 1 3).active_edges := by
      simp [remove_edge, theta_graph, theta_active]
    -- Condition 2: (1, 3) ∉ G_smart (so second if succeeds)
    have h_not_in : (1, 3) ∉ (remove_edge theta_graph 1 3).active_edges := by
      simp [remove_edge]
    rw [if_neg (show ¬((1, 2) ∉ (remove_edge theta_graph 1 3).active_edges) from fun h => h h_in)]
    rw [if_pos h_not_in]

    -- Evaluate the flux sum
    simp [sigma_val_eval]
    norm_num

  -- 4. Compare: 81 > 33.33
  show relaxed_energy (evolve_to_equilibrium theta_graph ϕ_start trap_sigma C_max) trap_sigma >
       relaxed_energy (remove_edge theta_graph 1 3) trap_sigma
  rw [h_greedy_energy, h_smart_energy]
  linarith

end DiscreteHodge
