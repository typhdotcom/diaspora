/-
# Topology Dynamics

Evolution of graph topology under strain. While TopologyChange.lean
proves that edges must break under sufficient frustration, this file defines
the step-by-step process of identifying and removing overstressed edges.
-/

import Diaspora.TopologyChange
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

open BigOperators Classical

namespace DiscreteHodge

/-! ## Graph Metrics -/

/-- Number of active undirected edges (card / 2, since we store both directions) -/
def DynamicGraph.edge_count {n : ℕ} (G : DynamicGraph n) : ℕ :=
  G.active_edges.card / 2

/--
Cyclomatic number (circuit rank): counts independent cycles in a connected graph.
For connected graphs: cyclomatic = |E| - |V| + 1.
This is NOT the true first Betti number, which would be |E| - |V| + c where c is the number of connected components.
-/
def DynamicGraph.cyclomatic_number {n : ℕ} (G : DynamicGraph n) : ℤ :=
  (G.edge_count : ℤ) - (n : ℤ) + 1

/-! ## Finding Overstressed Edges (Max Strain Logic) -/

/-- The comparison logic for finding max strain -/
noncomputable def select_max_strain_fn {n : ℕ} (ϕ : C0 n) (σ : C1 n) 
    (best : Option (Fin n × Fin n)) (curr : Fin n × Fin n) : Option (Fin n × Fin n) :=
  match best with
  | none => some curr
  | some b => if edge_strain ϕ σ curr.1 curr.2 > edge_strain ϕ σ b.1 b.2 then some curr else some b

/-- Helper: Fold function to find the edge with the maximum strain in a list -/
noncomputable def select_max_strain {n : ℕ} (ϕ : C0 n) (σ : C1 n)
    (candidates : List (Fin n × Fin n)) : Option (Fin n × Fin n) :=
  candidates.foldl (select_max_strain_fn ϕ σ) none

/-- Auxiliary Lemma: General correctness of the max strain fold logic -/
lemma select_max_strain_aux {n : ℕ} (ϕ : C0 n) (σ : C1 n)
    (l : List (Fin n × Fin n)) (init : Option (Fin n × Fin n)) (res : Fin n × Fin n)
    (h : l.foldl (select_max_strain_fn ϕ σ) init = some res) : 
    res ∈ l ∨ (∃ x, init = some x ∧ res = x) := by
  induction l generalizing init with
  | nil =>
    simp only [List.foldl_nil] at h
    right
    use res
  | cons head tail ih =>
    simp only [List.foldl_cons] at h
    specialize ih (select_max_strain_fn ϕ σ init head) h
    rcases ih with h_in_tail | ⟨x, h_acc_eq, h_res_eq⟩
    · left
      exact List.mem_cons_of_mem head h_in_tail
    · -- We know res = x. Replace x with res in the hypothesis.
      rw [←h_res_eq] at h_acc_eq 
      simp only [select_max_strain_fn] at h_acc_eq
      cases init with
      | none =>
        -- If init was none, acc became some head.
        injection h_acc_eq with h_head
        rw [←h_head]
        left
        exact List.mem_cons_self
      | some b =>
        -- If init was some b, acc became either head or b.
        simp only [] at h_acc_eq
        split_ifs at h_acc_eq
        · -- Case: head was better. Acc became head.
          injection h_acc_eq with h_head
          rw [←h_head]
          left
          exact List.mem_cons_self
        · -- Case: b was better/equal. Acc stayed b.
          injection h_acc_eq with h_b
          rw [←h_b]
          right
          use b

/-- Lemma: The result of select_max_strain is always a member of the input list -/
lemma select_max_strain_mem {n : ℕ} (ϕ : C0 n) (σ : C1 n)
    (l : List (Fin n × Fin n)) (res : Fin n × Fin n)
    (h : select_max_strain ϕ σ l = some res) : res ∈ l := by
  unfold select_max_strain at h
  have aux := select_max_strain_aux ϕ σ l none res h
  cases aux with
  | inl h_in => exact h_in
  | inr h_init =>
    obtain ⟨x, h_none, _⟩ := h_init
    contradiction

/-- The foldl result has strain ≥ the init -/
lemma select_max_strain_fn_foldl_ge_init {n : ℕ} (ϕ : C0 n) (σ : C1 n)
    (l : List (Fin n × Fin n)) (init : Fin n × Fin n) (res : Fin n × Fin n)
    (h : l.foldl (select_max_strain_fn ϕ σ) (some init) = some res) :
    edge_strain ϕ σ res.1 res.2 ≥ edge_strain ϕ σ init.1 init.2 := by
  induction l generalizing init res with
  | nil =>
    simp only [List.foldl_nil] at h
    injection h with h_res
    rw [← h_res]
  | cons hd tl ih =>
    simp only [List.foldl_cons] at h
    simp only [select_max_strain_fn] at h
    split_ifs at h with hcmp
    · -- hd > init, continue with hd
      have h_res_ge_hd := ih hd res h
      exact le_trans (le_of_lt hcmp) h_res_ge_hd
    · -- init >= hd, continue with init
      exact ih init res h

/-- Auxiliary: The foldl result has strain ≥ all elements processed -/
lemma select_max_strain_fn_foldl_max {n : ℕ} (ϕ : C0 n) (σ : C1 n)
    (l : List (Fin n × Fin n)) (init : Fin n × Fin n) (res : Fin n × Fin n)
    (h : l.foldl (select_max_strain_fn ϕ σ) (some init) = some res) :
    ∀ e ∈ l, edge_strain ϕ σ res.1 res.2 ≥ edge_strain ϕ σ e.1 e.2 := by
  induction l generalizing init res with
  | nil => intro e he; simp at he
  | cons hd tl ih =>
    simp only [List.foldl_cons] at h
    simp only [select_max_strain_fn] at h
    split_ifs at h with hcmp
    · -- hd > init, continue with hd
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he_tl
      · exact select_max_strain_fn_foldl_ge_init ϕ σ tl e res h
      · exact ih hd res h e he_tl
    · -- init >= hd, continue with init
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he_tl
      · -- e = hd
        have h_init_ge_hd : edge_strain ϕ σ init.1 init.2 ≥ edge_strain ϕ σ e.1 e.2 := le_of_not_gt hcmp
        have h_res_ge_init := select_max_strain_fn_foldl_ge_init ϕ σ tl init res h
        exact le_trans h_init_ge_hd h_res_ge_init
      · exact ih init res h e he_tl

/--
Find the edge that exceeds the breaking threshold with the MAXIMUM strain.
Returns the single worst edge found (if any).
-/
noncomputable def find_overstressed_edge {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (ϕ : C0 n) (σ : C1 n) (C_max : ℝ) :
    Option (Fin n × Fin n) :=
  let candidates := G.active_edges.toList.filter (fun (i, j) => decide (edge_strain ϕ σ i j > C_max))
  select_max_strain ϕ σ candidates

/--
Key Theorem: If find_overstressed_edge returns an edge, it is active and overstressed.
-/
theorem find_overstressed_edge_spec {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (ϕ : C0 n) (σ : C1 n) (C_max : ℝ)
    (i j : Fin n)
    (h_some : find_overstressed_edge G ϕ σ C_max = some (i, j)) :
    (i, j) ∈ G.active_edges ∧ edge_strain ϕ σ i j > C_max := by
  unfold find_overstressed_edge at h_some
  have h_in_candidates := select_max_strain_mem ϕ σ _ _ h_some
  rw [List.mem_filter] at h_in_candidates
  constructor
  · rw [Finset.mem_toList] at h_in_candidates
    exact h_in_candidates.1
  · have h_bool := h_in_candidates.2
    simp only [decide_eq_true_iff] at h_bool
    exact h_bool

/--
Maximality: The returned edge has strain ≥ all other overstressed edges.
-/
theorem find_overstressed_edge_max {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (ϕ : C0 n) (σ : C1 n) (C_max : ℝ)
    (i j : Fin n)
    (h_some : find_overstressed_edge G ϕ σ C_max = some (i, j))
    (a b : Fin n) (h_ab_active : (a, b) ∈ G.active_edges) (h_ab_over : edge_strain ϕ σ a b > C_max) :
    edge_strain ϕ σ i j ≥ edge_strain ϕ σ a b := by
  unfold find_overstressed_edge at h_some
  -- (a, b) is in the candidates list
  have h_ab_in_cand : (a, b) ∈ G.active_edges.toList.filter (fun x => decide (edge_strain ϕ σ x.1 x.2 > C_max)) := by
    simp only [List.mem_filter, Finset.mem_toList, decide_eq_true_iff]
    exact ⟨h_ab_active, h_ab_over⟩
  -- select_max_strain returns a maximal element
  unfold select_max_strain at h_some
  cases h_list : G.active_edges.toList.filter (fun x => decide (edge_strain ϕ σ x.1 x.2 > C_max)) with
  | nil => simp [h_list] at h_ab_in_cand
  | cons hd tl =>
    rw [h_list] at h_some h_ab_in_cand
    simp only [List.foldl_cons] at h_some
    simp only [List.mem_cons] at h_ab_in_cand
    rcases h_ab_in_cand with rfl | h_ab_in_tl
    · -- (a, b) = hd, so we use the fact that result strain ≥ init strain
      exact select_max_strain_fn_foldl_ge_init ϕ σ tl (a, b) (i, j) h_some
    · -- (a, b) in tail
      exact select_max_strain_fn_foldl_max ϕ σ tl hd (i, j) h_some (a, b) h_ab_in_tl

/-! ## Topological Evolution -/

/--
Remove a single edge from the graph.
-/
def remove_edge {n : ℕ} (G : DynamicGraph n) (i j : Fin n) : DynamicGraph n where
  active_edges := G.active_edges.erase (i, j) |>.erase (j, i)
  symmetric := by
    intro a b
    simp only [Finset.mem_erase, ne_eq]
    constructor
    · intro ⟨h1, h2, h3⟩
      have h_sym := (G.symmetric a b).mp h3
      refine ⟨?_, ?_, h_sym⟩
      · intro h_eq
        injection h_eq with ha hb
        subst ha hb
        exact h2 rfl
      · intro h_eq
        injection h_eq with ha hb
        subst ha hb
        exact h1 rfl
    · intro ⟨h1, h2, h3⟩
      have h_sym := (G.symmetric b a).mp h3
      refine ⟨?_, ?_, h_sym⟩
      · intro h_eq
        injection h_eq with ha hb
        subst ha hb
        exact h2 rfl
      · intro h_eq
        injection h_eq with ha hb
        subst ha hb
        exact h1 rfl
  no_loops := by
    intro a
    simp only [Finset.mem_erase, ne_eq]
    intro ⟨_, _, h3⟩
    exact G.no_loops a h3

/--
When an edge breaks, its capacity transfers from Active to Latent.
-/
theorem latent_capacity_growth {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (σ : C1 n) (i j : Fin n)
    (h_active : (i, j) ∈ G.active_edges) :
  latent_capacity (remove_edge G i j) σ = latent_capacity G σ + (σ.val i j)^2 := by
  rw [latent_capacity, latent_capacity, remove_edge]
  simp only [Finset.mem_erase, ne_eq, not_and]
  have h_sym : (j, i) ∈ G.active_edges := (G.symmetric j i).mpr h_active
  have skew_sq : σ.val j i ^ 2 = σ.val i j ^ 2 := by
    have : σ.val j i = -σ.val i j := σ.skew j i
    rw [this]; ring
  have cond_equiv : ∀ a b, (¬(a, b) = (j, i) → ¬(a, b) = (i, j) → (a, b) ∉ G.active_edges) ↔
                           ((a, b) = (j, i) ∨ (a, b) = (i, j) ∨ (a, b) ∉ G.active_edges) := by
    intro a b
    constructor
    · intro h
      by_cases h1 : (a, b) = (j, i)
      · left; exact h1
      · by_cases h2 : (a, b) = (i, j)
        · right; left; exact h2
        · right; right; exact h h1 h2
    · intro h h1 h2
      rcases h with h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact h
  simp_rw [cond_equiv]
  have sum_split : ∑ x, ∑ y, (if (x, y) = (j, i) ∨ (x, y) = (i, j) ∨ (x, y) ∉ G.active_edges
                                then σ.val x y ^ 2 else 0) =
                   ∑ x, ∑ y, (if (x, y) ∉ G.active_edges then σ.val x y ^ 2 else 0) +
                   σ.val i j ^ 2 + σ.val j i ^ 2 := by
    trans (∑ x, ∑ y, ((if (x,y) ∉ G.active_edges then σ.val x y ^ 2 else 0) +
                       (if (x,y) = (i,j) then σ.val i j ^ 2 else 0) +
                       (if (x,y) = (j,i) then σ.val j i ^ 2 else 0)))
    · congr 1; ext x; congr 1; ext y
      by_cases hji : (x, y) = (j, i)
      · rw [hji]
        simp only [h_sym, if_true, Or.inl]
        have neq : (j, i) ≠ (i, j) := by
          intro h; injection h with h1 h2
          have : j = i := h1
          rw [this] at h_sym
          exact G.no_loops i h_sym
        simp [neq]
        congr; injection hji; simp_all
      · by_cases hij : (x, y) = (i, j)
        · rw [hij]
          simp only [h_active, if_true, Or.inr, Or.inl]
          have neq : (i, j) ≠ (j, i) := by
            intro h; injection h with h1 h2
            have : i = j := h1
            rw [this] at h_active
            exact G.no_loops j h_active
          simp [neq]
          congr; injection hij; simp_all
        · by_cases hr : (x, y) ∉ G.active_edges
          · simp [hr, hji, hij]
          · simp [hr, hji, hij]
    · simp only [Finset.sum_add_distrib]
      have sum_pair_eq : ∀ (a b : Fin n) (c : ℝ),
          ∑ x, ∑ y, (if (x, y) = (a, b) then c else 0) = c := by
        intro a b c
        have inner : ∀ x, ∑ y, (if (x, y) = (a, b) then c else 0) = if x = a then c else 0 := by
          intro x
          by_cases hx : x = a
          · subst hx
            simp only [Prod.mk.injEq, true_and]
            rw [Finset.sum_ite_eq']; simp
          · simp only [hx, ite_false]
            apply Finset.sum_eq_zero
            intro y _
            simp [hx]
        simp_rw [inner]
        rw [Finset.sum_ite_eq']; simp
      rw [sum_pair_eq i j, sum_pair_eq j i]
  rw [sum_split, skew_sq]
  ring

/--
Single step of evolution: if an overstressed edge exists, break the worst one.
Otherwise, return the graph unchanged.
-/
noncomputable def evolve_step {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (ϕ : C0 n) (σ : C1 n) (C_max : ℝ) :
    DynamicGraph n :=
  match find_overstressed_edge G ϕ σ C_max with
  | some (i, j) => remove_edge G i j
  | none => G

/-! ## Properties of Evolution -/

/--
Removing an edge decreases edge count by 1 (since we erase both (i,j) and (j,i)).
-/
lemma edge_count_decreases_by_one {n : ℕ} (G : DynamicGraph n) (i j : Fin n)
    (h_active : (i, j) ∈ G.active_edges)
    (h_ne : i ≠ j) :
  (remove_edge G i j).edge_count + 1 = G.edge_count := by
  unfold DynamicGraph.edge_count remove_edge
  simp only
  have h_sym : (j, i) ∈ G.active_edges := (G.symmetric i j).mp h_active
  have h_ne_pair : (i, j) ≠ (j, i) := by
    intro h_eq
    injection h_eq with hi hj
    exact h_ne hi
  -- After erasing both (i,j) and (j,i), card decreases by 2
  have h_card : ((G.active_edges.erase (i, j)).erase (j, i)).card = G.active_edges.card - 2 := by
    have h1 := Finset.card_erase_of_mem h_active
    have h_mem_after : (j, i) ∈ G.active_edges.erase (i, j) := by
      simp only [Finset.mem_erase]
      exact ⟨h_ne_pair.symm, h_sym⟩
    have h2 := Finset.card_erase_of_mem h_mem_after
    omega
  -- So edge_count decreases by 1
  rw [h_card]
  have h_card_pos : G.active_edges.card ≥ 2 := by
    have : G.active_edges.card > 0 := Finset.card_pos.mpr ⟨(i,j), h_active⟩
    have : G.active_edges.card > 1 := by
      apply Finset.one_lt_card.mpr
      exact ⟨(i,j), h_active, (j,i), h_sym, h_ne_pair⟩
    omega
  omega

/--
Removing an edge decreases the cyclomatic number (removes a cycle).
This represents the graph becoming more tree-like.

Assumes the graph stays connected after removal.
-/
theorem cyclomatic_decreases_on_edge_removal {n : ℕ} (G : DynamicGraph n) (i j : Fin n)
    (h_active : (i, j) ∈ G.active_edges)
    (h_ne : i ≠ j)
    (_h_connected : True) : -- Graph stays connected after removal
  DynamicGraph.cyclomatic_number (remove_edge G i j) + 1 = DynamicGraph.cyclomatic_number G := by
  unfold DynamicGraph.cyclomatic_number
  have h_edge := edge_count_decreases_by_one G i j h_active h_ne
  omega

/--
Evolution preserves vertex count (locations don't disappear).
The type system guarantees this: DynamicGraph n → DynamicGraph n.
-/
theorem evolve_preserves_vertices {n : ℕ} [Fintype (Fin n)]
    (_ : DynamicGraph n) (_ : C0 n) (_ : C1 n) (_ : ℝ) :
  True := by trivial

/--
If evolution changes the graph, it's because an edge was overstressed.
-/
theorem evolve_changes_only_if_overstressed {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (ϕ : C0 n) (σ : C1 n) (C_max : ℝ)
    (h_changed : evolve_step G ϕ σ C_max ≠ G) :
  ∃ i j, (i, j) ∈ G.active_edges ∧ edge_strain ϕ σ i j > C_max := by
  unfold evolve_step at h_changed
  split at h_changed
  · rename_i i j h_found
    have spec := find_overstressed_edge_spec G ϕ σ C_max i j h_found
    use i, j
  · contradiction

/-! ## Dynamic Energy Calculation -/

/-- Sum of strain only on active edges -/
noncomputable def dynamic_strain_energy {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (ϕ : C0 n) (σ : C1 n) : ℝ :=
  (1/2) * ∑ i, ∑ j, if (i, j) ∈ G.active_edges then edge_strain ϕ σ i j else 0

/--
Energy Drop Theorem:
When an edge breaks, the total strain energy decreases by exactly the amount
that was stored in that edge.
-/
theorem energy_drop_on_break {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (ϕ : C0 n) (σ : C1 n) (i j : Fin n)
    (h_active : (i, j) ∈ G.active_edges)
    (h_ne : i ≠ j) :
  let G_next := remove_edge G i j
  dynamic_strain_energy G_next ϕ σ =
  dynamic_strain_energy G ϕ σ - edge_strain ϕ σ i j := by
  intro G_next
  
  simp only [dynamic_strain_energy]
  simp_rw [←Finset.sum_product']
  rw [←Finset.sum_filter, ←Finset.sum_filter]
  simp only [Prod.eta, Finset.filter_mem_eq_inter]

  let S_next := G_next.active_edges
  let f := fun (p : Fin n × Fin n) => edge_strain ϕ σ p.1 p.2
  
  have h_decomp : G.active_edges = insert (j, i) (insert (i, j) S_next) := by
    have h_sym : (j, i) ∈ G.active_edges := (G.symmetric i j).mp h_active
    have h_ne_pair : (i, j) ≠ (j, i) := by
      intro h_eq; injection h_eq with h_inj; exact h_ne h_inj
      
    have step1 : G.active_edges = insert (i, j) (G.active_edges.erase (i, j)) := 
      (Finset.insert_erase h_active).symm
      
    have h_ji_in_erased : (j, i) ∈ G.active_edges.erase (i, j) := by
      simp [Finset.mem_erase, h_ne_pair.symm, h_sym]
      
    rw [step1]
    rw [←Finset.insert_erase h_ji_in_erased]
    rw [Finset.insert_comm]
    rfl

  rw [h_decomp]

  have h_ij_not_in_next : (i, j) ∉ S_next := by
    simp [S_next, G_next, remove_edge, Finset.mem_erase]
  have h_ji_not_in_next : (j, i) ∉ S_next := by
    simp [S_next, G_next, remove_edge, Finset.mem_erase]
  have h_ne_pair : (j, i) ≠ (i, j) := by
    intro h; injection h with h'; exact h_ne h'.symm

  have h_ji_not_in_insert : (j, i) ∉ insert (i, j) S_next := by
    simp [h_ne_pair, h_ji_not_in_next]

  simp only [Finset.univ_product_univ, Finset.univ_inter]

  rw [Finset.sum_insert h_ji_not_in_insert]
  rw [Finset.sum_insert h_ij_not_in_next]
  
  have h_strain_sym : f (j, i) = f (i, j) := by
    unfold f edge_strain
    rw [(d0 ϕ).skew j i, σ.skew j i]
    ring

  change 1 / 2 * ∑ x ∈ G_next.active_edges, f x =
         1 / 2 * (f (j, i) + (f (i, j) + ∑ x ∈ S_next, f x)) - edge_strain ϕ σ i j
  rw [h_strain_sym]
  unfold f edge_strain
  ring

/-! ## Termination and Equilibrium -/

/--
Evolution terminates when no edges are overstressed.
At equilibrium, the graph is stable under the constraints.
-/
def is_equilibrium {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (ϕ : C0 n) (σ : C1 n) (C_max : ℝ) : Prop :=
  ∀ i j, (i, j) ∈ G.active_edges → edge_strain ϕ σ i j ≤ C_max

/--
If the graph is at equilibrium, evolution doesn't change it.
-/
theorem equilibrium_is_stable {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (ϕ : C0 n) (σ : C1 n) (C_max : ℝ)
    (h_eq : is_equilibrium G ϕ σ C_max) :
  evolve_step G ϕ σ C_max = G := by
  unfold evolve_step
  split
  · rename_i i j h_found
    have spec := find_overstressed_edge_spec G ϕ σ C_max i j h_found
    have h_active := spec.1
    have h_strain := spec.2
    have h_bounded := h_eq i j h_active
    linarith
  · rfl

/-! ## Iterated Evolution -/

/--
If evolution changes the graph, the number of active edges strictly decreases.
-/
theorem evolve_decreases_card {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (ϕ : C0 n) (σ : C1 n) (C_max : ℝ)
    (h_changed : evolve_step G ϕ σ C_max ≠ G) :
  (evolve_step G ϕ σ C_max).active_edges.card < G.active_edges.card := by
  unfold evolve_step at h_changed
  unfold evolve_step
  split
  · rename_i i j h_found
    unfold remove_edge
    simp only
    have spec := find_overstressed_edge_spec G ϕ σ C_max i j h_found
    have h_active := spec.1
    
    have h_sym : (j, i) ∈ G.active_edges := (G.symmetric i j).mp h_active
    have h_first : (G.active_edges.erase (i, j)).card < G.active_edges.card :=
      Finset.card_lt_card (Finset.erase_ssubset h_active)

    by_cases h_eq : (i, j) = (j, i)
    · have h_not_mem : (j, i) ∉ G.active_edges.erase (i, j) := by
        rw [h_eq]
        simp [Finset.mem_erase]
      rw [Finset.erase_eq_of_notMem h_not_mem]
      exact h_first
    · have h_mem_after : (j, i) ∈ G.active_edges.erase (i, j) := by
        simp only [Finset.mem_erase]
        exact ⟨Ne.symm h_eq, h_sym⟩
      calc ((G.active_edges.erase (i, j)).erase (j, i)).card
          < (G.active_edges.erase (i, j)).card := Finset.card_lt_card (Finset.erase_ssubset h_mem_after)
        _ < G.active_edges.card := h_first
  · rename_i h_none
    simp only [h_none] at h_changed
    exact absurd rfl h_changed

end DiscreteHodge
