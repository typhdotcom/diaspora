/-
# Topology Dynamics

The actual evolution of graph topology under strain. While TopologyChange.lean
proves that black holes *must* form, this file defines *how* they form: the
step-by-step process of edge breaking and topology change.

Key insight: This is a phase transition. The graph doesn't just move through
configuration space—it changes the configuration space itself.
-/

import Diaspora.TopologyChange
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

open BigOperators

namespace DiscreteHodge

/-! ## Dynamic Graph Structure -/

/--
A graph that can evolve: vertices are fixed, but edges can break.
This models spacetime where "locations" persist but "connections" can fail.
-/
structure DynamicGraph (n : ℕ) where
  /-- Active (unbroken) edges -/
  active_edges : Finset (Fin n × Fin n)
  /-- Active edges are symmetric (undirected graph) -/
  symmetric : ∀ i j, (i, j) ∈ active_edges ↔ (j, i) ∈ active_edges
  /-- No self-loops -/
  no_loops : ∀ i, (i, i) ∉ active_edges
deriving DecidableEq

/-- The complete graph on n vertices (all edges active) -/
def DynamicGraph.complete (n : ℕ) : DynamicGraph n where
  active_edges := Finset.univ.filter (fun (i, j) => i ≠ j)
  symmetric := by
    intro i j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  no_loops := by
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]

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

/-! ## Constraints on Dynamic Graphs -/

/--
A 1-cochain on a dynamic graph: only defined on active edges.
We embed this into the full C1 n by setting broken edges to zero.
-/
def DynamicC1 (n : ℕ) (G : DynamicGraph n) :=
  { σ : C1 n // ∀ i j, (i, j) ∉ G.active_edges → σ.val i j = 0 }

/-- Embed DynamicC1 into C1 -/
def DynamicC1.toC1 {n : ℕ} {G : DynamicGraph n} (σ : DynamicC1 n G) : C1 n :=
  σ.val

/-! ## Finding Overstressed Edges -/

/--
Find an edge that exceeds the breaking threshold.
Returns the first such edge found (if any).
-/
noncomputable def find_overstressed_edge {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (ϕ : C0 n) (σ : C1 n) (C_max : ℝ) :
    Option (Fin n × Fin n) :=
  G.active_edges.toList.find? (fun (i, j) => edge_strain ϕ σ i j > C_max)

/-! ## Topological Evolution -/

/--
Remove a single edge from the graph.
This is the atomic operation of black hole formation.
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
Single step of evolution: if an overstressed edge exists, break it.
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

/-- If find? returns some, the element satisfies the predicate -/
lemma List.find?_some_prop {α : Type*} (xs : List α) (p : α → Bool) (a : α)
    (h : xs.find? p = some a) : p a = true := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    unfold List.find? at h
    split at h
    · injection h with h_eq
      subst h_eq
      assumption
    · exact ih h

/-- If find? returns some, the element is in the list -/
lemma List.find?_some_mem {α : Type*} (xs : List α) (p : α → Bool) (a : α)
    (h : xs.find? p = some a) : a ∈ xs := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    unfold List.find? at h
    split at h
    · injection h with h_eq
      subst h_eq
      simp
    · simp
      right
      exact ih h

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
    use i, j
    unfold find_overstressed_edge at h_found
    have h_mem := List.find?_some_mem _ _ _ h_found
    have h_prop := List.find?_some_prop _ _ _ h_found
    simp at h_prop
    exact ⟨Finset.mem_toList.mp h_mem, h_prop⟩
  · -- none case: graph unchanged, contradicts h_changed
    contradiction

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
  
  -- 1. Expose definition
  simp only [dynamic_strain_energy]

  -- 2. Convert nested sums (∑ i, ∑ j) to product sums (∑ p)
  -- Use simp_rw to penetrate the multiplication and equation
  simp_rw [←Finset.sum_product']

  -- 3. Convert "sum over universe with if" to "sum over active edges"
  -- ∑ x, if x ∈ S then f x else 0  ==>  ∑ x in S, f x
  -- logic: we use sum_filter backwards, then simplify filter (· ∈ S) univ to S
  rw [←Finset.sum_filter, ←Finset.sum_filter]
  simp only [Prod.eta, Finset.filter_mem_eq_inter]

  -- 4. Decompose the sets: G = G_next ∪ {(i,j), (j,i)}
  let S_next := G_next.active_edges
  let f := fun (p : Fin n × Fin n) => edge_strain ϕ σ p.1 p.2
  
  -- Establish the set relationship
  have h_decomp : G.active_edges = insert (j, i) (insert (i, j) S_next) := by
    have h_sym : (j, i) ∈ G.active_edges := (G.symmetric i j).mp h_active
    have h_ne_pair : (i, j) ≠ (j, i) := by
      intro h_eq; injection h_eq with h_inj; exact h_ne h_inj
    
    -- G = (G \ {(i,j)}) + {(i,j)}
    have step1 : G.active_edges = insert (i, j) (G.active_edges.erase (i, j)) := 
      (Finset.insert_erase h_active).symm
      
    -- (j,i) is in the erased set
    have h_ji_in_erased : (j, i) ∈ G.active_edges.erase (i, j) := by
      simp [Finset.mem_erase, h_ne_pair.symm, h_sym]
      
    -- G = ((G \ {(i,j)}) \ {(j,i)}) + {(j,i)} + {(i,j)}
    rw [step1]
    -- Insert (j,i) back into the erased set
    rw [←Finset.insert_erase h_ji_in_erased]
    -- Swap insertion order to match RHS
    rw [Finset.insert_comm]
    -- S_next is exactly (G.active_edges.erase (i,j)).erase (j,i)
    rfl

  -- 5. Expand the sum for G
  rw [h_decomp]

  -- Prove (i,j) and (j,i) are NOT in S_next to use sum_insert
  have h_ij_not_in_next : (i, j) ∉ S_next := by
    simp [S_next, G_next, remove_edge, Finset.mem_erase]
  have h_ji_not_in_next : (j, i) ∉ S_next := by
    simp [S_next, G_next, remove_edge, Finset.mem_erase]
  have h_ne_pair : (j, i) ≠ (i, j) := by
    intro h; injection h with h'; exact h_ne h'.symm

  -- Prove (j,i) is not in (insert (i,j) S_next)
  have h_ji_not_in_insert : (j, i) ∉ insert (i, j) S_next := by
    simp [h_ne_pair, h_ji_not_in_next]

  -- Simplify univ ×ˢ univ ∩ S to just S
  simp only [Finset.univ_product_univ, Finset.univ_inter]

  -- Expand: Sum(S_next + {ji} + {ij}) = Sum(S_next) + f(ji) + f(ij)
  rw [Finset.sum_insert h_ji_not_in_insert]
  rw [Finset.sum_insert h_ij_not_in_next]
  
  -- 6. Algebraic Simplification
  -- Symmetry: strain(j,i) = strain(i,j)
  have h_strain_sym : f (j, i) = f (i, j) := by
    unfold f edge_strain
    rw [(d0 ϕ).skew j i, σ.skew j i]
    ring

  -- Result: 1/2 * (S + f + f) = 1/2 * S + f
  -- Convert edge_strain expressions to f notation
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
    -- Found overstressed edge, contradicts equilibrium
    unfold find_overstressed_edge at h_found
    have h_mem := List.find?_some_mem _ _ _ h_found
    have h_prop := List.find?_some_prop _ _ _ h_found
    simp at h_prop
    have h_active : (i, j) ∈ G.active_edges := Finset.mem_toList.mp h_mem
    have h_bounded := h_eq i j h_active
    linarith
  · -- No overstressed edge found
    rfl

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
    -- Edge was removed
    unfold remove_edge
    simp only
    -- (i,j) was active
    unfold find_overstressed_edge at h_found
    have h_mem := List.find?_some_mem _ _ _ h_found
    have h_active : (i, j) ∈ G.active_edges := Finset.mem_toList.mp h_mem
    -- (j,i) also active by symmetry
    have h_sym : (j, i) ∈ G.active_edges := (G.symmetric i j).mp h_active
    -- First erase decreases card
    have h_first : (G.active_edges.erase (i, j)).card < G.active_edges.card :=
      Finset.card_lt_card (Finset.erase_ssubset h_active)
    -- Second erase decreases card further (or stays same if (i,j) = (j,i))
    by_cases h_eq : (i, j) = (j, i)
    · -- If (i,j) = (j,i), second erase is no-op
      have h_not_mem : (j, i) ∉ G.active_edges.erase (i, j) := by
        rw [h_eq]
        simp [Finset.mem_erase]
      rw [Finset.erase_eq_of_notMem h_not_mem]
      exact h_first
    · -- If (i,j) ≠ (j,i), second erase decreases card
      have h_mem_after : (j, i) ∈ G.active_edges.erase (i, j) := by
        simp only [Finset.mem_erase]
        exact ⟨Ne.symm h_eq, h_sym⟩
      calc ((G.active_edges.erase (i, j)).erase (j, i)).card
          < (G.active_edges.erase (i, j)).card := Finset.card_lt_card (Finset.erase_ssubset h_mem_after)
        _ < G.active_edges.card := h_first
  · -- No change (contradiction with h_changed)
    rename_i h_none
    simp only [h_none] at h_changed
    exact absurd rfl h_changed

/--
Iterate evolution until equilibrium.
Termination is guaranteed: each step strictly decreases the number of edges.
-/
noncomputable def evolve_to_equilibrium {n : ℕ} [Fintype (Fin n)] [DecidableEq (DynamicGraph n)]
    (G : DynamicGraph n) (ϕ : C0 n) (σ : C1 n) (C_max : ℝ) :
    DynamicGraph n :=
  if h : evolve_step G ϕ σ C_max = G then
    G
  else
    have _ : (evolve_step G ϕ σ C_max).active_edges.card < G.active_edges.card :=
      evolve_decreases_card G ϕ σ C_max h
    evolve_to_equilibrium (evolve_step G ϕ σ C_max) ϕ σ C_max
termination_by G.active_edges.card

end DiscreteHodge
