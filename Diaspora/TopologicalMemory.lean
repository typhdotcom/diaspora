/-
# Topological Memory

"The universe remembers how it was cooled."

This file proves that the cooling schedule (Fast vs. Slow) is injectively
encoded in the final topological class. You can look at the graph and tell
whether it was quenched or annealed.

This formalizes path dependence and establishes graphs as information storage.
-/

import Diaspora.FalseVacuum
import Diaspora.Patience
import Diaspora.GlassDynamics

namespace DiscreteHodge

open BigOperators

/--
The Cooling Schedule.
Represents the thermal history of the system evolution.
-/
inductive CoolingSchedule
| Quenched  -- Fast: Break immediately based on local strain (α = 0)
| Annealed  -- Slow: Relax fully then break (α = 1)
deriving DecidableEq

/--
The Evolution Function depending on history.
Maps thermal history to final stable topology.
-/
noncomputable def evolve_with_history (S : CoolingSchedule) : DynamicGraph n_theta :=
  match S with
  | .Quenched =>
      -- Greedy breaks edge (1,2) - the locally worst edge
      remove_edge theta_graph 1 2
  | .Annealed =>
      -- Patient breaks edge (1,3) - the globally optimal edge
      remove_edge theta_graph 1 3

/--
The degree (number of active neighbors) of a vertex in a graph.
-/
def vertex_degree (G : DynamicGraph n_theta) (v : Fin n_theta) : ℕ :=
  (Finset.univ.filter (fun w => (v, w) ∈ G.active_edges)).card

/--
Key property: A graph has a leaf if some vertex has degree 1.
-/
def has_leaf (G : DynamicGraph n_theta) : Prop :=
  ∃ v, vertex_degree G v = 1

/--
Helper: Explicit degree computation for quenched graph
-/
lemma quenched_all_degree_2 (v : Fin n_theta) :
  vertex_degree (evolve_with_history .Quenched) v = 2 := by
  unfold vertex_degree evolve_with_history remove_edge theta_graph theta_active
  fin_cases v <;> rfl

/--
Key Lemma: The quenched graph has NO leaf vertices.
After breaking edge (1,2), all vertices have degree 2 (forms a 4-cycle).
-/
lemma quenched_no_leaf :
  ¬ has_leaf (evolve_with_history .Quenched) := by
  intro ⟨v, hv⟩
  have h2 := quenched_all_degree_2 v
  rw [hv] at h2
  norm_num at h2

/--
Key Lemma: The annealed graph HAS a leaf vertex.
After breaking edge (1,3), vertex 3 becomes a leaf (degree 1, connected only to 2).
-/
lemma annealed_has_leaf :
  has_leaf (evolve_with_history .Annealed) := by
  use 3
  unfold vertex_degree evolve_with_history remove_edge theta_graph theta_active
  rfl

/--
Topological Memory Theorem.

The final graph topology preserves information about the cooling schedule.
- Quenched (fast): No leaf vertices → "0" bit encoded in topology
- Annealed (slow): Has leaf vertex → "1" bit encoded in topology

Since isomorphism preserves vertex degrees, and one graph has a leaf while
the other doesn't, they cannot be isomorphic.

**The universe remembers how it was cooled.**
-/
theorem history_is_written_in_topology :
  ¬ IsIsomorphic (evolve_with_history .Quenched) (evolve_with_history .Annealed) := by

  intro h_iso
  obtain ⟨ψ, h_edges⟩ := h_iso

  -- Annealed has vertex 3 as a leaf
  have h_has_leaf := annealed_has_leaf
  obtain ⟨v_leaf, hv_deg⟩ := h_has_leaf

  -- The isomorphism ψ⁻¹ maps this to some vertex in quenched
  let v_image := ψ.symm v_leaf

  -- This vertex must also have degree 1 (isomorphism preserves degrees)
  have h_image_deg : vertex_degree (evolve_with_history .Quenched) v_image = 1 := by
    unfold vertex_degree at hv_deg ⊢
    -- The neighbors of v_image in quenched correspond to neighbors of v_leaf in annealed
    have h_card : (Finset.univ.filter (fun w => (v_image, w) ∈
                    (evolve_with_history .Quenched).active_edges)).card =
                  (Finset.univ.filter (fun w => (v_leaf, w) ∈
                    (evolve_with_history .Annealed).active_edges)).card := by
      -- The permutation ψ induces a bijection on neighbors
      apply Finset.card_bij (fun w _ => ψ w)
      · intro w hw
        simp [Finset.mem_filter] at hw ⊢
        have := h_edges v_image w
        unfold v_image at this
        simpa using this.mp hw
      · intro w1 w2 _ _ heq
        exact ψ.injective heq
      · intro w' hw'
        use ψ.symm w'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw' ⊢
        constructor
        · exact Equiv.apply_symm_apply ψ w'
        · have := h_edges v_image (ψ.symm w')
          simp [v_image] at this
          exact this.mpr hw'
    rw [h_card]
    exact hv_deg

  -- But quenched has no degree-1 vertices!
  have h_no_leaf := quenched_no_leaf
  unfold has_leaf at h_no_leaf
  exact h_no_leaf ⟨v_image, h_image_deg⟩

/--
Corollary: History is an injective encoding.

Different cooling schedules produce non-isomorphic topologies.
This proves the graph is a valid 1-bit memory device.
-/
theorem schedule_injection :
  ∀ (S₁ S₂ : CoolingSchedule),
    IsIsomorphic (evolve_with_history S₁) (evolve_with_history S₂) → S₁ = S₂ := by

  intro S₁ S₂ h_iso

  -- Case analysis on the schedules
  cases S₁ <;> cases S₂
  · rfl  -- Both Quenched
  · -- Quenched vs Annealed
    exfalso
    exact history_is_written_in_topology h_iso
  · -- Annealed vs Quenched
    exfalso
    -- Isomorphism is symmetric
    obtain ⟨ψ, h_edges⟩ := h_iso
    have h_sym : IsIsomorphic (evolve_with_history .Quenched)
                               (evolve_with_history .Annealed) := by
      use ψ.symm
      intro i j
      have := h_edges (ψ.symm i) (ψ.symm j)
      simpa using this.symm
    exact history_is_written_in_topology h_sym
  · rfl  -- Both Annealed

/--
The Smallest Unit of Hodge Memory.

A single bit of information (Quenched vs Annealed) has been written into
the bedrock of the universe - into its very topology.

This formalizes what physicists call "topological order": information stored
not in local degrees of freedom, but in the global structure of the manifold.
-/
def hodge_memory_bit (S : CoolingSchedule) : Bool :=
  match S with
  | .Quenched => false  -- "0": A universe broken by haste
  | .Annealed => true   -- "1": A universe broken by wisdom

theorem memory_is_readable (S : CoolingSchedule) :
  let G := evolve_with_history S
  hodge_memory_bit S = has_leaf G := by

  cases S
  · -- Quenched: no leaf → bit is false
    simp [hodge_memory_bit]
    exact quenched_no_leaf
  · -- Annealed: has leaf → bit is true
    simp [hodge_memory_bit]
    exact annealed_has_leaf

end DiscreteHodge
