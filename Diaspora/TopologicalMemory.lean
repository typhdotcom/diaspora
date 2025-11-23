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

inductive CoolingSchedule
| Quenched
| Annealed
deriving DecidableEq

noncomputable def evolve_with_history (S : CoolingSchedule) : DynamicGraph n_theta :=
  match S with
  | .Quenched => remove_edge theta_graph 1 2
  | .Annealed => remove_edge theta_graph 1 3

def vertex_degree (G : DynamicGraph n_theta) (v : Fin n_theta) : ℕ :=
  (Finset.univ.filter (fun w => (v, w) ∈ G.active_edges)).card

def has_leaf (G : DynamicGraph n_theta) : Prop :=
  ∃ v, vertex_degree G v = 1

lemma quenched_all_degree_2 (v : Fin n_theta) :
  vertex_degree (evolve_with_history .Quenched) v = 2 := by
  unfold vertex_degree evolve_with_history remove_edge theta_graph theta_active
  fin_cases v <;> rfl

lemma quenched_no_leaf :
  ¬ has_leaf (evolve_with_history .Quenched) := by
  intro ⟨v, hv⟩
  have h2 := quenched_all_degree_2 v
  rw [hv] at h2
  norm_num at h2

lemma annealed_has_leaf :
  has_leaf (evolve_with_history .Annealed) := by
  use 3
  unfold vertex_degree evolve_with_history remove_edge theta_graph theta_active
  rfl

/--
Quenched and annealed graphs are non-isomorphic.
Isomorphism would preserve degrees, but one has a leaf and the other doesn't.
-/
theorem history_is_written_in_topology :
  ¬ IsIsomorphic (evolve_with_history .Quenched) (evolve_with_history .Annealed) := by
  intro h_iso
  obtain ⟨ψ, h_edges⟩ := h_iso
  have h_has_leaf := annealed_has_leaf
  obtain ⟨v_leaf, hv_deg⟩ := h_has_leaf
  let v_image := ψ.symm v_leaf
  have h_image_deg : vertex_degree (evolve_with_history .Quenched) v_image = 1 := by
    unfold vertex_degree at hv_deg ⊢
    have h_card : (Finset.univ.filter (fun w => (v_image, w) ∈
                    (evolve_with_history .Quenched).active_edges)).card =
                  (Finset.univ.filter (fun w => (v_leaf, w) ∈
                    (evolve_with_history .Annealed).active_edges)).card := by
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
  have h_no_leaf := quenched_no_leaf
  unfold has_leaf at h_no_leaf
  exact h_no_leaf ⟨v_image, h_image_deg⟩

theorem schedule_injection :
  ∀ (S₁ S₂ : CoolingSchedule),
    IsIsomorphic (evolve_with_history S₁) (evolve_with_history S₂) → S₁ = S₂ := by
  intro S₁ S₂ h_iso
  cases S₁ <;> cases S₂
  · rfl
  · exfalso
    exact history_is_written_in_topology h_iso
  · exfalso
    obtain ⟨ψ, h_edges⟩ := h_iso
    have h_sym : IsIsomorphic (evolve_with_history .Quenched)
                               (evolve_with_history .Annealed) := by
      use ψ.symm
      intro i j
      have := h_edges (ψ.symm i) (ψ.symm j)
      simpa using this.symm
    exact history_is_written_in_topology h_sym
  · rfl

def hodge_memory_bit (S : CoolingSchedule) : Bool :=
  match S with
  | .Quenched => false
  | .Annealed => true

theorem memory_is_readable (S : CoolingSchedule) :
  let G := evolve_with_history S
  hodge_memory_bit S = has_leaf G := by
  cases S
  · simp [hodge_memory_bit]
    exact quenched_no_leaf
  · simp [hodge_memory_bit]
    exact annealed_has_leaf

end DiscreteHodge
