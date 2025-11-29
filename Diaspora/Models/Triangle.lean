/-
# Example: The Frustrated Tailed Triangle

A concrete realization of a Glassy System.
We construct a graph (Triangle + Tail) and a constraint σ that frustrates the loop.
We show that the landscape contains two non-isomorphic stable vacua:
1. A "Star" graph (breaking the far edge).
2. A "Line" graph (breaking a near edge).
-/

import Diaspora.Dynamics.Glass
import Diaspora.Dynamics.Sim
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith

open BigOperators Diaspora.Core Diaspora.Hodge Diaspora.Dynamics

namespace Diaspora.Models

/-! ## Setup: The Graph and Constraints -/

/-- N = 4 vertices. 0,1,2 are the triangle. 3 is the tail attached to 0. -/
abbrev n_kite : ℕ := 4

/--
The initial "Kite" graph (Triangle 0-1-2 + Tail 0-3).
-/
def kite_graph : DynamicGraph n_kite where
  active_edges := {(0,1), (1,0), (1,2), (2,1), (2,0), (0,2), (0,3), (3,0)}
  symmetric := by
    intro i j
    simp
    tauto
  no_loops := by
    intro i
    simp
    fin_cases i <;> decide

/--
Frustrated Constraints:
- The loop 0->1->2->0 wants flow +1.
- The tail 0->3 is relaxed (flow 0).
-/
def frustrated_sigma : C1 n_kite := {
  val := fun i j =>
    if i = 0 ∧ j = 1 then 1
    else if i = 1 ∧ j = 2 then 1
    else if i = 2 ∧ j = 0 then 1
    else if i = 1 ∧ j = 0 then -1
    else if i = 2 ∧ j = 1 then -1
    else if i = 0 ∧ j = 2 then -1
    else 0
  skew := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp <;> (try ring_nf) <;> (split_ifs <;> norm_num)
}

/-! ## Fin Constructor Normalization -/

@[simp] lemma fin_mk_two : ⟨2, (by decide : 2 < n_kite)⟩ = (2 : Fin n_kite) := rfl
@[simp] lemma fin_mk_three : ⟨3, (by decide : 3 < n_kite)⟩ = (3 : Fin n_kite) := rfl

/-! ## Candidate Vacua -/

/--
Vacuum 1: The "Star" Graph.
Formed by breaking the edge (1,2) (the edge "far" from the tail).
Edges remaining: (0,1), (0,2), (0,3).
Center 0 has degree 3.
-/
def star_graph : DynamicGraph n_kite :=
  remove_edge kite_graph 1 2

/--
Vacuum 2: The "Line" Graph.
Formed by breaking the edge (0,1) (an edge "near" the tail).
Edges remaining: (3,0), (0,2), (2,1).
Path: 3-0-2-1. Max degree is 2.
-/
def line_graph : DynamicGraph n_kite :=
  remove_edge kite_graph 0 1

/-! ## Stability Proofs -/

def star_potential (σ : C1 n_kite) : C0 n_kite := fun v =>
  match v with
  | 0 => 0
  | 1 => σ.val 0 1
  | 2 => σ.val 0 2
  | 3 => σ.val 0 3

lemma star_has_zero_strain (σ : C1 n_kite) :
    ∀ i j, (i, j) ∈ star_graph.active_edges → edge_strain (star_potential σ) σ i j = 0 := by
  intro i j h
  unfold edge_strain d0 star_potential star_graph remove_edge kite_graph at *
  fin_cases i <;> fin_cases j
  all_goals simp [Fin.ext_iff] at h ⊢
  all_goals try contradiction
  all_goals ring_nf
  all_goals rw [σ.skew]
  all_goals ring_nf

def line_potential (σ : C1 n_kite) : C0 n_kite := fun v =>
  match v with
  | 0 => σ.val 3 0
  | 1 => σ.val 3 0 + σ.val 0 2 + σ.val 2 1
  | 2 => σ.val 3 0 + σ.val 0 2
  | 3 => 0

lemma line_has_zero_strain (σ : C1 n_kite) :
    ∀ i j, (i, j) ∈ line_graph.active_edges → edge_strain (line_potential σ) σ i j = 0 := by
  intro i j h
  unfold edge_strain d0 line_potential line_graph remove_edge kite_graph at *
  fin_cases i <;> fin_cases j
  all_goals simp [Fin.ext_iff] at h ⊢
  all_goals try contradiction
  all_goals ring_nf
  all_goals rw [σ.skew]
  all_goals ring_nf

/--
Both Star and Line graphs are trees (cyclomatic number = 0).
Original edges = 4. Vertices = 4.
Remove 1 edge -> 3 edges.
Cyclomatic = E - V + 1 = 3 - 4 + 1 = 0.
-/
lemma star_is_tree : cyclomatic_number star_graph = 0 := by
  unfold cyclomatic_number star_graph edge_count
  unfold remove_edge kite_graph
  simp

lemma line_is_tree : cyclomatic_number line_graph = 0 := by
  unfold cyclomatic_number line_graph edge_count
  unfold remove_edge kite_graph
  simp

/-! ## Glassiness Proof -/

/--
The Star graph has a vertex of degree 3 (vertex 0).
-/
lemma star_has_degree_3 :
    ∃ i : Fin n_kite, (star_graph.active_edges.filter (fun x => x.1 = i)).card = 3 := by
  use 0
  unfold star_graph remove_edge kite_graph
  simp
  decide

/--
The Line graph has no vertex of degree 3 (max degree is 2).
-/
lemma line_max_degree_2 :
    ∀ i : Fin n_kite, (line_graph.active_edges.filter (fun x => x.1 = i)).card ≤ 2 := by
  intro i
  unfold line_graph remove_edge kite_graph
  fin_cases i <;> simp <;> decide

/--
Therefore, Star and Line are not isomorphic.
-/
theorem star_ne_line : ¬ IsIsomorphic star_graph line_graph := by
  intro h_iso
  rcases h_iso with ⟨ψ, h_map⟩
  obtain ⟨i_star, h_deg_star⟩ := star_has_degree_3
  have h_deg_line := line_max_degree_2 (ψ i_star)
  -- Isomorphism preserves degree
  have deg_preserved : (star_graph.active_edges.filter (fun x => x.1 = i_star)).card =
                       (line_graph.active_edges.filter (fun x => x.1 = ψ i_star)).card := by
    apply Finset.card_bij (fun e _ => (ψ e.1, ψ e.2))
    · intro e h_e
      simp only [Finset.mem_filter] at h_e ⊢
      exact ⟨(h_map e.1 e.2).mp h_e.1, by rw [h_e.2]⟩
    · intro e₁ e₂ h₁ h₂ h_eq
      have h1 := ψ.injective (Prod.ext_iff.mp h_eq).1
      have h2 := ψ.injective (Prod.ext_iff.mp h_eq).2
      ext <;> simp [h1, h2]
    · intro e' h_e'
      use (ψ.symm e'.1, ψ.symm e'.2)
      simp only [Finset.mem_filter] at h_e' ⊢
      refine ⟨⟨(h_map (ψ.symm e'.1) (ψ.symm e'.2)).mpr (by simp; exact h_e'.1), ?_⟩, by simp⟩
      simp [h_e'.2]
  rw [h_deg_star] at deg_preserved
  omega

/--
THE MAIN THEOREM:
The Tailed Triangle is a Glassy System.
-/
theorem tailed_triangle_is_glassy (C_max : ℝ) (h_pos : C_max ≥ 0) :
    IsGlassySystem frustrated_sigma C_max := by
  use star_graph, line_graph
  constructor
  · -- Star is in landscape
    unfold StableLandscape is_equilibrium
    use star_potential frustrated_sigma
    intro i j h_active
    rw [star_has_zero_strain frustrated_sigma i j h_active]
    exact h_pos
  constructor
  · -- Line is in landscape
    unfold StableLandscape is_equilibrium
    use line_potential frustrated_sigma
    intro i j h_active
    rw [line_has_zero_strain frustrated_sigma i j h_active]
    exact h_pos
  · -- They are distinct
    exact star_ne_line

/-! ## Evolution: Proof-Carrying Paths to Vacua -/

/-- Edge (1,2) is active in the kite graph. -/
lemma kite_has_edge_12 : (1, 2) ∈ kite_graph.active_edges := by decide

/-- Edge (0,1) is active in the kite graph. -/
lemma kite_has_edge_01 : (0, 1) ∈ kite_graph.active_edges := by decide

/--
The evolution chain from kite to star: break edge (1,2).
This is a proof-carrying object - the chain itself witnesses that the transition was valid.
-/
def kite_to_star_chain : EvolutionChain n_kite frustrated_sigma star_graph :=
  EvolutionChain.step (EvolutionChain.genesis kite_graph) 1 2 kite_has_edge_12

/--
The evolution chain from kite to line: break edge (0,1).
-/
def kite_to_line_chain : EvolutionChain n_kite frustrated_sigma line_graph :=
  EvolutionChain.step (EvolutionChain.genesis kite_graph) 0 1 kite_has_edge_01

/-- Both chains originate from the same graph. -/
theorem same_origin :
    kite_to_star_chain.origin = kite_graph ∧ kite_to_line_chain.origin = kite_graph := by
  constructor <;> rfl

/-- Breaking edge (1,2) increases latent capacity by σ(1,2)². -/
theorem star_entropy_increase :
    latent_capacity star_graph frustrated_sigma =
    latent_capacity kite_graph frustrated_sigma + (frustrated_sigma.val 1 2)^2 :=
  latent_capacity_growth kite_graph frustrated_sigma 1 2 kite_has_edge_12

/-- Breaking edge (0,1) increases latent capacity by σ(0,1)². -/
theorem line_entropy_increase :
    latent_capacity line_graph frustrated_sigma =
    latent_capacity kite_graph frustrated_sigma + (frustrated_sigma.val 0 1)^2 :=
  latent_capacity_growth kite_graph frustrated_sigma 0 1 kite_has_edge_01

/--
THE DYNAMICAL GLASSINESS THEOREM:
The same initial condition (kite_graph) can evolve to two distinct, non-isomorphic
stable configurations via valid evolution chains.
-/
theorem dynamical_glassiness :
    ∃ (chain_star : EvolutionChain n_kite frustrated_sigma star_graph)
      (chain_line : EvolutionChain n_kite frustrated_sigma line_graph),
      chain_star.origin = chain_line.origin ∧ ¬ IsIsomorphic star_graph line_graph :=
  ⟨kite_to_star_chain, kite_to_line_chain, rfl, star_ne_line⟩

end Diaspora.Models
