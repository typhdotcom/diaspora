/-
Universe evolution via proof-carrying simulation.
-/

import Diaspora.Dynamics.Transition
import Diaspora.Core.Calculus

open BigOperators Diaspora.Core

namespace Diaspora.Dynamics

/-! ## The Evolution Chain -/

/--
A chain of evolution steps where each transition is valid by construction.
-/
inductive EvolutionChain (n : ℕ) [Fintype (Fin n)] (σ : C1 n) : DynamicGraph n → Type where
  | genesis : (G : DynamicGraph n) → EvolutionChain n σ G
  | step :
      {G : DynamicGraph n} →
      EvolutionChain n σ G →
      (i j : Fin n) →
      (h_active : (i, j) ∈ G.active_edges) →
      EvolutionChain n σ (remove_edge G i j)

/-- Extract the initial graph from a chain -/
def EvolutionChain.origin {n : ℕ} [Fintype (Fin n)] {σ : C1 n} {G : DynamicGraph n}
    (chain : EvolutionChain n σ G) : DynamicGraph n :=
  match chain with
  | .genesis G₀ => G₀
  | .step prev _ _ _ => prev.origin

/-- The number of breaks in a chain -/
def EvolutionChain.length {n : ℕ} [Fintype (Fin n)] {σ : C1 n} {G : DynamicGraph n}
    (chain : EvolutionChain n σ G) : ℕ :=
  match chain with
  | .genesis _ => 0
  | .step prev _ _ _ => prev.length + 1

/-! ## The Entropy Law -/

/--
Each step increases latent capacity by the square of the constraint on the broken edge.
-/
theorem step_entropy_growth {n : ℕ} [Fintype (Fin n)] {σ : C1 n} {G : DynamicGraph n}
    (i j : Fin n) (h_active : (i, j) ∈ G.active_edges) :
    latent_capacity (remove_edge G i j) σ = latent_capacity G σ + (σ.val i j)^2 :=
  latent_capacity_growth G σ i j h_active

/--
Latent capacity is non-decreasing through any evolution chain.
-/
theorem chain_entropy_nondecreasing {n : ℕ} [Fintype (Fin n)] {σ : C1 n} {G : DynamicGraph n}
    (chain : EvolutionChain n σ G) :
    latent_capacity G σ ≥ latent_capacity chain.origin σ := by
  induction chain with
  | genesis G₀ => rfl
  | step prev i j h_active ih =>
    simp only [EvolutionChain.origin, step_entropy_growth i j h_active]
    linarith [sq_nonneg (σ.val i j)]

/-! ## The Verified Simulation Engine -/

/--
Evolve a chain until equilibrium.
-/
noncomputable def evolve {n : ℕ} [Fintype (Fin n)] [DecidableEq (DynamicGraph n)]
    {σ : C1 n} {G : DynamicGraph n}
    (chain : EvolutionChain n σ G)
    (C_max : ℝ)
    (solver : DynamicGraph n → C1 n → C0 n)
    : Σ G_final : DynamicGraph n, EvolutionChain n σ G_final :=

  let phi := solver G σ
  match h_find : find_overstressed_edge G phi σ C_max with
  | none =>
      ⟨G, chain⟩

  | some (i, j) =>
      have h_active : (i, j) ∈ G.active_edges :=
        (find_overstressed_edge_spec G phi σ C_max i j h_find).1

      let next_chain := EvolutionChain.step chain i j h_active
      let G_next := remove_edge G i j

      have _h_card : G_next.active_edges.card < G.active_edges.card := by
        simp only [G_next, remove_edge]
        calc ((G.active_edges.erase (i, j)).erase (j, i)).card
            ≤ (G.active_edges.erase (i, j)).card := Finset.card_erase_le
          _ < G.active_edges.card := Finset.card_lt_card (Finset.erase_ssubset h_active)

      evolve next_chain C_max solver

termination_by G.active_edges.card

/--
Run the universe from an initial graph.
-/
noncomputable def run_universe {n : ℕ} [Fintype (Fin n)] [DecidableEq (DynamicGraph n)]
    (G₀ : DynamicGraph n)
    (σ : C1 n)
    (C_max : ℝ)
    (solver : DynamicGraph n → C1 n → C0 n)
    : Σ G_final : DynamicGraph n, EvolutionChain n σ G_final :=
  evolve (EvolutionChain.genesis G₀) C_max solver

/-! ## Origin Preservation -/

/-- Origin is preserved when extending a chain by one step -/
@[simp]
lemma origin_step {n : ℕ} [Fintype (Fin n)] {σ : C1 n} {G : DynamicGraph n}
    (chain : EvolutionChain n σ G) (i j : Fin n) (h : (i, j) ∈ G.active_edges) :
    (EvolutionChain.step chain i j h).origin = chain.origin := rfl

/-- Origin is preserved through evolution -/
theorem evolve_preserves_origin {n : ℕ} [Fintype (Fin n)] [DecidableEq (DynamicGraph n)]
    {σ : C1 n} {G : DynamicGraph n}
    (chain : EvolutionChain n σ G)
    (C_max : ℝ)
    (solver : DynamicGraph n → C1 n → C0 n) :
    (evolve chain C_max solver).2.origin = chain.origin := by
  rw [evolve]
  split
  · rfl
  · rename_i i j h_find
    have h_active : (i, j) ∈ G.active_edges :=
      (find_overstressed_edge_spec G (solver G σ) σ C_max i j h_find).1
    dsimp only
    have _h_card : (remove_edge G i j).active_edges.card < G.active_edges.card := by
      simp only [remove_edge]
      calc ((G.active_edges.erase (i, j)).erase (j, i)).card
          ≤ (G.active_edges.erase (i, j)).card := Finset.card_erase_le
        _ < G.active_edges.card := Finset.card_lt_card (Finset.erase_ssubset h_active)
    exact evolve_preserves_origin _ C_max solver
termination_by G.active_edges.card

/-! ## The Main Theorem -/

/--
The simulation produces a universe where entropy has not decreased.
-/
theorem simulation_entropy_nondecreasing {n : ℕ} [Fintype (Fin n)] [DecidableEq (DynamicGraph n)]
    (G₀ : DynamicGraph n) (σ : C1 n) (C_max : ℝ) (solver : DynamicGraph n → C1 n → C0 n) :
    let result := run_universe G₀ σ C_max solver
    latent_capacity result.1 σ ≥ latent_capacity G₀ σ := by
  simp only [run_universe]
  let res := evolve (σ := σ) (EvolutionChain.genesis G₀) C_max solver
  have h := chain_entropy_nondecreasing res.2
  have h_origin := evolve_preserves_origin (σ := σ) (EvolutionChain.genesis G₀) C_max solver
  simp only [EvolutionChain.origin] at h_origin
  rw [h_origin] at h
  exact h

end Diaspora.Dynamics
