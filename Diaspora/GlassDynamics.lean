/-
# Glassy Dynamics and The Landscape

Formalizing the "roughness" of the topological energy landscape.
We define when two resulting spacetimes are topologically distinct (non-isomorphic)
and formally state the condition for a "glassy" system: one with multiple,
distinct stable vacua.
-/

import Diaspora.TopologyDynamics
import Diaspora.Universe
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Defs

namespace DiscreteHodge

/-! ## Graph Isomorphism -/

/--
Two dynamic graphs are isomorphic if there exists a permutation of vertices
that preserves the edge structure.
-/
def IsIsomorphic {n : ℕ} (G₁ G₂ : DynamicGraph n) : Prop :=
  ∃ ψ : Equiv.Perm (Fin n),
    ∀ i j : Fin n, (i, j) ∈ G₁.active_edges ↔ (ψ i, ψ j) ∈ G₂.active_edges

/-- Isomorphism is an equivalence relation -/
theorem isomorphism_is_equivalence {n : ℕ} :
  Equivalence (@IsIsomorphic n) := by
  constructor
  · -- Reflexive
    intro G
    use Equiv.refl (Fin n)
    simp
  · -- Symmetric
    intro G₁ G₂ ⟨ψ, h⟩
    use ψ.symm
    intro i j
    specialize h (ψ.symm i) (ψ.symm j)
    simp at h
    exact h.symm
  · -- Transitive
    intro G₁ G₂ G₃ ⟨ψ₁, h₁⟩ ⟨ψ₂, h₂⟩
    use ψ₁.trans ψ₂
    intro i j
    rw [h₁, h₂]
    simp

/-! ## The Energy Landscape -/

/--
The set of all possible stable topologies (vacua) for a given constraint σ.
A graph is in the landscape if it is an equilibrium for the given constraints.
-/
def StableLandscape {n : ℕ} [Fintype (Fin n)] (σ : C1 n) (C_max : ℝ) : Set (DynamicGraph n) :=
  { G | ∃ ϕ, is_equilibrium G ϕ σ C_max }

/--
A system is "Glassy" if its landscape contains at least two non-isomorphic
stable configurations. This implies the vacuum is not unique; the final
physics depends on the history of the collapse.
-/
def IsGlassySystem {n : ℕ} [Fintype (Fin n)] (σ : C1 n) (C_max : ℝ) : Prop :=
  ∃ G₁ G₂ : DynamicGraph n,
    G₁ ∈ StableLandscape σ C_max ∧
    G₂ ∈ StableLandscape σ C_max ∧
    ¬ IsIsomorphic G₁ G₂

/-! ## Chaos and Sensitivity -/

/--
Sensitivity to Initial Conditions (The Butterfly Effect).
Small perturbations in the starting strain ϕ can lead to non-isomorphic
final topologies.
-/
def topological_sensitivity_statement
    {n : ℕ} [Fintype (Fin n)] [DecidableEq (DynamicGraph n)]
    (σ : C1 n) (C_max : ℝ) : Prop :=
  ∃ (G_start : DynamicGraph n) (ϕ₁ ϕ₂ : C0 n),
    -- The inputs are arbitrarily close
    (∀ i, |ϕ₁ i - ϕ₂ i| < 0.001) ∧
    -- But they evolve to topologically distinct universes
    -- We define "static solvers" that just apply the initial potential regardless of topology
    let solver₁ := fun (_ : DynamicGraph n) (_ : C1 n) => ϕ₁
    let solver₂ := fun (_ : DynamicGraph n) (_ : C1 n) => ϕ₂
    -- We extract the final graph (.1) from the simulation result
    let final₁ := (run_universe G_start σ C_max solver₁).1
    let final₂ := (run_universe G_start σ C_max solver₂).1
    ¬ IsIsomorphic final₁ final₂

end DiscreteHodge
