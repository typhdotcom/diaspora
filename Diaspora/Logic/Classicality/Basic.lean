import Diaspora.Core.Calculus
import Diaspora.Hodge.Decomposition
import Mathlib.Order.WellFounded
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Diaspora.Logic

open Diaspora.Core Diaspora.Hodge

variable {n : ℕ} [Fintype (Fin n)]

/--
Convert a DynamicGraph to a SimpleGraph (forgetting orientation, keeping adjacency).
-/
def DynamicGraph.toSimpleGraph (G : DynamicGraph n) : SimpleGraph (Fin n) where
  Adj := fun i j => (i, j) ∈ G.active_edges
  symm := fun i j h => (G.symmetric i j).mp h
  loopless := fun i h => G.no_loops i h

/-- A 'Classical' universe is one where the Harmonic subspace is empty. -/
def IsClassical (G : DynamicGraph n) : Prop :=
  Module.finrank ℝ (HarmonicSubspace G) = 0

/-- Membership defined by Gradient Flow: child lies at lower potential than parent. -/
def IsMember (G : DynamicGraph n) (ϕ : C0 n) (child parent : Fin n) : Prop :=
  (parent, child) ∈ G.active_edges ∧ (ϕ parent > ϕ child)

/-- A potential is 'Faithful' if it orients every active edge (no ties). -/
def IsFaithfulPotential (G : DynamicGraph n) (ϕ : C0 n) : Prop :=
  ∀ i j, (i, j) ∈ G.active_edges → ϕ i ≠ ϕ j

/-- IsMember is well-founded for any potential on a finite graph. -/
theorem isMember_wellFounded (G : DynamicGraph n) (ϕ : C0 n) :
    WellFounded (IsMember G ϕ) := by
  let gtPot : Fin n → Fin n → Prop := fun child parent => ϕ parent > ϕ child
  have h_sub : Subrelation (IsMember G ϕ) gtPot := @fun x y h => h.2
  have h_trans : IsTrans (Fin n) gtPot := ⟨fun _ _ _ hab hbc => lt_trans hab hbc⟩
  have h_irrefl : IsIrrefl (Fin n) gtPot := ⟨fun _ h => lt_irrefl _ h⟩
  have h_wf : WellFounded gtPot := @Finite.wellFounded_of_trans_of_irrefl _ _ _ h_trans h_irrefl
  exact Subrelation.wf h_sub h_wf

end Diaspora.Logic
