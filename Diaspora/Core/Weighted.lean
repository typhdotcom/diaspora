import Diaspora.Core.Calculus
import Diaspora.Core.Phase
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Diaspora.Core
open BigOperators

/-- A graph where edges have continuous capacity (weights). -/
structure WeightedGraph (n : ℕ) where
  weights : Fin n → Fin n → ℝ
  symmetric : ∀ i j, weights i j = weights j i
  nonneg : ∀ i j, 0 ≤ weights i j
  /-- Conservation of Attention: The total capacity of the universe is fixed. -/
  total_capacity_fixed : ∑ i, ∑ j, weights i j = (n : ℝ)^2

/-- The pure potential difference, unmitigated by capacity. -/
def raw_strain {n : ℕ} (ϕ : C0 n) (σ : C1 n) (i j : Fin n) : ℝ :=
  ((d0 ϕ).val i j - σ.val i j)^2

/-- raw_strain is symmetric: squaring an antisymmetric function yields symmetry. -/
lemma raw_strain_symm {n : ℕ} (ϕ : C0 n) (σ : C1 n) (i j : Fin n) :
    raw_strain ϕ σ i j = raw_strain ϕ σ j i := by
  unfold raw_strain d0
  simp only
  have h1 : (ϕ j - ϕ i) = -(ϕ i - ϕ j) := by ring
  have h2 : σ.val i j = -σ.val j i := σ.skew i j
  calc ((ϕ j - ϕ i) - σ.val i j)^2
     = (-(ϕ i - ϕ j) - -σ.val j i)^2 := by rw [h1, h2]
   _ = ((ϕ i - ϕ j) - σ.val j i)^2 := by ring_nf

/-- raw_strain is non-negative (it's a square). -/
lemma raw_strain_nonneg {n : ℕ} (ϕ : C0 n) (σ : C1 n) (i j : Fin n) :
    0 ≤ raw_strain ϕ σ i j := sq_nonneg _

/-- Phase-aware strain using geodesic distance.
    Respects the cyclic boundary of phase fields. -/
noncomputable def phase_strain {n k : ℕ} [NeZero k]
    (ϕ : PC0 n k) (σ : PC1 n k) (i j : Fin n) : ℝ :=
  let delta := (pd0 ϕ).val i j - σ.val i j
  (geodesic_dist delta 0 : ℝ)^2

/-- Phase strain is symmetric. -/
lemma phase_strain_symm {n k : ℕ} [NeZero k] (ϕ : PC0 n k) (σ : PC1 n k) (i j : Fin n) :
    phase_strain ϕ σ i j = phase_strain ϕ σ j i := by
  unfold phase_strain pd0
  simp only
  have h1 : (ϕ j - ϕ i) = -(ϕ i - ϕ j) := by ring
  have h2 : σ.val i j = -σ.val j i := σ.skew i j
  have h_delta_eq : (ϕ j - ϕ i) - σ.val i j = -((ϕ i - ϕ j) - σ.val j i) := by
    calc (ϕ j - ϕ i) - σ.val i j
        = -(ϕ i - ϕ j) - -σ.val j i := by rw [h1, h2]
      _ = -((ϕ i - ϕ j) - σ.val j i) := by ring
  rw [h_delta_eq, geodesic_dist_neg]

/-- Phase strain is non-negative. -/
lemma phase_strain_nonneg {n k : ℕ} [NeZero k] (ϕ : PC0 n k) (σ : PC1 n k) (i j : Fin n) :
    0 ≤ phase_strain ϕ σ i j := sq_nonneg _

/-- Converts a WeightedGraph into a DynamicGraph by thresholding. -/
noncomputable def to_dynamic {n : ℕ} (G : WeightedGraph n) (ε : ℝ) : DynamicGraph n where
  active_edges :=
    (Finset.univ.product Finset.univ).filter (fun p => G.weights p.1 p.2 ≥ ε ∧ p.1 ≠ p.2)

  symmetric := by
    intro i j
    simp only [Finset.mem_filter]
    rw [G.symmetric i j, ne_comm]
    simp [Finset.mem_univ]

  no_loops := by
    intro i
    simp only [Finset.mem_filter]
    intro h
    exact h.2.2 rfl


end Diaspora.Core
