/-
# Spectral Memory

"Can one hear the shape of a cooling schedule?"

This file proves that the Laplacian Spectrum (specifically the second moment,
or spectral variance) is distinct for the Quenched and Annealed histories.
-/

import Diaspora.TopologicalMemory
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace DiscreteHodge

open BigOperators Matrix

/-! ## Matrix Definitions -/

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Adjacency Matrix: A_ij = 1 if connected, 0 otherwise -/
def adjacency_matrix (G : DynamicGraph n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if (i, j) ∈ G.active_edges then 1 else 0

/-- Degree Matrix: D_ii = degree(i), 0 otherwise -/
def degree_matrix (G : DynamicGraph n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => (vertex_degree G i : ℝ))

/-- Laplacian Matrix: L = D - A -/
def laplacian_matrix (G : DynamicGraph n) : Matrix (Fin n) (Fin n) ℝ :=
  (degree_matrix G) - (adjacency_matrix G)

/-! ## Spectral Invariants -/

noncomputable def spectral_variance (G : DynamicGraph n) : ℝ :=
  Matrix.trace (laplacian_matrix G ^ 2)

theorem spectral_variance_eq_sum_sq_plus_sum (G : DynamicGraph n) :
  spectral_variance G = ∑ i, ((vertex_degree G i : ℝ) ^ 2 + (vertex_degree G i : ℝ)) := by
  unfold spectral_variance laplacian_matrix
  
  -- 1. Expansion: (D-A)^2 = D^2 - DA - AD + A^2
  rw [pow_two]
  rw [sub_mul, mul_sub, mul_sub]
  simp only [Matrix.trace_sub]

  -- 2. D^2 term
  have h_D2 : (degree_matrix G * degree_matrix G).trace = ∑ i, (vertex_degree G i : ℝ) ^ 2 := by
    unfold degree_matrix
    rw [Matrix.trace_mul_comm, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    apply Finset.sum_congr rfl
    intro i _
    simp only [pow_two]

  -- 3. DA term (Zero)
  have h_DA : (degree_matrix G * adjacency_matrix G).trace = 0 := by
    simp only [Matrix.trace, degree_matrix, adjacency_matrix, Matrix.diagonal, Matrix.diag, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro x _
    apply Finset.sum_eq_zero
    intro y _
    all_goals {simp; intro h_edge h_eq; subst h_eq; exact absurd h_edge (G.no_loops _)}

  -- 4. AD term (Zero via trace commutativity)
  have h_AD : (adjacency_matrix G * degree_matrix G).trace = 0 := by
    rw [Matrix.trace_mul_comm]
    exact h_DA

  -- 5. A^2 term
  have h_A2 : (adjacency_matrix G * adjacency_matrix G).trace = ∑ i, (vertex_degree G i : ℝ) := by
    unfold adjacency_matrix vertex_degree Matrix.trace
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.diag, Matrix.mul_apply]
    -- Use symmetry: A_ij * A_ji = A_ij * A_ij = A_ij (since 0-1 and symmetric)
    trans (∑ j, if (i,j) ∈ G.active_edges then (1:ℝ) else 0)
    · apply Finset.sum_congr rfl; intro j _
      by_cases h : (i,j) ∈ G.active_edges
      · simp [h, (G.symmetric i j).mp h]
      · simp [h]
    · norm_cast; simp [Finset.sum_boole]; convert rfl using 2; ext; simp
  
  rw [h_D2, h_DA, h_AD, h_A2]
  simp only [sub_zero, zero_sub, sub_neg_eq_add]
  rw [←Finset.sum_add_distrib]

/-! ## The Calculation -/

/-- Quenched (Cycle): Tr(L²) = 24 -/
theorem quenched_variance_val :
  spectral_variance (evolve_with_history .Quenched) = 24 := by
  rw [spectral_variance_eq_sum_sq_plus_sum]
  rw [Fin.sum_univ_four]
  have h_deg : ∀ i, vertex_degree (evolve_with_history .Quenched) i = 2 :=
    quenched_all_degree_2
  simp [h_deg]
  norm_num

/-- Annealed (Tadpole): Tr(L²) = 26 -/
theorem annealed_variance_val :
  spectral_variance (evolve_with_history .Annealed) = 26 := by
  rw [spectral_variance_eq_sum_sq_plus_sum]
  rw [Fin.sum_univ_four]
  
  -- We use a direct expansion approach to avoid Fin literal unification issues
  let G := evolve_with_history .Annealed
  
  -- Calculate degrees explicitly for 0, 1, 2, 3
  have h0 : vertex_degree G 0 = 2 := by rfl
  have h1 : vertex_degree G 1 = 2 := by rfl
  have h2 : vertex_degree G 2 = 3 := by rfl
  have h3 : vertex_degree G 3 = 1 := by rfl

  rw [h0, h1, h2, h3]
  norm_num

/-! ## The Conclusions -/

/-- 
Theorem: History is Audible.
The energy spectrum variance differs between the two histories.
-/
theorem history_is_audible :
  spectral_variance (evolve_with_history .Quenched) ≠ 
  spectral_variance (evolve_with_history .Annealed) := by
  rw [quenched_variance_val, annealed_variance_val]
  norm_num

/--
Active Retrieval.
If Tr(L²) > 25, the system was annealed.
Returns Prop to ensure physical realism (computability issue).
-/
def was_annealed_spectrally (G : DynamicGraph n_theta) : Prop :=
  spectral_variance G > 25

theorem spectral_memory_works :
  was_annealed_spectrally (evolve_with_history .Annealed) ∧ 
  ¬ was_annealed_spectrally (evolve_with_history .Quenched) := by
  unfold was_annealed_spectrally
  constructor
  · rw [annealed_variance_val]; norm_num
  · rw [quenched_variance_val]; norm_num

end DiscreteHodge
