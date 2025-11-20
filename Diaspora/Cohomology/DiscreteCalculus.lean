/-
# Discrete Calculus on Graphs

Foundational definitions for discrete exterior calculus: chain complexes,
cochains, inner products, and differential operators.

This file contains only definitions and basic identities. Heavy proofs are
delegated to HodgeDecomposition.lean.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith

open BigOperators Complex

namespace DiscreteHodge

/-! ## Classical Cochains -/

/-- A 0-cochain is a function on vertices (Phases) -/
def C0 (n : ℕ) := Fin n → ℝ

/-- A 1-cochain is a skew-symmetric function on edges (Constraints/Flux) -/
structure C1 (n : ℕ) where
  val : Fin n → Fin n → ℝ
  skew : ∀ i j, val i j = -val j i

/-- The Coboundary Operator d⁰: C⁰ → C¹ (Gradient) -/
def d0 {n : ℕ} (ϕ : C0 n) : C1 n := {
  val := fun i j => ϕ j - ϕ i
  skew := by intro i j; ring
}

/-- Inner product on 1-cochains (sum over unique edges) -/
noncomputable def inner_product_C1 {n : ℕ} [Fintype (Fin n)] (σ τ : C1 n) : ℝ :=
  (1/2) * ∑ i : Fin n, ∑ j : Fin n, (σ.val i j) * (τ.val i j)

/-- Squared Norm of a 1-cochain -/
noncomputable def norm_sq {n : ℕ} [Fintype (Fin n)] (σ : C1 n) : ℝ := inner_product_C1 σ σ

/-- The residual: dϕ - σ -/
noncomputable def residual {n : ℕ} (ϕ : C0 n) (σ : C1 n) : C1 n :=
  { val := fun i j => (d0 ϕ).val i j - σ.val i j,
    skew := by intro i j; simp [d0]; rw [σ.skew]; ring }

/-- Harmonic forms: divergence-free at every node -/
def IsHarmonic {n : ℕ} [Fintype (Fin n)] (σ : C1 n) : Prop :=
  ∀ i : Fin n, ∑ j : Fin n, σ.val i j = 0

/--
Harmonic Flow Conservation (Kirchhoff's Current Law).

If a node `i` acts as a bridge strictly between `prev` and `next`
(meaning γ is zero on all other edges connected to `i`),
then the harmonic flow entering from `prev` must exactly equal the flow exiting to `next`.

This reduces solving harmonic forms on cycles from N linear equations to 1 variable.
-/
lemma harmonic_flow_transfer {n : ℕ} [Fintype (Fin n)]
  (γ : C1 n) (i prev next : Fin n)
  (h_harm : IsHarmonic γ)
  (h_isolation : ∀ x, x ≠ prev ∧ x ≠ next → γ.val i x = 0) :
  γ.val prev i = γ.val i next := by
  have h_div_zero := h_harm i
  unfold IsHarmonic at h_div_zero

  let relevant : Finset (Fin n) := {prev, next}

  rw [←Finset.sum_subset (s₁ := relevant)] at h_div_zero
  swap
  · simp
  swap
  · intro x _ hx
    have : x ≠ prev ∧ x ≠ next := by
      unfold relevant at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      push_neg at hx
      exact hx
    exact h_isolation x this

  by_cases h : prev = next
  · subst h
    have : γ.val i prev = 0 := by
      have eq : ({prev, prev} : Finset (Fin n)) = {prev} := by simp
      have : ∑ x ∈ relevant, γ.val i x = ∑ x ∈ ({prev} : Finset (Fin n)), γ.val i x := by
        unfold relevant
        rw [eq]
      rw [this] at h_div_zero
      simp at h_div_zero
      exact h_div_zero
    rw [γ.skew prev i, this]
    linarith
  · simp only [relevant, Finset.sum_insert, Finset.mem_singleton, h, not_false_eq_true, Finset.sum_singleton] at h_div_zero
    rw [γ.skew i prev] at h_div_zero
    linarith

/-- The divergence operator d*: C¹ → C⁰ (negative adjoint of coboundary) -/
noncomputable def divergence {n : ℕ} [Fintype (Fin n)] (σ : C1 n) : C0 n :=
  fun i => - ∑ j : Fin n, σ.val i j

/-- divergence is the (negative) adjoint of d0 under the inner product -/
lemma divergence_is_adjoint {n : ℕ} [Fintype (Fin n)] (ϕ : C0 n) (σ : C1 n) :
  inner_product_C1 (d0 ϕ) σ = ∑ i : Fin n, ϕ i * divergence σ i := by
  unfold inner_product_C1 d0 divergence
  simp only
  have key : ∑ i : Fin n, ∑ j : Fin n, (ϕ j - ϕ i) * σ.val i j = 2 * ∑ i : Fin n, ϕ i * (-∑ j : Fin n, σ.val i j) := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    conv_lhs =>
      enter [1]
      rw [Finset.sum_comm]
    conv_lhs =>
      enter [1, 2, i, 2, j]
      rw [σ.skew]
    simp only [mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, two_mul, Finset.sum_add_distrib]
    ring
  rw [key]
  ring

/-- The graph Laplacian Δ = d* ∘ d: C⁰ → C⁰ -/
noncomputable def graph_laplacian {n : ℕ} [Fintype (Fin n)] (ϕ : C0 n) : C0 n :=
  divergence (d0 ϕ)

/-- The basis vector at index k (1 at k, 0 elsewhere) -/
def basis_vector {n : ℕ} (k : Fin n) : C0 n :=
  fun i => if i = k then 1 else 0

/-- Δϕ = lam·ϕ -/
def IsEigenvector {n : ℕ} [Fintype (Fin n)] (ϕ : C0 n) (lam : ℝ) : Prop :=
  ∀ i : Fin n, graph_laplacian ϕ i = lam * ϕ i

/-! ## Chains -/

/--
  A 1-chain is a formal integer linear combination of oriented edges.

  We represent this as an antisymmetric function Fin n → Fin n → ℤ,
  where c i j represents the coefficient of the oriented edge (i,j).

  For example, a path 0→1→2 is represented as:
  - c 0 1 = 1, c 1 2 = 1, all others = 0
-/
structure Chain1 (n : ℕ) where
  coeff : Fin n → Fin n → ℤ
  antisym : ∀ i j, coeff i j = -coeff j i

/-- The zero 1-chain (no edges) -/
def Chain1.zero (n : ℕ) : Chain1 n := {
  coeff := fun _ _ => 0
  antisym := by intro i j; ring
}

/-- Addition of 1-chains (formal sum) -/
def Chain1.add {n : ℕ} (c₁ c₂ : Chain1 n) : Chain1 n := {
  coeff := fun i j => c₁.coeff i j + c₂.coeff i j
  antisym := by intro i j; rw [c₁.antisym, c₂.antisym]; ring
}

/-- A 1-chain is a cycle if it has no boundary (each vertex has equal in-degree and out-degree) -/
def Chain1.IsCycle {n : ℕ} [Fintype (Fin n)] (c : Chain1 n) : Prop :=
  ∀ i : Fin n, ∑ j : Fin n, c.coeff i j = 0

/-- ⟨σ, c⟩ = (1/2) ∑ᵢⱼ σ(i,j) · c(i,j) -/
noncomputable def eval {n : ℕ} [Fintype (Fin n)] (σ : C1 n) (c : Chain1 n) : ℝ :=
  (1/2) * ∑ i : Fin n, ∑ j : Fin n, σ.val i j * (c.coeff i j : ℝ)

/-- Holonomy: evaluation of a 1-cochain on a 1-chain -/
noncomputable def holonomy {n : ℕ} [Fintype (Fin n)]
    (σ : C1 n) (c : Chain1 n) : ℝ :=
  eval σ c

/-! ## Quantum Cochains -/

/-- A quantum 0-cochain: complex-valued wavefunction on vertices -/
def QC0 (n : ℕ) := Fin n → ℂ

/-- A quantum 1-cochain: complex-valued skew-symmetric function on edges -/
structure QC1 (n : ℕ) where
  val : Fin n → Fin n → ℂ
  skew : ∀ i j, val i j = -val j i

/-- The quantum coboundary operator (gradient on ℂ) -/
def qd0 {n : ℕ} (ψ : QC0 n) : QC1 n := {
  val := fun i j => ψ j - ψ i
  skew := by intro i j; ring
}

/-- Hermitian inner product on quantum 0-cochains -/
noncomputable def inner_QC0 {n : ℕ} [Fintype (Fin n)] (ψ φ : QC0 n) : ℂ :=
  ∑ i : Fin n, star (ψ i) * φ i

/-- Hermitian inner product on quantum 1-cochains -/
noncomputable def inner_QC1 {n : ℕ} [Fintype (Fin n)] (σ τ : QC1 n) : ℂ :=
  (1/2) * ∑ i : Fin n, ∑ j : Fin n, star (σ.val i j) * τ.val i j

/-- Norm squared on QC0 (always real and non-negative) -/
noncomputable def norm_sq_QC0 {n : ℕ} [Fintype (Fin n)] (ψ : QC0 n) : ℝ :=
  (inner_QC0 ψ ψ).re

/-- Norm squared on QC1 -/
noncomputable def norm_sq_QC1 {n : ℕ} [Fintype (Fin n)] (σ : QC1 n) : ℝ :=
  (inner_QC1 σ σ).re

/-- The quantum divergence operator (adjoint of qd0) -/
noncomputable def qdivergence {n : ℕ} [Fintype (Fin n)] (σ : QC1 n) : QC0 n :=
  fun i => -∑ j : Fin n, σ.val i j

/-- The quantum graph Laplacian Δ = d* ∘ d -/
noncomputable def quantum_laplacian {n : ℕ} [Fintype (Fin n)] (ψ : QC0 n) : QC0 n :=
  qdivergence (qd0 ψ)

end DiscreteHodge
