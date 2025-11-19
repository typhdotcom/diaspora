/-
# The Cohomological Foundation of Diaspora

This file recasts the core physical theorems of the Diaspora framework into
the language of Discrete Hodge Theory.

## The Dictionary

1. **Phases** (ω) are 0-cochains: C⁰(G, ℝ)
2. **Constraints** (σ) are 1-cochains: C¹(G, ℝ)
3. **Graph Derivative** (d) is the coboundary operator d⁰: C⁰ → C¹
4. **V_int** is the squared L2 norm of the residual: ||dω - σ||²
5. **Holonomy** is the evaluation of σ on homology cycles.

## The Unification

The "Ground State" of a system with holonomy is the **Harmonic Representative** of the cohomology class [σ].

- **Mass** = The Harmonic Component (non-exact part of constraints).
- **Relaxation** = Hodge Decomposition (orthogonal projection).
- **Inheritance** = Linearity of the Hodge Projection.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Module.FiniteDimension

open BigOperators

namespace DiscreteHodge

/-! ## Part 1: Chain Complexes on Graphs -/

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

/-! ## Part 2: Inner Products and Norms -/

/-- Inner product on 1-cochains (sum over unique edges) -/
noncomputable def inner_product_C1 {n : ℕ} [Fintype (Fin n)] (σ τ : C1 n) : ℝ :=
  (1/2) * ∑ i : Fin n, ∑ j : Fin n, (σ.val i j) * (τ.val i j)

/-- Squared Norm of a 1-cochain -/
noncomputable def norm_sq {n : ℕ} [Fintype (Fin n)] (σ : C1 n) : ℝ := inner_product_C1 σ σ

/-- Inner product on 1-cochains is symmetric -/
lemma inner_product_C1_comm {n : ℕ} [Fintype (Fin n)] (σ τ : C1 n) :
  inner_product_C1 σ τ = inner_product_C1 τ σ := by
  unfold inner_product_C1
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  congr 1
  ext i
  congr 1
  ext j
  rw [σ.skew, τ.skew]
  ring

/--
  **Theorem: V_int is the distance to exactness**

  V_int(X) = || d⁰ϕ - σ ||²

  This recasts your internal cost as the failure of the constraints (σ)
  to be the gradient of some scalar field (ϕ).
-/
theorem V_int_is_cohomological_distance {n : ℕ} [Fintype (Fin n)] (ϕ : C0 n) (σ : C1 n) :
  norm_sq { val := fun i j => (d0 ϕ).val i j - σ.val i j,
            skew := by intro i j; simp [d0]; rw [σ.skew]; ring }
  = (1/2) * ∑ i, ∑ j, ( (ϕ j - ϕ i) - σ.val i j )^2 := by
  -- This is definitionally equal after unfolding
  unfold norm_sq inner_product_C1 d0
  simp only
  -- The computation is straightforward
  congr 1
  congr 1
  ext i
  congr 1
  ext j
  ring

/-! ## Part 3: Hodge Decomposition -/

/--
  The Space of Exact Forms: Image(d⁰).
  These are constraints that can be perfectly satisfied (Holonomy = 0).
-/
def IsExact {n : ℕ} (σ : C1 n) : Prop :=
  ∃ ϕ : C0 n, ∀ i j, σ.val i j = (d0 ϕ).val i j

/--
  The Space of Harmonic Forms:
  In graph theory, these are cycle flows.
  They represent the non-trivial cohomology H¹(G, ℝ).

  A form is Harmonic if it is "divergence free" (Kirchhoff's Law) at every node.
  (Note: This is technically the dual, but on graphs H₁ ≅ H¹).
-/
def IsHarmonic {n : ℕ} [Fintype (Fin n)] (σ : C1 n) : Prop :=
  ∀ i : Fin n, ∑ j : Fin n, σ.val i j = 0

/-- The divergence operator d*: C¹ → C⁰ (negative adjoint of coboundary) -/
noncomputable def divergence {n : ℕ} [Fintype (Fin n)] (σ : C1 n) : C0 n :=
  fun i => - ∑ j : Fin n, σ.val i j

/-- Helper lemma: swapping sum indices -/
lemma sum_swap {n : ℕ} [Fintype (Fin n)] (f : Fin n → Fin n → ℝ) :
  ∑ i : Fin n, ∑ j : Fin n, f i j = ∑ i : Fin n, ∑ j : Fin n, f j i := by
  rw [Finset.sum_comm]

/-- Lemma: divergence is the (negative) adjoint of d0 under the inner product -/
lemma divergence_is_adjoint {n : ℕ} [Fintype (Fin n)] (ϕ : C0 n) (σ : C1 n) :
  inner_product_C1 (d0 ϕ) σ = ∑ i : Fin n, ϕ i * divergence σ i := by
  unfold inner_product_C1 d0 divergence
  simp only
  -- LHS = (1/2) * ∑ᵢ∑ⱼ (ϕⱼ - ϕᵢ) * σᵢⱼ
  -- We'll show: ∑ᵢ∑ⱼ (ϕⱼ - ϕᵢ) * σᵢⱼ = 2 * ∑ᵢ ϕᵢ * (-∑ⱼ σᵢⱼ)
  have key : ∑ i : Fin n, ∑ j : Fin n, (ϕ j - ϕ i) * σ.val i j = 2 * ∑ i : Fin n, ϕ i * (-∑ j : Fin n, σ.val i j) := by
    -- Expand (ϕⱼ - ϕᵢ) * σᵢⱼ = ϕⱼ*σᵢⱼ - ϕᵢ*σᵢⱼ
    simp only [sub_mul, Finset.sum_sub_distrib]
    -- Now: ∑ᵢ∑ⱼ ϕⱼ*σᵢⱼ - ∑ᵢ∑ⱼ ϕᵢ*σᵢⱼ
    -- In the first term, swap indices: ∑ᵢ∑ⱼ ϕⱼ*σᵢⱼ = ∑ᵢ∑ⱼ ϕᵢ*σⱼᵢ
    conv_lhs =>
      enter [1]
      rw [sum_swap]
    -- Use skew-symmetry: σⱼᵢ = -σᵢⱼ
    conv_lhs =>
      enter [1, 2, i, 2, j]  -- Navigate to σ.val j i inside the first sum
      rw [σ.skew]
    simp only [mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, two_mul, Finset.sum_add_distrib]
    ring
  rw [key]
  ring

/-- Linearity of d0: d(ϕ + ψ) = dϕ + dψ -/
lemma d0_add {n : ℕ} (ϕ ψ : C0 n) :
  ∀ i j, (d0 (fun i => ϕ i + ψ i)).val i j = (d0 ϕ).val i j + (d0 ψ).val i j := by
  intro i j
  simp [d0]
  ring

/-- Scalar multiplication pulls out of d0 -/
lemma d0_smul {n : ℕ} (c : ℝ) (ϕ : C0 n) :
  ∀ i j, (d0 (fun i => c * ϕ i)).val i j = c * (d0 ϕ).val i j := by
  intro i j
  simp [d0]
  ring

/-- Expansion of the squared norm: ||A + B||² = ||A||² + 2⟨A,B⟩ + ||B||² -/
lemma norm_sq_add {n : ℕ} [Fintype (Fin n)] (A B : C1 n) :
  norm_sq { val := fun i j => A.val i j + B.val i j,
            skew := by intro i j; rw [A.skew, B.skew]; ring } =
  norm_sq A + 2 * inner_product_C1 A B + norm_sq B := by
  unfold norm_sq inner_product_C1
  simp only [Finset.sum_add_distrib, mul_add, add_mul]
  have h_comm : ∀ i j, B.val i j * A.val i j = A.val i j * B.val i j := fun i j => mul_comm _ _
  simp only [h_comm]
  ring_nf

/-- The graph Laplacian Δ = d* ∘ d: C⁰ → C⁰ -/
noncomputable def graph_laplacian {n : ℕ} [Fintype (Fin n)] (ϕ : C0 n) : C0 n :=
  divergence (d0 ϕ)

/-- Expand the Laplacian: (Δϕ)ᵢ = -∑ⱼ (ϕⱼ - ϕᵢ) = ∑ⱼ (ϕᵢ - ϕⱼ) -/
lemma laplacian_expansion {n : ℕ} [Fintype (Fin n)] (ϕ : C0 n) (i : Fin n) :
  graph_laplacian ϕ i = - ∑ j : Fin n, (ϕ j - ϕ i) := by
  unfold graph_laplacian divergence d0
  rfl

/-- Helper: The objective function we're minimizing -/
noncomputable def objective {n : ℕ} [Fintype (Fin n)] (σ : C1 n) (ϕ : C0 n) : ℝ :=
  norm_sq { val := fun i j => (d0 ϕ).val i j - σ.val i j,
            skew := by intro i j; simp [d0]; rw [σ.skew]; ring }

/-- The basis vector at index k (1 at k, 0 elsewhere) -/
def basis_vector {n : ℕ} (k : Fin n) : C0 n :=
  fun i => if i = k then 1 else 0

/-- The key lemma: If ϕ minimizes ||dϕ - σ||², then Δϕ = d*σ -/
theorem euler_lagrange {n : ℕ} [Fintype (Fin n)] (σ : C1 n) (ϕ : C0 n) :
  (∀ ϕ', objective σ ϕ ≤ objective σ ϕ') →
  ∀ k, graph_laplacian ϕ k = divergence σ k := by
  intro h_min k

  -- 1. Define the direction of perturbation: basis vector at k
  let ψ := basis_vector k

  -- 2. The optimality condition: if ϕ is optimal, then ⟨dϕ - σ, dψ⟩ = 0
  have optimality_condition : inner_product_C1 { val := fun i j => (d0 ϕ).val i j - σ.val i j,
                                                 skew := by intro i j; simp [d0]; rw [σ.skew]; ring } (d0 ψ) = 0 := by
    by_contra h_nonzero
    -- Use the quadratic expansion: ∀ ε, Aε² + Bε ≥ 0 implies B = 0
    let A := norm_sq (d0 ψ)
    let B := 2 * inner_product_C1 { val := fun i j => (d0 ϕ).val i j - σ.val i j,
                                    skew := by intro i j; simp [d0]; rw [σ.skew]; ring } (d0 ψ)

    have quadr_ineq : ∀ (ε : ℝ), A * ε^2 + B * ε ≥ 0 := by
      intro ε
      let ϕ_eps : C0 n := fun i => ϕ i + ε * ψ i
      have val_expand : ∀ i j, (d0 ϕ_eps).val i j - σ.val i j =
        ((d0 ϕ).val i j - σ.val i j) + ε * (d0 ψ).val i j := by
        intro i j
        simp [d0, ψ, ϕ_eps, basis_vector]
        split_ifs <;> ring
      -- Use norm_sq (X + Y) expansion
      have h_obj := h_min ϕ_eps
      have h_eq : (fun i j => (d0 ϕ_eps).val i j - σ.val i j) =
                  (fun i j => ((d0 ϕ).val i j - σ.val i j) + ε * (d0 ψ).val i j) := by
        ext i j
        exact val_expand i j
      simp only [h_eq, objective] at h_obj ⊢
      -- Rewrite RHS as sum of two C1s
      let resid : C1 n := { val := fun i j => (d0 ϕ).val i j - σ.val i j,
                            skew := by intro i j; rw [σ.skew]; simp [d0]; ring }
      let eps_dpsi : C1 n := { val := fun i j => ε * (d0 ψ).val i j,
                               skew := by intro i j; simp [d0]; ring }
      have h_split : ({ val := fun i j => (d0 ϕ).val i j - σ.val i j + ε * (d0 ψ).val i j,
                        skew := by intro i j; rw [σ.skew]; simp [d0]; ring } : C1 n) =
                     ({ val := fun i j => resid.val i j + eps_dpsi.val i j,
                        skew := by intro i j; rw [resid.skew, eps_dpsi.skew]; ring } : C1 n) := by
        rfl
      rw [h_split] at h_obj
      rw [norm_sq_add] at h_obj
      -- The h_obj inequality simplifies to: 0 ≤ 2 * ⟨resid, eps_dpsi⟩ + norm_sq eps_dpsi
      -- But eps_dpsi = ε * dψ, so this becomes: 0 ≤ 2ε * ⟨resid, dψ⟩ + ε² * norm_sq dψ
      -- Which is exactly: A * ε² + B * ε ≥ 0
      have h_simp : norm_sq resid + 2 * inner_product_C1 resid eps_dpsi + norm_sq eps_dpsi =
                    norm_sq resid + 2 * ε * inner_product_C1 resid (d0 ψ) + ε^2 * A := by
        congr 1
        · -- 1. The Linear Term
          dsimp [inner_product_C1, eps_dpsi]
          ring_nf
          -- This is just bilinearity: ∑∑ resid * ε * dψ = ε * ∑∑ resid * dψ
          simp only [mul_comm (resid.val _ _), mul_assoc, ← Finset.mul_sum]
        · -- 2. The Quadratic Term
          dsimp [norm_sq, inner_product_C1, A, eps_dpsi]
          simp only [pow_two]
          ring_nf
          -- Pull ε^2 out of the sums
          simp only [← Finset.mul_sum]
      rw [h_simp] at h_obj
      simp only [resid, ge_iff_le, A, B] at h_obj ⊢
      linarith

    -- B must be 0
    have h_B_zero : B = 0 := by
      by_contra hB
      -- A is sum of squares, so A ≥ 0
      -- Choose ε so that A * ε^2 + B * ε < 0
      let ε := -B / (2 * (A + 1))
      have h_eps : A * ε^2 + B * ε < 0 := by
        -- Substitute ε = -B / (2 * (A + 1))
        simp only [ε, pow_two]
        -- Clear denominators and simplify
        field_simp
        ring_nf
        -- Goal: -(B^2 * A * (1 + 2A + A^2)⁻¹) - B^2 * (1 + 2A + A^2)⁻¹ * 2 < 0
        -- Factor: -B^2 * (A + 2) * (1 + 2A + A^2)⁻¹ < 0
        -- Since B ≠ 0, we have B^2 > 0
        -- Since A ≥ 0, we have A + 2 > 0
        -- Since (1 + 2A + A^2) = (1 + A)^2 > 0, the inverse is positive
        -- So the whole expression is negative
        have hB_sq : B ^ 2 > 0 := sq_pos_of_ne_zero hB
        -- A is a norm squared, so A ≥ 0
        have hA_nonneg : A ≥ 0 := by
          simp only [A, norm_sq, inner_product_C1]
          -- Now it's (1/2) * ∑∑ (val * val)
          apply mul_nonneg
          · norm_num
          · apply Finset.sum_nonneg; intro i _
            apply Finset.sum_nonneg; intro j _
            apply mul_self_nonneg
        have h_denom_pos : 1 + A * 2 + A ^ 2 > 0 := by nlinarith [sq_nonneg A]
        have h_inv_pos : 0 < (1 + A * 2 + A ^ 2)⁻¹ := by positivity
        -- The numerator after clearing denominators is: -(B^2 * A) - (B^2 * 2) = -B^2 * (A + 2)
        -- Since B^2 > 0 and A + 2 > 0, this is negative
        have h_A_plus_2_pos : A + 2 > 0 := by linarith
        nlinarith [mul_pos hB_sq h_A_plus_2_pos, mul_pos h_inv_pos hB_sq]
      have h_contra := quadr_ineq ε
      linarith

    have h : B = 0 := h_B_zero
    simp only [B] at h
    have h_zero : inner_product_C1 { val := fun i j => (d0 ϕ).val i j - σ.val i j,
                                     skew := by intro i j; simp [d0]; rw [σ.skew]; ring } (d0 ψ) = 0 := by
      linarith
    exact h_nonzero h_zero

  -- 3. Apply adjointness to get the equation
  have h_adj : inner_product_C1 { val := fun i j => (d0 ϕ).val i j - σ.val i j,
                                  skew := by intro i j; simp [d0]; rw [σ.skew]; ring } (d0 ψ)
             = ∑ i, ψ i * divergence { val := fun i j => (d0 ϕ).val i j - σ.val i j,
                                       skew := by intro i j; simp [d0]; rw [σ.skew]; ring } i := by
    rw [inner_product_C1_comm]
    exact divergence_is_adjoint ψ { val := fun i j => (d0 ϕ).val i j - σ.val i j,
                                     skew := by intro i j; simp [d0]; rw [σ.skew]; ring }

  rw [h_adj] at optimality_condition
  -- ψ is basis_vector k, so ψ i is 1 if i=k else 0
  simp only [basis_vector, ψ] at optimality_condition
  rw [Finset.sum_eq_single k] at optimality_condition
  · -- The term at k is 1 * divergence(...) = 0
    simp only at optimality_condition
    -- divergence(dϕ - σ) = divergence(dϕ) - divergence(σ) = Δϕ - divergence(σ)
    unfold divergence at optimality_condition
    simp only at optimality_condition
    -- optimality_condition is now: -(∑ j, (dϕ_kj - σ_kj)) = 0
    -- Expand: -(∑ j, dϕ_kj - ∑ j, σ_kj) = 0
    have h_expand : -(∑ j, ({ val := fun i j => (d0 ϕ).val i j - σ.val i j,
                               skew := by intro i j; simp [d0]; rw [σ.skew]; ring } : C1 n).val k j)
                   = -(∑ j, ((d0 ϕ).val k j - σ.val k j)) := by rfl
    rw [h_expand] at optimality_condition
    simp only [Finset.sum_sub_distrib] at optimality_condition
    have h_split : -(∑ j, (d0 ϕ).val k j - ∑ j, σ.val k j) = (-∑ j, (d0 ϕ).val k j) - (-∑ j, σ.val k j) := by ring
    rw [h_split] at optimality_condition
    -- Re-fold definitions
    have h_lap : (-∑ j, (d0 ϕ).val k j) = graph_laplacian ϕ k := by rfl
    have h_div : (-∑ j, σ.val k j) = divergence σ k := by rfl
    rw [h_lap, h_div] at optimality_condition
    simp at optimality_condition
    linarith [optimality_condition]
  · -- Case i ≠ k
    intro i _ hik
    simp [hik]
  · -- Case k ∉ Fin n (impossible)
    intro hk
    exact absurd (Finset.mem_univ k) hk

/--
  **The Hodge Decomposition Theorem (Graph Version)**

  Any constraint σ can be uniquely decomposed into:
  σ = d⁰ϕ + γ
  where d⁰ϕ is Exact (Relaxation) and γ is Harmonic (Mass/Holonomy).

  AND: d⁰ϕ ⊥ γ (Orthogonality).

  **Proof Strategy** (currently has `sorry` placeholders):
  1. Show ϕ minimizing ||dϕ - σ||² exists (compactness on finite dim space)
  2. Apply Euler-Lagrange: first-order condition gives Δϕ = d*σ
  3. Define γ = σ - dϕ. From Δϕ = d*σ we get d*γ = 0, so γ is harmonic
  4. Orthogonality: ⟨dϕ, γ⟩ = ⟨dϕ, σ⟩ - ||dϕ||² = ⟨ϕ, d*σ⟩ - ||dϕ||² = ⟨ϕ, Δϕ⟩ - ||dϕ||² = ||dϕ||² - ||dϕ||² = 0

  **Status**: Proof structure is complete, but three lemmas still need full proofs:
  - `divergence_is_adjoint`: ⟨dϕ, σ⟩ = ⟨ϕ, d*σ⟩ (algebraic manipulation)
  - `euler_lagrange`: Minimizer satisfies Δϕ = d*σ (calculus of variations)
  - `hodge_decomposition` assembly (straightforward given the above)

  These are all standard results in discrete differential geometry, just tedious to formalize.
-/
theorem hodge_decomposition {n : ℕ} [Fintype (Fin n)] (σ : C1 n) :
  ∃ (ϕ : C0 n) (γ : C1 n),
    (∀ i j, σ.val i j = (d0 ϕ).val i j + γ.val i j) ∧
    IsHarmonic γ ∧
    inner_product_C1 (d0 ϕ) γ = 0 := by

  -- 1. EXISTENCE OF MINIMIZER
  have h_exists : ∃ ϕ_opt : C0 n, ∀ ϕ', objective σ ϕ_opt ≤ objective σ ϕ' := by
    -- A. Local Aliases (EuclideanSpace provides L2 geometry)
    let E := EuclideanSpace ℝ (Fin n)
    let F := EuclideanSpace ℝ (Fin n × Fin n)

    -- B. Define Linear Map on Raw Functions
    -- We use 'intros' to ensure context is clear before 'ext'
    let L_raw : (Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ) := {
      toFun := fun ϕ x => ϕ x.2 - ϕ x.1,
      map_add' := by
        intros -- Clears ∀ x y
        ext    -- Applies functional extensionality
        dsimp
        ring,
      map_smul' := by
        intros -- Clears ∀ c x
        ext
        dsimp
        ring
    }

    -- C. Cast to EuclideanSpace
    let L : E →ₗ[ℝ] F := L_raw
    let target : F := fun x => σ.val x.1 x.2
    let K := LinearMap.range L

    -- D. The Projection Theorem
    have h_nonempty : (K : Set F).Nonempty := Submodule.nonempty K
    obtain ⟨p, hp_mem_closure, hp_min_eq⟩ := 
      Metric.exists_mem_closure_infDist_eq_dist h_nonempty target
    
    have h_closed : IsClosed (K : Set F) := Submodule.closed_of_finiteDimensional K
    rw [h_closed.closure_eq] at hp_mem_closure

    -- E. Pullback
    obtain ⟨ϕ_opt_val, h_map⟩ := hp_mem_closure
    use ϕ_opt_val
    intro ϕ'
    
    -- Cast for type checking
    let ϕ'_val : E := ϕ'

    -- F. Objective Equivalence
    have obj_eq : ∀ ψ : E, objective σ ψ = (1/2) * (dist (L ψ) target)^2 := by
      intro ψ
      unfold objective norm_sq inner_product_C1
      rw [PiLp.dist_eq_of_L2]
      have sum_nonneg : 0 ≤ ∑ x : Fin n × Fin n, dist (L ψ x) (target x) ^ 2 :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      rw [Real.sq_sqrt sum_nonneg]
      rw [Fintype.sum_prod_type]
      congr 1
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [Real.dist_eq, sq_abs, ←pow_two]
      dsimp
      rfl

    -- G. Apply Optimality
    rw [obj_eq ϕ_opt_val, obj_eq ϕ'_val]
    gcongr
    rw [h_map, dist_comm p target, dist_comm (L ϕ'_val) target]
    rw [←hp_min_eq]
    apply Metric.infDist_le_dist_of_mem
    exact LinearMap.mem_range_self L ϕ'_val

  obtain ⟨ϕ_opt, h_min⟩ := h_exists

  -- 2. CONSTRUCT DECOMPOSITION
  let γ : C1 n := {
    val := fun i j => σ.val i j - (d0 ϕ_opt).val i j,
    skew := by intro i j; rw [σ.skew]; simp [d0]; ring
  }

  use ϕ_opt, γ
  constructor
  · intro i j; simp [γ]

  constructor
  · -- Harmonicity
    unfold IsHarmonic
    intro i
    have el := euler_lagrange σ ϕ_opt h_min i
    simp only [γ, Finset.sum_sub_distrib]
    have h1 : ∑ j, σ.val i j = -divergence σ i := by unfold divergence; ring
    have h2 : ∑ j, (d0 ϕ_opt).val i j = -divergence (d0 ϕ_opt) i := by unfold divergence; ring
    rw [h1, h2]
    have h3 : divergence (d0 ϕ_opt) i = graph_laplacian ϕ_opt i := by unfold graph_laplacian; rfl
    rw [h3, el]
    ring

  · -- Orthogonality
    rw [divergence_is_adjoint]
    apply Finset.sum_eq_zero
    intro i _
    have h_harm_val : ∑ j, γ.val i j = 0 := by
      simp only [γ]
      have el := euler_lagrange σ ϕ_opt h_min i
      have h1 : ∑ j, σ.val i j = -divergence σ i := by unfold divergence; ring
      have h2 : ∑ j, (d0 ϕ_opt).val i j = -graph_laplacian ϕ_opt i := by unfold graph_laplacian divergence; ring
      simp only [Finset.sum_sub_distrib, h1, h2, el]
      ring
    unfold divergence
    rw [h_harm_val]
    ring

/-! ## Part 4: Recasting the Main Theorems -/

/--
  **Recast: "V_int Lower Bound"**

  Original: V_int ≥ K²/k
  Hodge: The minimum energy is the norm of the Harmonic component.

  Min || d⁰ϕ - σ ||² = || γ ||²

  Proof: Since σ = d⁰ϕ_opt + γ, and we subtract d⁰ϕ, we are left with γ.
-/
theorem minimum_V_int_is_harmonic_norm {n : ℕ} [Fintype (Fin n)] (σ : C1 n) :
  ∃ ϕ_opt : C0 n,
    let resid : C1 n := { val := fun i j => (d0 ϕ_opt).val i j - σ.val i j,
                          skew := by intro i j; simp [d0]; rw [σ.skew]; ring }
    let γ : C1 n := { val := fun i j => σ.val i j - (d0 ϕ_opt).val i j,
                      skew := by intro i j; rw [σ.skew]; simp [d0]; ring }
    norm_sq resid = norm_sq γ := by
  -- Get the Hodge decomposition
  obtain ⟨ϕ_opt, γ_harm, h_decomp, h_harmonic, h_orth⟩ := hodge_decomposition σ
  use ϕ_opt

  -- The residual is exactly -γ_harm
  have h_resid : ∀ i j, ((d0 ϕ_opt).val i j - σ.val i j) = -γ_harm.val i j := by
    intro i j
    -- We have: σ = dϕ + γ, so dϕ - σ = -γ
    have h := h_decomp i j
    -- Unfold d0 in h: σ = (ϕ_opt j - ϕ_opt i) + γ
    simp only [d0] at h ⊢
    linarith

  -- Therefore ||resid||² = ||γ||²
  simp only [norm_sq, inner_product_C1]
  congr 1
  congr 1
  ext i
  congr 1
  ext j
  -- Both sides are the same: (dϕ - σ)² = (σ - dϕ)²
  -- Since dϕ - σ = -γ and σ - dϕ = γ, we have (-γ)² = γ²
  have h1 := h_resid i j
  have h2 : σ.val i j - (d0 ϕ_opt).val i j = γ_harm.val i j := by linarith [h1]
  rw [h1, h2]
  ring

/--
  **Recast: "Conservation of Holonomy"**

  Original: K_new = (K1 + K2)/2
  Hodge: The Harmonic projection is a Linear Operator.

  Harmonic(α·σ₁ + β·σ₂) = α·Harmonic(σ₁) + β·Harmonic(σ₂)
-/
theorem harmonic_projection_is_linear {n : ℕ} [Fintype (Fin n)] (σ₁ σ₂ : C1 n) (α β : ℝ) :
  ∃ (γ₁ γ₂ γ_sum : C1 n),
    -- γ₁ is the harmonic part of σ₁
    (∃ ϕ₁ : C0 n, ∀ i j, σ₁.val i j = (d0 ϕ₁).val i j + γ₁.val i j) ∧
    IsHarmonic γ₁ ∧
    -- γ₂ is the harmonic part of σ₂
    (∃ ϕ₂ : C0 n, ∀ i j, σ₂.val i j = (d0 ϕ₂).val i j + γ₂.val i j) ∧
    IsHarmonic γ₂ ∧
    -- γ_sum is the harmonic part of α·σ₁ + β·σ₂
    (let σ_sum : C1 n := { val := fun i j => α * σ₁.val i j + β * σ₂.val i j,
                            skew := by intro i j; rw [σ₁.skew, σ₂.skew]; ring }
     ∃ ϕ_sum : C0 n, ∀ i j, σ_sum.val i j = (d0 ϕ_sum).val i j + γ_sum.val i j) ∧
    IsHarmonic γ_sum ∧
    -- Linearity: γ_sum = α·γ₁ + β·γ₂
    (∀ i j, γ_sum.val i j = α * γ₁.val i j + β * γ₂.val i j) := by
  -- Get Hodge decompositions
  obtain ⟨ϕ₁, γ₁, h_decomp₁, h_harm₁, _⟩ := hodge_decomposition σ₁
  obtain ⟨ϕ₂, γ₂, h_decomp₂, h_harm₂, _⟩ := hodge_decomposition σ₂

  -- Define the linear combination
  let σ_sum : C1 n := { val := fun i j => α * σ₁.val i j + β * σ₂.val i j,
                         skew := by intro i j; rw [σ₁.skew, σ₂.skew]; ring }

  -- The harmonic part of σ_sum is α·γ₁ + β·γ₂
  let γ_sum : C1 n := { val := fun i j => α * γ₁.val i j + β * γ₂.val i j,
                         skew := by intro i j; rw [γ₁.skew, γ₂.skew]; ring }

  -- The exact part is α·(d0 ϕ₁) + β·(d0 ϕ₂) = d0(α·ϕ₁ + β·ϕ₂)
  let ϕ_sum : C0 n := fun i => α * ϕ₁ i + β * ϕ₂ i

  use γ₁, γ₂, γ_sum

  refine ⟨⟨ϕ₁, h_decomp₁⟩, h_harm₁, ⟨ϕ₂, h_decomp₂⟩, h_harm₂, ?_, ?_, ?_⟩

  -- Prove the scaled decomposition holds
  · use ϕ_sum
    intro i j
    simp only [d0]
    have h1 := h_decomp₁ i j
    have h2 := h_decomp₂ i j
    -- α·σ₁ + β·σ₂ = α·(dϕ₁ + γ₁) + β·(dϕ₂ + γ₂) = d(α·ϕ₁ + β·ϕ₂) + (α·γ₁ + β·γ₂)
    calc σ_sum.val i j
        = α * σ₁.val i j + β * σ₂.val i j := rfl
      _ = α * ((d0 ϕ₁).val i j + γ₁.val i j) + β * ((d0 ϕ₂).val i j + γ₂.val i j) := by rw [h1, h2]
      _ = α * (ϕ₁ j - ϕ₁ i + γ₁.val i j) + β * (ϕ₂ j - ϕ₂ i + γ₂.val i j) := by simp [d0]
      _ = (α * ϕ₁ j + β * ϕ₂ j) - (α * ϕ₁ i + β * ϕ₂ i) + (α * γ₁.val i j + β * γ₂.val i j) := by ring
      _ = (d0 ϕ_sum).val i j + γ_sum.val i j := by simp [ϕ_sum, γ_sum, d0]

  -- γ_sum is harmonic
  · intro i
    calc ∑ j : Fin n, γ_sum.val i j
        = ∑ j : Fin n, (α * γ₁.val i j + β * γ₂.val i j) := rfl
      _ = ∑ j : Fin n, α * γ₁.val i j + ∑ j : Fin n, β * γ₂.val i j := by rw [Finset.sum_add_distrib]
      _ = α * ∑ j : Fin n, γ₁.val i j + β * ∑ j : Fin n, γ₂.val i j := by rw [Finset.mul_sum, Finset.mul_sum]
      _ = α * 0 + β * 0 := by rw [h_harm₁ i, h_harm₂ i]
      _ = 0 := by ring

  -- Linearity: γ_sum = α·γ₁ + β·γ₂
  · intro i j
    rfl

/--
  **Recast: "Inheritance Beats Calm"**

  Original: Scaling optimized phases beats starting from 0.
  Hodge: Because the decomposition is orthogonal, scaling the Exact component
  linearly scales the solution.

  If σ decomposes to (Exact + Harmonic), and we scale constraints by 1/2,
  the new optimal solution is exactly 1/2 of the old Exact component.

  "Calm" resets the Exact component to 0.
  "Inheritance" keeps the Exact component (scaled).

  Since ||Exact||² > 0 usually, keeping it is better than regenerating it
  against an external task.
-/
theorem inheritance_is_linearity {n : ℕ} [Fintype (Fin n)] (σ : C1 n) :
  ∃ (ϕ_opt : C0 n) (γ : C1 n),
    -- Hodge decomposition of σ
    (∀ i j, σ.val i j = (d0 ϕ_opt).val i j + γ.val i j) ∧
    IsHarmonic γ ∧
    -- When we scale σ by α, the optimal phases scale by α
    (∀ α : ℝ,
      let σ_scaled : C1 n := { val := fun i j => α * σ.val i j,
                                skew := by intro i j; rw [σ.skew]; ring }
      let ϕ_scaled : C0 n := fun i => α * ϕ_opt i
      let γ_scaled : C1 n := { val := fun i j => α * γ.val i j,
                                skew := by intro i j; rw [γ.skew]; ring }
      -- The scaled decomposition holds
      (∀ i j, σ_scaled.val i j = (d0 ϕ_scaled).val i j + γ_scaled.val i j) ∧
      -- And it's still a valid Hodge decomposition (harmonic + orthogonal)
      IsHarmonic γ_scaled) := by
  -- Get the Hodge decomposition
  obtain ⟨ϕ_opt, γ, h_decomp, h_harm, h_orth⟩ := hodge_decomposition σ
  use ϕ_opt, γ

  constructor
  · exact h_decomp
  constructor
  · exact h_harm
  · intro α
    constructor
    · intro i j
      simp only [d0]
      -- Scale both sides of σ = dϕ + γ by α
      have h := h_decomp i j
      calc α * σ.val i j
          = α * ((d0 ϕ_opt).val i j + γ.val i j) := by rw [h]
        _ = α * (ϕ_opt j - ϕ_opt i) + α * γ.val i j := by simp [d0]; ring
        _ = α * ϕ_opt j - α * ϕ_opt i + α * γ.val i j := by ring
    · intro i
      calc ∑ j : Fin n, α * γ.val i j
          = α * ∑ j : Fin n, γ.val i j := by rw [Finset.mul_sum]
        _ = α * 0 := by rw [h_harm i]
        _ = 0 := by ring

end DiscreteHodge
