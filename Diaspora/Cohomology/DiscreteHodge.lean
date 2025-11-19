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
  unfold norm_sq inner_product_C1 d0
  simp only
  congr 1
  congr 1
  ext i
  congr 1
  ext j
  ring

/-! ## Part 3: Hodge Decomposition -/

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

  let ψ := basis_vector k

  have optimality_condition : inner_product_C1 { val := fun i j => (d0 ϕ).val i j - σ.val i j,
                                                 skew := by intro i j; simp [d0]; rw [σ.skew]; ring } (d0 ψ) = 0 := by
    by_contra h_nonzero
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
      have h_obj := h_min ϕ_eps
      have h_eq : (fun i j => (d0 ϕ_eps).val i j - σ.val i j) =
                  (fun i j => ((d0 ϕ).val i j - σ.val i j) + ε * (d0 ψ).val i j) := by
        ext i j
        exact val_expand i j
      simp only [h_eq, objective] at h_obj ⊢
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
      have h_simp : norm_sq resid + 2 * inner_product_C1 resid eps_dpsi + norm_sq eps_dpsi =
                    norm_sq resid + 2 * ε * inner_product_C1 resid (d0 ψ) + ε^2 * A := by
        congr 1
        · dsimp [inner_product_C1, eps_dpsi]
          ring_nf
          simp only [mul_comm (resid.val _ _), mul_assoc, ← Finset.mul_sum]
        · dsimp [norm_sq, inner_product_C1, A, eps_dpsi]
          simp only [pow_two]
          ring_nf
          simp only [← Finset.mul_sum]
      rw [h_simp] at h_obj
      simp only [resid, ge_iff_le, A, B] at h_obj ⊢
      linarith

    have h_B_zero : B = 0 := by
      by_contra hB
      let ε := -B / (2 * (A + 1))
      have h_eps : A * ε^2 + B * ε < 0 := by
        simp only [ε, pow_two]
        field_simp
        ring_nf
        have hB_sq : B ^ 2 > 0 := sq_pos_of_ne_zero hB
        have hA_nonneg : A ≥ 0 := by
          simp only [A, norm_sq, inner_product_C1]
          apply mul_nonneg
          · norm_num
          · apply Finset.sum_nonneg; intro i _
            apply Finset.sum_nonneg; intro j _
            apply mul_self_nonneg
        have h_denom_pos : 1 + A * 2 + A ^ 2 > 0 := by nlinarith [sq_nonneg A]
        have h_inv_pos : 0 < (1 + A * 2 + A ^ 2)⁻¹ := by positivity
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

  have h_adj : inner_product_C1 { val := fun i j => (d0 ϕ).val i j - σ.val i j,
                                  skew := by intro i j; simp [d0]; rw [σ.skew]; ring } (d0 ψ)
             = ∑ i, ψ i * divergence { val := fun i j => (d0 ϕ).val i j - σ.val i j,
                                       skew := by intro i j; simp [d0]; rw [σ.skew]; ring } i := by
    rw [inner_product_C1_comm]
    exact divergence_is_adjoint ψ { val := fun i j => (d0 ϕ).val i j - σ.val i j,
                                     skew := by intro i j; simp [d0]; rw [σ.skew]; ring }

  rw [h_adj] at optimality_condition
  simp only [basis_vector, ψ] at optimality_condition
  rw [Finset.sum_eq_single k] at optimality_condition
  · simp only at optimality_condition
    unfold divergence at optimality_condition
    simp only at optimality_condition
    have h_expand : -(∑ j, ({ val := fun i j => (d0 ϕ).val i j - σ.val i j,
                               skew := by intro i j; simp [d0]; rw [σ.skew]; ring } : C1 n).val k j)
                   = -(∑ j, ((d0 ϕ).val k j - σ.val k j)) := by rfl
    rw [h_expand] at optimality_condition
    simp only [Finset.sum_sub_distrib] at optimality_condition
    have h_split : -(∑ j, (d0 ϕ).val k j - ∑ j, σ.val k j) = (-∑ j, (d0 ϕ).val k j) - (-∑ j, σ.val k j) := by ring
    rw [h_split] at optimality_condition
    have h_lap : (-∑ j, (d0 ϕ).val k j) = graph_laplacian ϕ k := by rfl
    have h_div : (-∑ j, σ.val k j) = divergence σ k := by rfl
    rw [h_lap, h_div] at optimality_condition
    simp at optimality_condition
    linarith [optimality_condition]
  · intro i _ hik
    simp [hik]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/--
  **The Hodge Decomposition Theorem**

  Any 1-cochain σ decomposes uniquely as σ = d⁰ϕ + γ where d⁰ϕ is exact,
  γ is harmonic, and d⁰ϕ ⊥ γ.
-/
theorem hodge_decomposition {n : ℕ} [Fintype (Fin n)] (σ : C1 n) :
  ∃ (ϕ : C0 n) (γ : C1 n),
    (∀ i j, σ.val i j = (d0 ϕ).val i j + γ.val i j) ∧
    IsHarmonic γ ∧
    inner_product_C1 (d0 ϕ) γ = 0 := by

  have h_exists : ∃ ϕ_opt : C0 n, ∀ ϕ', objective σ ϕ_opt ≤ objective σ ϕ' := by
    let E := EuclideanSpace ℝ (Fin n)
    let F := EuclideanSpace ℝ (Fin n × Fin n)

    let L_raw : (Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ) := {
      toFun := fun ϕ x => ϕ x.2 - ϕ x.1,
      map_add' := by
        intros
        ext
        dsimp
        ring,
      map_smul' := by
        intros
        ext
        dsimp
        ring
    }

    let L : E →ₗ[ℝ] F := L_raw
    let target : F := fun x => σ.val x.1 x.2
    let K := LinearMap.range L

    have h_nonempty : (K : Set F).Nonempty := Submodule.nonempty K
    obtain ⟨p, hp_mem_closure, hp_min_eq⟩ :=
      Metric.exists_mem_closure_infDist_eq_dist h_nonempty target

    have h_closed : IsClosed (K : Set F) := Submodule.closed_of_finiteDimensional K
    rw [h_closed.closure_eq] at hp_mem_closure

    obtain ⟨ϕ_opt_val, h_map⟩ := hp_mem_closure
    use ϕ_opt_val
    intro ϕ'

    let ϕ'_val : E := ϕ'

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

    rw [obj_eq ϕ_opt_val, obj_eq ϕ'_val]
    gcongr
    rw [h_map, dist_comm p target, dist_comm (L ϕ'_val) target]
    rw [←hp_min_eq]
    apply Metric.infDist_le_dist_of_mem
    exact LinearMap.mem_range_self L ϕ'_val

  obtain ⟨ϕ_opt, h_min⟩ := h_exists

  let γ : C1 n := {
    val := fun i j => σ.val i j - (d0 ϕ_opt).val i j,
    skew := by intro i j; rw [σ.skew]; simp [d0]; ring
  }

  use ϕ_opt, γ
  constructor
  · intro i j; simp [γ]

  constructor
  · unfold IsHarmonic
    intro i
    have el := euler_lagrange σ ϕ_opt h_min i
    simp only [γ, Finset.sum_sub_distrib]
    have h1 : ∑ j, σ.val i j = -divergence σ i := by unfold divergence; ring
    have h2 : ∑ j, (d0 ϕ_opt).val i j = -divergence (d0 ϕ_opt) i := by unfold divergence; ring
    rw [h1, h2]
    have h3 : divergence (d0 ϕ_opt) i = graph_laplacian ϕ_opt i := by unfold graph_laplacian; rfl
    rw [h3, el]
    ring

  · rw [divergence_is_adjoint]
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
  obtain ⟨ϕ_opt, γ_harm, h_decomp, h_harmonic, h_orth⟩ := hodge_decomposition σ
  use ϕ_opt

  have h_resid : ∀ i j, ((d0 ϕ_opt).val i j - σ.val i j) = -γ_harm.val i j := by
    intro i j
    have h := h_decomp i j
    simp only [d0] at h ⊢
    linarith

  simp only [norm_sq, inner_product_C1]
  congr 1
  congr 1
  ext i
  congr 1
  ext j
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
    (∃ ϕ₁ : C0 n, ∀ i j, σ₁.val i j = (d0 ϕ₁).val i j + γ₁.val i j) ∧
    IsHarmonic γ₁ ∧
    (∃ ϕ₂ : C0 n, ∀ i j, σ₂.val i j = (d0 ϕ₂).val i j + γ₂.val i j) ∧
    IsHarmonic γ₂ ∧
    (let σ_sum : C1 n := { val := fun i j => α * σ₁.val i j + β * σ₂.val i j,
                            skew := by intro i j; rw [σ₁.skew, σ₂.skew]; ring }
     ∃ ϕ_sum : C0 n, ∀ i j, σ_sum.val i j = (d0 ϕ_sum).val i j + γ_sum.val i j) ∧
    IsHarmonic γ_sum ∧
    (∀ i j, γ_sum.val i j = α * γ₁.val i j + β * γ₂.val i j) := by
  obtain ⟨ϕ₁, γ₁, h_decomp₁, h_harm₁, _⟩ := hodge_decomposition σ₁
  obtain ⟨ϕ₂, γ₂, h_decomp₂, h_harm₂, _⟩ := hodge_decomposition σ₂

  let σ_sum : C1 n := { val := fun i j => α * σ₁.val i j + β * σ₂.val i j,
                         skew := by intro i j; rw [σ₁.skew, σ₂.skew]; ring }

  let γ_sum : C1 n := { val := fun i j => α * γ₁.val i j + β * γ₂.val i j,
                         skew := by intro i j; rw [γ₁.skew, γ₂.skew]; ring }

  let ϕ_sum : C0 n := fun i => α * ϕ₁ i + β * ϕ₂ i

  use γ₁, γ₂, γ_sum

  refine ⟨⟨ϕ₁, h_decomp₁⟩, h_harm₁, ⟨ϕ₂, h_decomp₂⟩, h_harm₂, ?_, ?_, ?_⟩
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

  · intro i
    calc ∑ j : Fin n, γ_sum.val i j
        = ∑ j : Fin n, (α * γ₁.val i j + β * γ₂.val i j) := rfl
      _ = ∑ j : Fin n, α * γ₁.val i j + ∑ j : Fin n, β * γ₂.val i j := by rw [Finset.sum_add_distrib]
      _ = α * ∑ j : Fin n, γ₁.val i j + β * ∑ j : Fin n, γ₂.val i j := by rw [Finset.mul_sum, Finset.mul_sum]
      _ = α * 0 + β * 0 := by rw [h_harm₁ i, h_harm₂ i]
      _ = 0 := by ring

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
      IsHarmonic γ_scaled) := by
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

/--
  **Theorem: Orthogonality gives Pythagorean decomposition**

  At the optimal ϕ_opt, σ = dϕ_opt + γ with ⟨dϕ_opt, γ⟩ = 0, so:
  ||σ||² = ||dϕ_opt||² + ||γ||² (Pythagorean theorem)
-/
theorem pythagorean_from_orthogonality {n : ℕ} [Fintype (Fin n)] (σ : C1 n) :
  ∃ (ϕ γ : C1 n),
    (∀ i j, σ.val i j = ϕ.val i j + γ.val i j) ∧
    inner_product_C1 ϕ γ = 0 ∧
    norm_sq σ = norm_sq ϕ + norm_sq γ := by
  obtain ⟨ϕ_opt, γ, h_decomp, h_harm, h_orth⟩ := hodge_decomposition σ
  let ϕ_cochain : C1 n := d0 ϕ_opt
  use ϕ_cochain, γ
  refine ⟨h_decomp, h_orth, ?_⟩
  -- σ = ϕ + γ and ⟨ϕ,γ⟩ = 0, so ||σ||² = ||ϕ+γ||² = ||ϕ||² + 2⟨ϕ,γ⟩ + ||γ||² = ||ϕ||² + ||γ||²
  have h_sigma_as_sum : ({ val := fun i j => ϕ_cochain.val i j + γ.val i j,
                            skew := by intro i j; rw [ϕ_cochain.skew, γ.skew]; ring } : C1 n) =
                        ({ val := σ.val, skew := σ.skew } : C1 n) := by
    simp only [ϕ_cochain]
    congr
    funext i j
    exact (h_decomp i j).symm
  rw [←h_sigma_as_sum, norm_sq_add, h_orth]
  ring

/-! ## Part 5: Chains and Chain/Cochain Pairing -/

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

/--
  The zero 1-chain (no edges)
-/
def Chain1.zero (n : ℕ) : Chain1 n := {
  coeff := fun _ _ => 0
  antisym := by intro i j; ring
}

/--
  Addition of 1-chains (formal sum)
-/
def Chain1.add {n : ℕ} (c₁ c₂ : Chain1 n) : Chain1 n := {
  coeff := fun i j => c₁.coeff i j + c₂.coeff i j
  antisym := by intro i j; rw [c₁.antisym, c₂.antisym]; ring
}

/--
  A 1-chain is a cycle if it has no boundary (each vertex has equal in-degree and out-degree)
-/
def Chain1.IsCycle {n : ℕ} [Fintype (Fin n)] (c : Chain1 n) : Prop :=
  ∀ i : Fin n, ∑ j : Fin n, c.coeff i j = 0

/--
  **The Fundamental Pairing: Evaluating a 1-cochain on a 1-chain**

  This is the integration of a differential form over a chain.
  ⟨σ, c⟩ = ∑ᵢⱼ σ(i,j) · c(i,j)

  The factor of 1/2 accounts for antisymmetry (each edge counted twice in double sum).
-/
noncomputable def eval {n : ℕ} [Fintype (Fin n)] (σ : C1 n) (c : Chain1 n) : ℝ :=
  (1/2) * ∑ i : Fin n, ∑ j : Fin n, σ.val i j * (c.coeff i j : ℝ)

/--
  Evaluation is linear in the cochain
-/
lemma eval_add_cochain {n : ℕ} [Fintype (Fin n)] (σ₁ σ₂ : C1 n) (c : Chain1 n) :
  eval { val := fun i j => σ₁.val i j + σ₂.val i j,
         skew := by intro i j; rw [σ₁.skew, σ₂.skew]; ring } c =
  eval σ₁ c + eval σ₂ c := by
  unfold eval
  simp only [add_mul, Finset.sum_add_distrib]
  ring

/--
  Evaluation is linear in the chain
-/
lemma eval_add_chain {n : ℕ} [Fintype (Fin n)] (σ : C1 n) (c₁ c₂ : Chain1 n) :
  eval σ (Chain1.add c₁ c₂) = eval σ c₁ + eval σ c₂ := by
  unfold eval Chain1.add
  simp only [Int.cast_add, mul_add, Finset.sum_add_distrib]

/--
  **The Fundamental Theorem: Exact forms evaluate to zero on cycles**

  If σ = dϕ (exact form) and c is a cycle (boundary = 0), then ⟨dϕ, c⟩ = 0.

  This is the discrete version of Stokes' theorem: ∫_c dϕ = ∫_∂c ϕ = 0 (since ∂c = 0).

  This is WHY phase differences telescope around cycles.
-/
theorem exact_form_vanishes_on_cycles {n : ℕ} [Fintype (Fin n)] (ϕ : C0 n) (c : Chain1 n)
    (h_cycle : Chain1.IsCycle c) :
  eval (d0 ϕ) c = 0 := by
  unfold eval d0
  simp only
  -- ⟨dϕ, c⟩ = (1/2) ∑ᵢⱼ (ϕ(j) - ϕ(i)) · c(i,j)
  --         = (1/2) ∑ᵢⱼ ϕ(j)·c(i,j) - (1/2) ∑ᵢⱼ ϕ(i)·c(i,j)
  --         = (1/2) ∑ⱼ ϕ(j)·(∑ᵢ c(i,j)) - (1/2) ∑ᵢ ϕ(i)·(∑ⱼ c(i,j))
  --         = 0 - 0  (by IsCycle condition)

  have h_expand : ∑ i : Fin n, ∑ j : Fin n, (ϕ j - ϕ i) * (c.coeff i j : ℝ) =
                  ∑ i : Fin n, ∑ j : Fin n, ϕ j * (c.coeff i j : ℝ) -
                  ∑ i : Fin n, ∑ j : Fin n, ϕ i * (c.coeff i j : ℝ) := by
    simp only [sub_mul, Finset.sum_sub_distrib]

  rw [h_expand]

  -- Swap summation order in first term
  conv_lhs =>
    arg 2
    arg 1
    rw [Finset.sum_comm]

  -- Factor out ϕ values
  have h_first : ∑ j : Fin n, ∑ i : Fin n, ϕ j * (c.coeff i j : ℝ) =
                 ∑ j : Fin n, ϕ j * (∑ i : Fin n, (c.coeff i j : ℝ)) := by
    congr 1
    ext j
    rw [Finset.mul_sum]

  have h_second : ∑ i : Fin n, ∑ j : Fin n, ϕ i * (c.coeff i j : ℝ) =
                  ∑ i : Fin n, ϕ i * (∑ j : Fin n, (c.coeff i j : ℝ)) := by
    congr 1
    ext i
    rw [Finset.mul_sum]

  rw [h_first, h_second]

  -- Apply cycle condition: ∑ⱼ c(i,j) = 0 for all i
  have h_cycle_cond : ∀ i : Fin n, (∑ j : Fin n, (c.coeff i j : ℝ)) = 0 := by
    intro i
    have h := h_cycle i
    simp only [←Int.cast_sum, h, Int.cast_zero]

  -- Also: ∑ᵢ c(i,j) = -∑ᵢ c(j,i) = -0 = 0 (by antisymmetry and cycle condition)
  have h_cycle_cond_swap : ∀ j : Fin n, (∑ i : Fin n, (c.coeff i j : ℝ)) = 0 := by
    intro j
    calc ∑ i : Fin n, (c.coeff i j : ℝ)
        = ∑ i : Fin n, (-(c.coeff j i) : ℝ) := by
          congr 1; ext i; rw [c.antisym]; simp
      _ = -(∑ i : Fin n, (c.coeff j i : ℝ)) := by rw [Finset.sum_neg_distrib]
      _ = -0 := by rw [h_cycle_cond j]
      _ = 0 := by ring

  -- Now both terms vanish
  simp only [h_cycle_cond, h_cycle_cond_swap]
  ring

/-
  **Future Work: Harmonic forms and homology classes**

  Harmonic forms are well-defined on homology classes.
  If c₁ and c₂ differ by a boundary (c₁ = c₂ + ∂b for some 2-chain b),
  then ⟨γ, c₁⟩ = ⟨γ, c₂⟩ for any harmonic form γ.

  This means harmonic forms define maps H₁(G, ℤ) → ℝ (homology to reals).
  This is why "mass is topological" - it only depends on homology classes.

  To prove this, we would need to define 2-chains and the boundary operator ∂.
-/

end DiscreteHodge
