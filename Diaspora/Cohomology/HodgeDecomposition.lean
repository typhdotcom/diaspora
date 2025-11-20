/-
# Hodge Decomposition

The core decomposition theorem: every 1-cochain σ splits uniquely as σ = dϕ + γ
where dϕ is exact and γ is harmonic, with dϕ ⊥ γ.

This file contains the heavy functional analysis proofs. Downstream files import
only the theorem statements, not the proof details.
-/

import Diaspora.Cohomology.DiscreteCalculus
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

/-! ## Supporting Lemmas -/

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

/-- Harmonic forms ↔ divergence-free -/
lemma IsHarmonic_iff_divergence_zero {n : ℕ} [Fintype (Fin n)] (σ : C1 n) :
  IsHarmonic σ ↔ divergence σ = (fun _ => 0 : C0 n) := by
  constructor
  · intro h
    funext i
    unfold divergence
    specialize h i
    simp [h]
  · intro h i
    have := congrArg (fun f => f i) h
    unfold divergence at this
    linarith

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

/-- Expand the Laplacian: (Δϕ)ᵢ = -∑ⱼ (ϕⱼ - ϕᵢ) = ∑ⱼ (ϕᵢ - ϕⱼ) -/
lemma laplacian_expansion {n : ℕ} [Fintype (Fin n)] (ϕ : C0 n) (i : Fin n) :
  graph_laplacian ϕ i = - ∑ j : Fin n, (ϕ j - ϕ i) := by
  unfold graph_laplacian divergence d0
  rfl

/-- Helper: The objective function we're minimizing -/
noncomputable def objective {n : ℕ} [Fintype (Fin n)] (σ : C1 n) (ϕ : C0 n) : ℝ :=
  norm_sq { val := fun i j => (d0 ϕ).val i j - σ.val i j,
            skew := by intro i j; simp [d0]; rw [σ.skew]; ring }

/-! ## Main Theorems -/

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

/-- σ = d⁰ϕ + γ where d⁰ϕ is exact, γ is harmonic, and d⁰ϕ ⊥ γ -/
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

end DiscreteHodge
