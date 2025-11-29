/-
# Harmonic Analysis

Algebraic consequences of the Hodge decomposition: physical theorems about
minimization, linearity, orthogonality, holonomy, and spectral properties.

These are the "Lego blocks" of the physical theory.
-/

import Diaspora.Hodge.Decomposition
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open BigOperators Complex Diaspora.Core

namespace Diaspora.Hodge

/-! ## Physical Theorems -/

/-- V_int(X) = || d⁰ϕ - σ ||² -/
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

/-- V_int as norm of residual -/
lemma V_int_eq_norm_residual {n : ℕ} [Fintype (Fin n)] (ϕ : C0 n) (σ : C1 n) :
  norm_sq (Diaspora.Core.residual ϕ σ) =
    (1/2) * ∑ i, ∑ j, ((ϕ j - ϕ i) - σ.val i j)^2 := by
  simpa [Diaspora.Core.residual] using V_int_is_cohomological_distance (n:=n) ϕ σ

/-- Min || d⁰ϕ - σ ||² = || γ ||² -/
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

/-- Harmonic(α·σ₁ + β·σ₂) = α·Harmonic(σ₁) + β·Harmonic(σ₂) -/
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

/-- Scaling constraints linearly scales the exact component of the solution -/
theorem inheritance_is_linearity {n : ℕ} [Fintype (Fin n)] (σ : C1 n) :
  ∃ (ϕ_opt : C0 n) (γ : C1 n),
    (∀ i j, σ.val i j = (d0 ϕ_opt).val i j + γ.val i j) ∧
    IsHarmonic γ ∧
    (∀ α : ℝ,
      let σ_scaled : C1 n := { val := fun i j => α * σ.val i j,
                                skew := by intro i j; rw [σ.skew]; ring }
      let ϕ_scaled : C0 n := fun i => α * ϕ_opt i
      let γ_scaled : C1 n := { val := fun i j => α * γ.val i j,
                                skew := by intro i j; rw [γ.skew]; ring }
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

/-- Scaling a 1-cochain scales its norm squared by α² -/
lemma norm_sq_smul {n : ℕ} [Fintype (Fin n)] (α : ℝ) (σ : C1 n) :
  norm_sq
    { val := fun i j => α * σ.val i j,
      skew := by intro i j; rw [σ.skew]; ring }
  = α^2 * norm_sq σ := by
  unfold norm_sq inner_product_C1
  simp [pow_two, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]

/-- ||σ||² = ||dϕ_opt||² + ||γ||² -/
theorem pythagorean_from_orthogonality {n : ℕ} [Fintype (Fin n)] (σ : C1 n) :
  ∃ (ϕ γ : C1 n),
    (∀ i j, σ.val i j = ϕ.val i j + γ.val i j) ∧
    inner_product_C1 ϕ γ = 0 ∧
    norm_sq σ = norm_sq ϕ + norm_sq γ := by
  obtain ⟨ϕ_opt, γ, h_decomp, h_harm, h_orth⟩ := hodge_decomposition σ
  let ϕ_cochain : C1 n := d0 ϕ_opt
  use ϕ_cochain, γ
  refine ⟨h_decomp, h_orth, ?_⟩
  have h_sigma_as_sum : ({ val := fun i j => ϕ_cochain.val i j + γ.val i j,
                            skew := by intro i j; rw [ϕ_cochain.skew, γ.skew]; ring } : C1 n) =
                        ({ val := σ.val, skew := σ.skew } : C1 n) := by
    simp only [ϕ_cochain]
    congr
    funext i j
    exact (h_decomp i j).symm
  rw [←h_sigma_as_sum, norm_sq_add, h_orth]
  ring

/-! ## Stokes' Theorem and Holonomy -/

lemma eval_add_cochain {n : ℕ} [Fintype (Fin n)] (σ₁ σ₂ : C1 n) (c : Chain1 n) :
  eval { val := fun i j => σ₁.val i j + σ₂.val i j,
         skew := by intro i j; rw [σ₁.skew, σ₂.skew]; ring } c =
  eval σ₁ c + eval σ₂ c := by
  unfold eval
  simp only [add_mul, Finset.sum_add_distrib]
  ring

lemma eval_add_chain {n : ℕ} [Fintype (Fin n)] (σ : C1 n) (c₁ c₂ : Chain1 n) :
  eval σ (Chain1.add c₁ c₂) = eval σ c₁ + eval σ c₂ := by
  unfold eval Chain1.add
  simp only [Int.cast_add, mul_add, Finset.sum_add_distrib]

/-- Stokes' theorem: ⟨dϕ, c⟩ = 0 for cycles c -/
theorem exact_form_vanishes_on_cycles {n : ℕ} [Fintype (Fin n)] (ϕ : C0 n) (c : Chain1 n)
    (h_cycle : Chain1.IsCycle c) :
  eval (d0 ϕ) c = 0 := by
  unfold eval d0
  simp only
  have h_expand : ∑ i : Fin n, ∑ j : Fin n, (ϕ j - ϕ i) * (c.coeff i j : ℝ) =
                  ∑ i : Fin n, ∑ j : Fin n, ϕ j * (c.coeff i j : ℝ) -
                  ∑ i : Fin n, ∑ j : Fin n, ϕ i * (c.coeff i j : ℝ) := by
    simp only [sub_mul, Finset.sum_sub_distrib]

  rw [h_expand]
  conv_lhs =>
    arg 2
    arg 1
    rw [Finset.sum_comm]
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
  have h_cycle_cond : ∀ i : Fin n, (∑ j : Fin n, (c.coeff i j : ℝ)) = 0 := by
    intro i
    have h := h_cycle i
    simp only [←Int.cast_sum, h, Int.cast_zero]
  have h_cycle_cond_swap : ∀ j : Fin n, (∑ i : Fin n, (c.coeff i j : ℝ)) = 0 := by
    intro j
    calc ∑ i : Fin n, (c.coeff i j : ℝ)
        = ∑ i : Fin n, (-(c.coeff j i) : ℝ) := by
          congr 1; ext i; rw [c.antisym]; simp
      _ = -(∑ i : Fin n, (c.coeff j i : ℝ)) := by rw [Finset.sum_neg_distrib]
      _ = -0 := by rw [h_cycle_cond j]
      _ = 0 := by ring
  simp only [h_cycle_cond, h_cycle_cond_swap]
  ring

/-- Exact forms vanish on cycles -/
lemma holonomy_exact_zero_on_cycles {n : ℕ} [Fintype (Fin n)]
    (ϕ : C0 n) (c : Chain1 n) (h_cycle : Chain1.IsCycle c) :
  holonomy (d0 ϕ) c = 0 := by
  unfold holonomy
  exact exact_form_vanishes_on_cycles ϕ c h_cycle

/-- Holonomy is linear in the cochain -/
lemma holonomy_add_cochain {n : ℕ} [Fintype (Fin n)]
    (σ₁ σ₂ : C1 n) (c : Chain1 n) :
  holonomy
    { val := fun i j => σ₁.val i j + σ₂.val i j,
      skew := by intro i j; rw [σ₁.skew, σ₂.skew]; ring } c
  = holonomy σ₁ c + holonomy σ₂ c := by
  unfold holonomy
  exact eval_add_cochain σ₁ σ₂ c

/-- Holonomy is linear in the chain -/
lemma holonomy_add_chain {n : ℕ} [Fintype (Fin n)]
    (σ : C1 n) (c₁ c₂ : Chain1 n) :
  holonomy σ (Chain1.add c₁ c₂) =
  holonomy σ c₁ + holonomy σ c₂ := by
  unfold holonomy
  exact eval_add_chain σ c₁ c₂

/-- Holonomy scales with the cochain -/
lemma holonomy_smul_cochain {n : ℕ} [Fintype (Fin n)]
    (α : ℝ) (σ : C1 n) (c : Chain1 n) :
  holonomy
    { val := fun i j => α * σ.val i j,
      skew := by intro i j; rw [σ.skew]; ring } c
  = α * holonomy σ c := by
  unfold holonomy eval
  simp [Finset.mul_sum, mul_assoc, mul_left_comm]

/-- Holonomy of σ on any cycle depends only on its harmonic component. -/
lemma holonomy_factor_through_harmonic {n : ℕ} [Fintype (Fin n)]
    (σ : C1 n) :
  ∃ γ : C1 n, IsHarmonic γ ∧
    ∃ ϕ : C0 n,
      (∀ i j, σ.val i j = (d0 ϕ).val i j + γ.val i j) ∧
      ∀ c : Chain1 n, Chain1.IsCycle c →
        holonomy σ c = holonomy γ c := by
  obtain ⟨ϕ, γ, h_decomp, h_harm, h_orth⟩ := hodge_decomposition σ
  refine ⟨γ, h_harm, ϕ, h_decomp, ?_⟩
  intro c h_cycle

  have hσ :
      σ =
        { val := fun i j => (d0 ϕ).val i j + γ.val i j,
          skew := by
            intro i j
            unfold d0
            rw [γ.skew]
            have := h_decomp i j
            have := h_decomp j i
            linarith } := by
    cases σ
    congr
    funext i j
    exact h_decomp i j

  have h_split :
      holonomy σ c =
        holonomy (d0 ϕ) c + holonomy γ c := by
    rw [hσ]
    exact holonomy_add_cochain (σ₁ := d0 ϕ) (σ₂ := γ) c

  have h_exact_zero : holonomy (d0 ϕ) c = 0 :=
    holonomy_exact_zero_on_cycles ϕ c h_cycle

  simp [h_split, h_exact_zero]

/-- The harmonic component of the averaged constraints is the average of the
    harmonic components. This is the cohomological "law of averaging". -/
lemma harmonic_projection_average {n : ℕ} [Fintype (Fin n)] (σ₁ σ₂ : C1 n) :
  ∃ (γ₁ γ₂ γ_avg : C1 n),
    (∃ ϕ₁ : C0 n, ∀ i j, σ₁.val i j = (d0 ϕ₁).val i j + γ₁.val i j) ∧
    IsHarmonic γ₁ ∧
    (∃ ϕ₂ : C0 n, ∀ i j, σ₂.val i j = (d0 ϕ₂).val i j + γ₂.val i j) ∧
    IsHarmonic γ₂ ∧
    (let σ_avg : C1 n :=
      { val := fun i j => (σ₁.val i j + σ₂.val i j) / 2,
        skew := by
          intro i j
          have h1 := σ₁.skew i j
          have h2 := σ₂.skew i j
          field_simp
          rw [h1, h2]
          ring }
     ∃ ϕ_avg : C0 n, ∀ i j, σ_avg.val i j = (d0 ϕ_avg).val i j + γ_avg.val i j) ∧
    IsHarmonic γ_avg ∧
    (∀ i j, γ_avg.val i j = (γ₁.val i j + γ₂.val i j) / 2) := by
  have h := harmonic_projection_is_linear (σ₁ := σ₁) (σ₂ := σ₂)
                  (α := (1/2 : ℝ)) (β := (1/2 : ℝ))
  rcases h with ⟨γ₁, γ₂, γ_sum, h₁, h_harm₁, h₂, h_harm₂, h_sum_decomp, h_harm_sum, h_sum_eq⟩

  refine ⟨γ₁, γ₂, γ_sum, h₁, h_harm₁, h₂, h_harm₂, ?_, h_harm_sum, ?_⟩

  · rcases h_sum_decomp with ⟨ϕ_sum, hϕ_sum⟩
    refine ⟨ϕ_sum, ?_⟩
    intro i j
    have := hϕ_sum i j
    show (σ₁.val i j + σ₂.val i j) / 2 = (d0 ϕ_sum).val i j + γ_sum.val i j
    rw [add_div]
    convert this using 2 <;> ring

  · intro i j
    have := h_sum_eq i j
    field_simp at this ⊢
    linarith

/-! ## Spectral Theory -/

/-- The quadratic form ⟨d0 ϕ, d0 ϕ⟩ is nonnegative -/
lemma inner_d0_nonneg {n : ℕ} [Fintype (Fin n)] (ϕ : C0 n) :
  inner_product_C1 (d0 ϕ) (d0 ϕ) ≥ 0 := by
  unfold inner_product_C1
  have : ∑ i, ∑ j, (d0 ϕ).val i j * (d0 ϕ).val i j ≥ 0 := by
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro j _
    exact mul_self_nonneg _
  have : (1/2 : ℝ) * _ ≥ 0 := mul_nonneg (by norm_num) this
  simpa [norm_sq] using this

/-- Constant functions are zero-eigenvalue eigenvectors -/
theorem zero_is_eigenvalue {n : ℕ} [Fintype (Fin n)] (c : ℝ) :
  IsEigenvector (fun _ : Fin n => c) 0 := by
  unfold IsEigenvector
  intro i
  unfold graph_laplacian divergence d0
  simp only
  have h_const_sum : ∑ j : Fin n, (c - c) = 0 := by
    simp only [sub_self, Finset.sum_const_zero]
  rw [h_const_sum]
  ring

lemma constant_in_kernel {n : ℕ} [Fintype (Fin n)] (c : ℝ) :
  ∀ i j, (d0 (fun _ : Fin n => c)).val i j = 0 := by
  intro i j
  unfold d0
  simp only
  ring

/-! ## Quantum Harmonic Properties -/

/-- The Hermitian inner product is conjugate-symmetric -/
lemma inner_QC0_conj {n : ℕ} [Fintype (Fin n)] (ψ φ : QC0 n) :
  inner_QC0 ψ φ = star (inner_QC0 φ ψ) := by
  unfold inner_QC0
  rw [star_sum]
  congr 1
  ext i
  simp [mul_comm]

/-- Expand the quantum Laplacian -/
lemma quantum_laplacian_expansion {n : ℕ} [Fintype (Fin n)] (ψ : QC0 n) (i : Fin n) :
  quantum_laplacian ψ i = -∑ j : Fin n, (ψ j - ψ i) := by
  unfold quantum_laplacian qdivergence qd0
  rfl

/-- The quantum Laplacian is Hermitian (self-adjoint) -/
theorem quantum_laplacian_hermitian {n : ℕ} [Fintype (Fin n)] (ψ φ : QC0 n) :
  inner_QC0 (quantum_laplacian ψ) φ = inner_QC0 ψ (quantum_laplacian φ) := by
  unfold inner_QC0 quantum_laplacian qdivergence qd0

  simp only [star_neg, neg_mul, mul_neg, Finset.sum_neg_distrib]
  simp only [star_sum, star_sub]

  conv_lhs => enter [1, 2, i]; rw [Finset.sum_mul]
  conv_rhs => enter [1, 2, i]; rw [Finset.mul_sum]

  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]

  congr 1
  rw [Finset.sum_comm]

/-- A quantum state is an energy eigenstate with energy E if Ĥψ = Eψ
    (Hamiltonian Ĥ = -Δ, so eigenvalue of Δ is -E) -/
def IsEnergyEigenstate {n : ℕ} [Fintype (Fin n)] (ψ : QC0 n) (E : ℝ) : Prop :=
  ∀ i : Fin n, quantum_laplacian ψ i = -E * ψ i

/-- Constant phase is zero-energy eigenstate (gauge freedom) -/
theorem constant_is_zero_energy {n : ℕ} [Fintype (Fin n)] (c : ℂ) :
  IsEnergyEigenstate (fun _ : Fin n => c) 0 := by
  unfold IsEnergyEigenstate quantum_laplacian qdivergence qd0
  intro i
  simp only [sub_self, Finset.sum_const_zero, neg_zero]
  norm_num

/-- Embedding real phases into quantum states -/
def classical_to_quantum {n : ℕ} (φ : C0 n) : QC0 n :=
  fun i => (φ i : ℂ)

/-- The quantum Laplacian restricts to classical Laplacian on real states -/
theorem quantum_laplacian_extends_classical {n : ℕ} [Fintype (Fin n)] (φ : C0 n) :
  ∀ i, quantum_laplacian (classical_to_quantum φ) i =
       (graph_laplacian φ i : ℂ) := by
  intro i
  unfold quantum_laplacian qdivergence qd0 classical_to_quantum
  unfold graph_laplacian divergence d0
  simp only [ofReal_sub, ofReal_sum, ofReal_neg]

/-- A quantum 1-chain (same as classical) -/
abbrev QChain1 := Chain1

/-- Evaluation of quantum 1-cochain on 1-chain (complex-valued holonomy) -/
noncomputable def qeval {n : ℕ} [Fintype (Fin n)] (σ : QC1 n) (c : QChain1 n) : ℂ :=
  (1/2) * ∑ i : Fin n, ∑ j : Fin n, σ.val i j * (c.coeff i j : ℂ)

/-- Quantum Stokes' theorem: exact forms vanish on cycles -/
theorem quantum_exact_vanishes_on_cycles {n : ℕ} [Fintype (Fin n)]
    (ψ : QC0 n) (c : QChain1 n) (h_cycle : Chain1.IsCycle c) :
  qeval (qd0 ψ) c = 0 := by
  unfold qeval qd0
  simp only

  have h_expand : ∑ i : Fin n, ∑ j : Fin n, (ψ j - ψ i) * (c.coeff i j : ℂ) =
                  ∑ i : Fin n, ∑ j : Fin n, ψ j * (c.coeff i j : ℂ) -
                  ∑ i : Fin n, ∑ j : Fin n, ψ i * (c.coeff i j : ℂ) := by
    simp only [sub_mul, Finset.sum_sub_distrib]

  rw [h_expand]

  conv_lhs =>
    arg 2
    arg 1
    rw [Finset.sum_comm]

  have h_first : ∑ j : Fin n, ∑ i : Fin n, ψ j * (c.coeff i j : ℂ) =
                 ∑ j : Fin n, ψ j * (∑ i : Fin n, (c.coeff i j : ℂ)) := by
    congr 1
    ext j
    rw [Finset.mul_sum]

  have h_second : ∑ i : Fin n, ∑ j : Fin n, ψ i * (c.coeff i j : ℂ) =
                  ∑ i : Fin n, ψ i * (∑ j : Fin n, (c.coeff i j : ℂ)) := by
    congr 1
    ext i
    rw [Finset.mul_sum]

  rw [h_first, h_second]

  have h_cycle_cond : ∀ i : Fin n, (∑ j : Fin n, (c.coeff i j : ℂ)) = 0 := by
    intro i
    have h := h_cycle i
    simp only [←Int.cast_sum, h, Int.cast_zero]

  have h_cycle_cond_swap : ∀ j : Fin n, (∑ i : Fin n, (c.coeff i j : ℂ)) = 0 := by
    intro j
    calc ∑ i : Fin n, (c.coeff i j : ℂ)
        = ∑ i : Fin n, (-(c.coeff j i) : ℂ) := by
          congr 1; ext i; rw [c.antisym]; simp
      _ = -(∑ i : Fin n, (c.coeff j i : ℂ)) := by
          simp only [Finset.sum_neg_distrib]
      _ = -0 := by rw [h_cycle_cond j]
      _ = 0 := by ring

  simp only [h_cycle_cond, h_cycle_cond_swap, mul_zero, Finset.sum_const_zero]
  ring

/-! ## Harmonic Forms on Simple Cycles -/

/--
A simple cycle is one where each node has exactly two neighbors in the cycle.
This structure captures paths like 0→1→2→3→0 where each vertex appears exactly once.

The key property is that the entire set forms a single connected cycle under `next`,
meaning every element can be reached from any other by iterating `next`.
-/
structure SimpleCycle (n : ℕ) where
  /-- The successor function defining the cycle structure -/
  next : Fin n → Fin n
  /-- The predecessor function -/
  prev : Fin n → Fin n
  /-- next is injective (each node has a unique successor) -/
  next_injective : Function.Injective next
  /-- prev is injective (each node has a unique predecessor) -/
  prev_injective : Function.Injective prev
  /-- next and prev are inverses -/
  next_prev : ∀ i, next (prev i) = i
  prev_next : ∀ i, prev (next i) = i
  /-- The cycle is connected: every element is reachable from any other -/
  connected [Fintype (Fin n)] [Inhabited (Fin n)] :
    ∀ i j : Fin n, ∃ k : ℕ, next^[k] i = j

/--
A harmonic form is supported on a simple cycle if it's zero on all edges
not in the cycle.
-/
def SupportedOnCycle {n : ℕ} (cycle : SimpleCycle n) (γ : C1 n) : Prop :=
  ∀ i j : Fin n, j ≠ cycle.next i → γ.val i j = 0

/-- Consecutive edges in a harmonic form on a cycle have equal values. -/
lemma consecutive_edges_equal {n : ℕ} [Fintype (Fin n)]
    (cycle : SimpleCycle n) (γ : C1 n)
    (h_harm : IsHarmonic γ)
    (h_support : SupportedOnCycle cycle γ)
    (i : Fin n) :
  γ.val i (cycle.next i) = γ.val (cycle.next i) (cycle.next (cycle.next i)) := by
  let j := cycle.next i
  have h_isolation_j : ∀ x, x ≠ cycle.prev j ∧ x ≠ cycle.next j → γ.val j x = 0 := by
    intro x ⟨h_ne_prev, h_ne_next⟩
    exact h_support j x h_ne_next
  have h_transfer_j := harmonic_flow_transfer γ j (cycle.prev j) (cycle.next j) h_harm h_isolation_j
  have h_prev_j : cycle.prev j = i := by
    calc cycle.prev j
        = cycle.prev (cycle.next i) := rfl
      _ = i := cycle.prev_next i
  rw [h_prev_j] at h_transfer_j
  exact h_transfer_j

/--
On a simple cycle, if a harmonic form is supported on that cycle,
then it has the same value on every edge of the cycle.
-/
lemma next_surjective {n : ℕ} [Fintype (Fin n)] (cycle : SimpleCycle n) :
    Function.Surjective cycle.next := by
  intro j
  use cycle.prev j
  exact cycle.next_prev j

lemma next_bijective {n : ℕ} [Fintype (Fin n)] (cycle : SimpleCycle n) :
    Function.Bijective cycle.next :=
  ⟨cycle.next_injective, next_surjective cycle⟩

theorem harmonic_constant_on_simple_cycle {n : ℕ} [Fintype (Fin n)]
    (cycle : SimpleCycle n) (γ : C1 n)
    (h_harm : IsHarmonic γ)
    (h_support : SupportedOnCycle cycle γ)
    [Inhabited (Fin n)] :
  ∃ k : ℝ, ∀ i : Fin n, γ.val i (cycle.next i) = k := by
  classical
  let i₀ : Fin n := default
  use γ.val i₀ (cycle.next i₀)
  intro i
  have h_consec : ∀ j : Fin n, γ.val j (cycle.next j) = γ.val (cycle.next j) (cycle.next (cycle.next j)) :=
    fun j => consecutive_edges_equal cycle γ h_harm h_support j
  let f : Fin n → ℝ := fun j => γ.val j (cycle.next j)
  have h_f_constant : ∀ j : Fin n, f j = f (cycle.next j) := by
    intro j
    exact h_consec j
  have h_iterate : ∀ (j : Fin n) (k : ℕ), f (cycle.next^[k] j) = f j := by
    intro j k
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [Function.iterate_succ_apply']
      calc f (cycle.next (cycle.next^[k] j))
          = f (cycle.next^[k] j) := (h_f_constant _).symm
        _ = f j := ih
  have h_in_orbit : ∃ k : ℕ, cycle.next^[k] i₀ = i := by
    classical
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective cycle.next (next_bijective cycle)
    have h_same_cycle : Equiv.Perm.SameCycle σ i₀ i := by
      classical
      have h_conn := cycle.connected i₀ i
      obtain ⟨k, hk⟩ := h_conn
      have h_pow_eq_next : ∀ m : ℕ, ∀ x : Fin n, (σ ^ m) x = cycle.next^[m] x := by
        intro m x
        induction m generalizing x with
        | zero => simp [pow_zero, Function.iterate_zero]
        | succ m ih =>
          simp only [pow_succ]
          rw [Equiv.Perm.mul_apply]
          have h_σ : σ x = cycle.next x := rfl
          rw [h_σ, ih]
          rfl
      use (k : ℤ)
      rw [zpow_natCast, h_pow_eq_next, hk]
    have := Equiv.Perm.SameCycle.exists_nat_pow_eq h_same_cycle
    obtain ⟨k, hk⟩ := this
    have h_pow_eq : ∀ m : ℕ, ∀ x : Fin n, (σ ^ m) x = cycle.next^[m] x := by
      intro m x
      induction m generalizing x with
      | zero => simp [pow_zero, Function.iterate_zero]
      | succ m ih =>
        simp only [pow_succ]
        rw [Equiv.Perm.mul_apply]
        have h_σ : σ x = cycle.next x := rfl
        rw [h_σ, ih]
        rfl
    exact ⟨k, by rw [← h_pow_eq, hk]⟩
  obtain ⟨k, hk⟩ := h_in_orbit
  calc f i
      = f (cycle.next^[k] i₀) := by rw [←hk]
    _ = f i₀ := h_iterate i₀ k

/-- The 1-chain representing a simple cycle (1 on each edge i → next i). -/
def SimpleCycle.toChain1 {n : ℕ} (cycle : SimpleCycle n) : Chain1 n := {
  coeff := fun i j =>
    if j = cycle.next i ∧ i ≠ cycle.next j then 1
    else if i = cycle.next j ∧ j ≠ cycle.next i then -1
    else 0
  antisym := by
    intro i j
    split
    · rename_i h
      split
      · rename_i h'
        -- Contradiction: h says i ≠ next j, h' says i = next j
        exact absurd h'.1 h.2
      · ring
    · split <;> ring
}

/--
Holonomy calibration: if a harmonic form γ has constant value k on every edge
of a simple cycle, then the holonomy equals n·k.
-/
theorem holonomy_of_constant_harmonic {n : ℕ} [Fintype (Fin n)]
    (cycle : SimpleCycle n) (γ : C1 n) (k : ℝ)
    (h_const : ∀ i : Fin n, γ.val i (cycle.next i) = k) :
  holonomy γ (SimpleCycle.toChain1 cycle) = (Fintype.card (Fin n)) * k := by
  unfold holonomy eval
  have h_sum : ∀ i : Fin n,
      ∑ j : Fin n, γ.val i j * (cycle.toChain1.coeff i j : ℝ) = 2 * k := by
    intro i
    simp only [SimpleCycle.toChain1]
    let s : Finset (Fin n) := {cycle.prev i, cycle.next i}
    trans (∑ j ∈ s, γ.val i j * ↑(cycle.toChain1.coeff i j))
    · symm
      refine Finset.sum_subset (Finset.subset_univ s) ?_
      intro j _ hj
      simp [s, Finset.mem_insert, Finset.mem_singleton] at hj
      push_neg at hj
      simp only [SimpleCycle.toChain1]
      split_ifs with h1 h2
      · exact absurd h1.1 hj.2
      · have : j = cycle.prev i := by
          have : cycle.prev (cycle.next j) = cycle.prev i := by rw [h2.1]
          rw [cycle.prev_next] at this
          exact this
        exact absurd this hj.1
      · ring
    by_cases h_distinct : cycle.prev i ≠ cycle.next i
    case pos =>
      have h_pair : s = {cycle.prev i, cycle.next i} := rfl
      have h_ne : cycle.prev i ≠ cycle.next i := h_distinct
      rw [Finset.sum_pair h_ne]
      have h_coeff_prev : (cycle.toChain1.coeff i (cycle.prev i) : ℝ) = -1 := by
        simp only [SimpleCycle.toChain1]
        have h_not_eq : ¬(cycle.prev i = cycle.next i ∧ i ≠ cycle.next (cycle.prev i)) := by
          simp [h_ne]
        have h_is_prev : i = cycle.next (cycle.prev i) ∧ cycle.prev i ≠ cycle.next i := by
          exact ⟨(cycle.next_prev i).symm, h_ne⟩
        simp only [if_neg h_not_eq, if_pos h_is_prev]
        norm_num
      have h_coeff_next : (cycle.toChain1.coeff i (cycle.next i) : ℝ) =
                          (if i ≠ cycle.next (cycle.next i) then 1 else 0) := by
        simp only [SimpleCycle.toChain1, true_and]
        by_cases h_next2 : i ≠ cycle.next (cycle.next i)
        · simp [h_next2]
        · simp [h_next2]
      have h_next2_ne : i ≠ cycle.next (cycle.next i) := by
        intro h_eq
        have : cycle.prev i = cycle.next i := by
          apply cycle.next_injective
          calc cycle.next (cycle.prev i)
              = i := cycle.next_prev i
            _ = cycle.next (cycle.next i) := h_eq
        exact h_ne this
      have h_coeff_next_eq : (cycle.toChain1.coeff i (cycle.next i) : ℝ) = 1 := by
        rw [h_coeff_next]
        simp [h_next2_ne]
      simp only [h_coeff_prev, h_coeff_next_eq]
      have h_val_next : γ.val i (cycle.next i) = k := h_const i
      have h_val_prev : γ.val i (cycle.prev i) = -k := by
        have h_i_eq : i = cycle.next (cycle.prev i) := (cycle.next_prev i).symm
        calc γ.val i (cycle.prev i)
            = -(γ.val (cycle.prev i) i) := by rw [γ.skew]
          _ = -(γ.val (cycle.prev i) (cycle.next (cycle.prev i))) := by rw [← h_i_eq]
          _ = -k := by rw [h_const]
      rw [h_val_prev, h_val_next]
      ring
    case neg =>
      push_neg at h_distinct
      have h_eq : cycle.prev i = cycle.next i := h_distinct
      have h_singleton : s = {cycle.next i} := by
        ext j
        simp [s, h_eq, Finset.mem_singleton]
      rw [h_singleton, Finset.sum_singleton]
      have h_i_eq : i = cycle.next (cycle.next i) := by
        calc i = cycle.next (cycle.prev i) := (cycle.next_prev i).symm
             _ = cycle.next (cycle.next i) := by rw [h_eq]
      have h_coeff_zero : (cycle.toChain1.coeff i (cycle.next i) : ℝ) = 0 := by
        simp only [SimpleCycle.toChain1, true_and]
        have h1 : ¬(i ≠ cycle.next (cycle.next i)) := by
          intro h
          exact h h_i_eq
        rw [if_neg h1]
        have h2 : ¬(i = cycle.next (cycle.next i) ∧ cycle.next i ≠ cycle.next i) := by
          intro ⟨_, h⟩
          exact h rfl
        rw [if_neg h2]
        norm_num
      rw [h_coeff_zero]
      have h_k_zero : k = 0 := by
        have h_val := h_const i
        have h_skew : γ.val i (cycle.next i) = -γ.val (cycle.next i) i := γ.skew i (cycle.next i)
        have : γ.val (cycle.next i) i = k := by
          have h_next2 : cycle.next (cycle.next i) = i := by
            calc cycle.next (cycle.next i)
                = cycle.next (cycle.prev i) := by rw [← h_eq]
              _ = i := cycle.next_prev i
          calc γ.val (cycle.next i) i
              = γ.val (cycle.next i) (cycle.next (cycle.next i)) := by congr 1
            _ = k := h_const (cycle.next i)
        linarith
      rw [h_k_zero]
      ring
  have : ∑ i : Fin n, ∑ j : Fin n, γ.val i j * ↑(cycle.toChain1.coeff i j) =
         ∑ i : Fin n, 2 * k := Finset.sum_congr rfl (fun i _ => h_sum i)
  rw [this, Finset.sum_const, Finset.card_univ]
  ring

/-- Topological quantization: integer winding implies rational field values k = m/n. -/
theorem topological_quantization {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (cycle : SimpleCycle n) (γ : C1 n) (k : ℝ)
    (h_const : ∀ i, γ.val i (cycle.next i) = k)
    (m : ℤ)
    (h_topological : holonomy γ (SimpleCycle.toChain1 cycle) = m) :
  k = m / (Fintype.card (Fin n)) := by
  have h_total := holonomy_of_constant_harmonic cycle γ k h_const
  rw [h_topological] at h_total
  have h_card : (Fintype.card (Fin n) : ℝ) ≠ 0 := by simp
  field_simp [h_card] at h_total ⊢
  linarith

/-- Cycle cost: internal energy equals K²/n. -/
theorem cycle_creates_holonomy_cost {n : ℕ} [Fintype (Fin n)]
    (cycle : SimpleCycle n) (γ : C1 n)
    (h_harm : IsHarmonic γ)
    (h_support : SupportedOnCycle cycle γ)
    (m : ℤ)
    (h_holonomy : ∑ i, γ.val i (cycle.next i) = m)
    (h_n_ge_3 : n ≥ 3) :
  norm_sq γ = (m : ℝ)^2 / (Fintype.card (Fin n)) := by
  classical
  haveI : Inhabited (Fin n) := ⟨0, Nat.zero_lt_of_lt (by omega : 0 < n)⟩
  obtain ⟨k, h_const⟩ := harmonic_constant_on_simple_cycle cycle γ h_harm h_support
  have h_k_eq : k = m / (Fintype.card (Fin n)) := by
    have : ∑ i : Fin n, k = m := by
      calc ∑ i : Fin n, k
          = ∑ i : Fin n, γ.val i (cycle.next i) := Finset.sum_congr rfl (fun i _ => (h_const i).symm)
        _ = m := h_holonomy
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    have h_ne : (Fintype.card (Fin n) : ℝ) ≠ 0 := by simp
    field_simp [h_ne]
    linarith
  unfold norm_sq inner_product_C1
  have h_sum_eq : ∑ i : Fin n, ∑ j : Fin n, γ.val i j * γ.val i j =
                  (Fintype.card (Fin n)) * 2 * k^2 := by
    have h_each : ∀ i, ∑ j, γ.val i j * γ.val i j = 2 * k^2 := by
      intro i
      let s : Finset (Fin n) := {cycle.next i, cycle.prev i}
      trans (∑ j ∈ s, γ.val i j * γ.val i j)
      · symm
        refine Finset.sum_subset (Finset.subset_univ s) ?_
        intro j _ hj
        simp [s, Finset.mem_insert, Finset.mem_singleton] at hj
        push_neg at hj
        have h := h_support i j hj.1
        rw [h]
        ring
      have h_ne : cycle.prev i ≠ cycle.next i := by
        intro h_eq
        have h_period_2 : cycle.next (cycle.next i) = i := by
          calc cycle.next (cycle.next i)
              = cycle.next (cycle.prev i) := by rw [← h_eq]
            _ = i := cycle.next_prev i
        have h_exists_third : ∃ j : Fin n, j ≠ i ∧ j ≠ cycle.next i := by
          by_contra h_not
          push_neg at h_not
          have h_all : ∀ j : Fin n, j = i ∨ j = cycle.next i := fun j =>
            by_cases (fun h : j = i => Or.inl h) (fun h => Or.inr (h_not j h))
          have h_card_le : Fintype.card (Fin n) ≤ 2 := by
            classical
            have h_subset : (Finset.univ : Finset (Fin n)) ⊆ {i, cycle.next i} := by
              intro j _
              simp [h_all j]
            calc Fintype.card (Fin n)
                = Finset.univ.card := Finset.card_univ.symm
              _ ≤ ({i, cycle.next i} : Finset (Fin n)).card := Finset.card_le_card h_subset
              _ ≤ 2 := Finset.card_le_two
          have h_card_eq : Fintype.card (Fin n) = n := by convert Fintype.card_fin n
          omega
        obtain ⟨j, hj_ne_i, hj_ne_next⟩ := h_exists_third
        have := cycle.connected i j
        obtain ⟨k, hk⟩ := this
        have h_period_gen : ∀ m, cycle.next^[m] i = i ∨ cycle.next^[m] i = cycle.next i := by
          intro m
          induction m with
          | zero => left; rfl
          | succ m' ih =>
            cases ih with
            | inl h => right; simp [Function.iterate_succ_apply', h]
            | inr h => left; simp [Function.iterate_succ_apply', h, h_period_2]
        have h_periodic := h_period_gen k
        cases h_periodic with
        | inl h => rw [←hk] at hj_ne_i; exact hj_ne_i h
        | inr h => rw [←hk] at hj_ne_next; exact hj_ne_next h
      have h_next : γ.val i (cycle.next i) = k := h_const i
      have h_prev : γ.val i (cycle.prev i) = -k := by
        calc γ.val i (cycle.prev i)
            = -γ.val (cycle.prev i) i := γ.skew i (cycle.prev i)
          _ = -γ.val (cycle.prev i) (cycle.next (cycle.prev i)) := by rw [cycle.next_prev]
          _ = -k := by rw [h_const]
      calc ∑ j ∈ s, γ.val i j * γ.val i j
          = γ.val i (cycle.next i) * γ.val i (cycle.next i) +
            γ.val i (cycle.prev i) * γ.val i (cycle.prev i) := by
              simp only [s]
              rw [Finset.sum_insert (by intro h; exact h_ne.symm (Finset.mem_singleton.mp h)), Finset.sum_singleton]
        _ = k * k + (-k) * (-k) := by rw [h_next, h_prev]
        _ = 2 * k^2 := by ring
    calc ∑ i, ∑ j, γ.val i j * γ.val i j
        = ∑ i, 2 * k^2 := Finset.sum_congr rfl (fun i _ => h_each i)
      _ = (Fintype.card (Fin n)) * 2 * k^2 := by
          rw [Finset.sum_const, Finset.card_univ]; ring
  rw [h_sum_eq, h_k_eq]
  have h_ne : (Fintype.card (Fin n) : ℝ) ≠ 0 := by simp
  field_simp [h_ne]

/-- Quantized energy spectrum: winding m gives energy m²/n. -/
theorem quantized_energy_spectrum {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (cycle : SimpleCycle n) (γ : C1 n)
    (h_harm : IsHarmonic γ)
    (h_support : SupportedOnCycle cycle γ)
    (m : ℤ)
    (h_winding : holonomy γ (SimpleCycle.toChain1 cycle) = m)
    (h_n_ge_3 : n ≥ 3) :
  norm_sq γ = (m : ℝ)^2 / (Fintype.card (Fin n)) := by
  classical
  haveI : Inhabited (Fin n) := ⟨0, Nat.zero_lt_of_lt (by omega : 0 < n)⟩
  obtain ⟨k, h_const⟩ := harmonic_constant_on_simple_cycle cycle γ h_harm h_support
  have h_k : k = m / (Fintype.card (Fin n)) := topological_quantization cycle γ k h_const m h_winding
  have h_K : ∑ i, γ.val i (cycle.next i) = m := by
    calc ∑ i, γ.val i (cycle.next i)
        = ∑ i, k := Finset.sum_congr rfl (fun i _ => h_const i)
      _ = (Fintype.card (Fin n) : ℝ) * k := by rw [Finset.sum_const, Finset.card_univ]; ring
      _ = (Fintype.card (Fin n) : ℝ) * (m / (Fintype.card (Fin n))) := by rw [h_k]
      _ = m := by
        have h_ne : (Fintype.card (Fin n) : ℝ) ≠ 0 := by simp
        field_simp [h_ne]
  rw [cycle_creates_holonomy_cost cycle γ h_harm h_support m h_K h_n_ge_3]

end Diaspora.Hodge
