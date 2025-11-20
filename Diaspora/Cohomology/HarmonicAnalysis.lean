/-
# Harmonic Analysis

Algebraic consequences of the Hodge decomposition: physical theorems about
minimization, linearity, orthogonality, holonomy, and spectral properties.

These are the "Lego blocks" of the physical theory.
-/

import Diaspora.Cohomology.HodgeDecomposition
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open BigOperators Complex

namespace DiscreteHodge

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
  norm_sq (residual ϕ σ) =
    (1/2) * ∑ i, ∑ j, ((ϕ j - ϕ i) - σ.val i j)^2 := by
  simpa [residual] using V_int_is_cohomological_distance (n:=n) ϕ σ

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

end DiscreteHodge
