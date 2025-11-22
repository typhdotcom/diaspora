/-
# Hodge Decomposition

The core decomposition theorem: every 1-cochain σ splits uniquely as σ = dϕ + γ
where dϕ is exact and γ is harmonic, with dϕ ⊥ γ.

This file contains the heavy functional analysis proofs. Downstream files import
only the theorem statements, not the proof details.
-/

import Diaspora.DiscreteCalculus
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

open BigOperators

namespace DiscreteHodge

/-! ## Graph-Aware Hodge Theory -/

section GraphAware

variable {n : ℕ} [Fintype (Fin n)] (G : DynamicGraph n)

-- ActiveForm G is finite-dimensional (subtype of finite product type)
noncomputable instance activeFormFiniteDimensional : FiniteDimensional ℝ (ActiveForm G) := by
  -- We construct an injective linear map into a finite-dimensional space
  haveI : Finite (Fin n × Fin n) := inferInstance
  haveI : FiniteDimensional ℝ (Fin n × Fin n → ℝ) := inferInstance
  -- The natural embedding toC1 then into the underlying function space
  let embed : ActiveForm G →ₗ[ℝ] (Fin n × Fin n → ℝ) := {
    toFun := fun σ => fun (i, j) => σ.val.val i j,
    map_add' := by intro σ τ; ext ⟨i, j⟩; rfl,
    map_smul' := by intro r σ; ext ⟨i, j⟩; rfl
  }
  apply FiniteDimensional.of_injective embed
  intro σ τ h
  ext i j
  have : (fun (p : Fin n × Fin n) => σ.val.val p.1 p.2) = (fun (p : Fin n × Fin n) => τ.val.val p.1 p.2) := h
  exact congr_fun this (i, j)

-- ActiveForm G is complete (finite-dimensional inner product spaces are complete)
noncomputable instance activeFormCompleteSpace : CompleteSpace (ActiveForm G) :=
  FiniteDimensional.complete ℝ (ActiveForm G)


/-- The graph gradient as a linear map -/
noncomputable def d_G_linear : (Fin n → ℝ) →ₗ[ℝ] ActiveForm G where
  toFun := d_G G
  map_add' := by
    intro φ ψ
    ext i j
    show (d_G G (φ + ψ)).val.val i j = (d_G G φ + d_G G ψ).val.val i j
    -- RHS unfolds to (d_G G φ).val.val i j + (d_G G ψ).val.val i j
    change (if (i, j) ∈ G.active_edges then (φ + ψ) j - (φ + ψ) i else 0) =
           (if (i, j) ∈ G.active_edges then φ j - φ i else 0) +
           (if (i, j) ∈ G.active_edges then ψ j - ψ i else 0)
    by_cases h : (i, j) ∈ G.active_edges <;> simp [h, Pi.add_apply]
    ring
  map_smul' := by
    intro r φ
    ext i j
    show (d_G G (r • φ)).val.val i j = (r • d_G G φ).val.val i j
    -- RHS unfolds to r * (d_G G φ).val.val i j
    change (if (i, j) ∈ G.active_edges then (r • φ) j - (r • φ) i else 0) =
           r * (if (i, j) ∈ G.active_edges then φ j - φ i else 0)
    by_cases h : (i, j) ∈ G.active_edges <;> simp [h, Pi.smul_apply, smul_eq_mul]
    ring

/-- The image of the gradient operator (exact forms on the graph) -/
noncomputable def ImGradient : Submodule ℝ (ActiveForm G) :=
  LinearMap.range (d_G_linear G)

-- The gradient submodule is finite-dimensional (submodule of finite-dimensional space)
noncomputable instance gradientFiniteDimensional : FiniteDimensional ℝ (ImGradient G) :=
  FiniteDimensional.finiteDimensional_submodule (ImGradient G)

-- The gradient submodule is complete (finite-dimensional subspaces are complete)
noncomputable instance gradientCompleteSpace : CompleteSpace (ImGradient G) :=
  FiniteDimensional.complete ℝ (ImGradient G)

-- The gradient submodule has orthogonal projection
noncomputable instance gradientHasOrthogonalProjection : (ImGradient G).HasOrthogonalProjection :=
  @Submodule.HasOrthogonalProjection.ofCompleteSpace ℝ (ActiveForm G) _ _ _ (ImGradient G) _

/--
The new Hodge decomposition using orthogonal projection.
Every active form σ decomposes uniquely into a gradient part and an orthogonal harmonic part.
-/
theorem hodge_decomposition_graph (σ : ActiveForm G) :
  ∃ (φ : C0 n) (γ : ActiveForm G),
    σ = d_G G φ + γ ∧
    γ ∈ (ImGradient G)ᗮ ∧
    ActiveForm.inner (d_G G φ) γ = 0 := by
  -- Use orthogonal projection onto the gradient subspace
  let dφ := (ImGradient G).orthogonalProjection σ
  -- The harmonic part is the orthogonal complement
  let γ := σ - dφ

  -- The exact part is in the image of d_G, so there exists φ
  have ⟨φ, h_φ⟩ : ∃ φ, d_G G φ = dφ := by
    have : (dφ : ActiveForm G) ∈ ImGradient G := Submodule.coe_mem dφ
    unfold ImGradient at this
    exact this

  use φ, γ
  constructor
  · -- σ = dφ + γ by definition of γ
    unfold γ
    rw [h_φ]
    abel
  constructor
  · -- γ is orthogonal to ImGradient
    unfold γ
    -- σ - ↑dφ is in the orthogonal complement by construction
    have h_star_eq : (ImGradient G).starProjection σ = ↑dφ := Submodule.starProjection_apply _ _
    rw [←h_star_eq]
    -- The orthogonal projection onto Kᗮ is exactly σ - K.starProjection σ
    exact Submodule.sub_starProjection_mem_orthogonal σ
  · -- Orthogonality of dφ and γ
    rw [h_φ]
    unfold γ
    -- Use that if x ∈ K and y ∈ Kᗮ, then inner x y = 0
    have h_mem_K : (↑dφ : ActiveForm G) ∈ ImGradient G := Submodule.coe_mem dφ
    have h_star_eq : (ImGradient G).starProjection σ = ↑dφ := Submodule.starProjection_apply _ _
    rw [←h_star_eq]
    have h_mem_Kperp := Submodule.sub_starProjection_mem_orthogonal σ (K := ImGradient G)
    rw [Submodule.mem_orthogonal] at h_mem_Kperp
    exact h_mem_Kperp _ h_mem_K

end GraphAware

/-! ## Complete Graph Specialization -/

section CompleteGraph

variable {n : ℕ} [Fintype (Fin n)]

/-- Embed C1 n into ActiveForm (complete graph) -/
noncomputable def C1_to_ActiveForm (σ : C1 n) : ActiveForm (DynamicGraph.complete n) :=
  ⟨σ, by intro i j h; simp [DynamicGraph.complete] at h; subst h; have := σ.skew i i; linarith⟩

/-- Extract C1 from ActiveForm (complete graph) -/
noncomputable def ActiveForm_to_C1 (σ : ActiveForm (DynamicGraph.complete n)) : C1 n :=
  σ.val

omit [Fintype (Fin n)] in
lemma C1_ActiveForm_equiv (σ : C1 n) :
    ActiveForm_to_C1 (C1_to_ActiveForm σ) = σ := rfl

omit [Fintype (Fin n)] in
lemma ActiveForm_C1_equiv (σ : ActiveForm (DynamicGraph.complete n)) :
    C1_to_ActiveForm (ActiveForm_to_C1 σ) = σ := by
  ext i j; rfl

omit [Fintype (Fin n)] in
lemma d0_eq_d_G_complete (φ : C0 n) :
    ActiveForm_to_C1 (d_G (DynamicGraph.complete n) φ) = d0 φ := by
  ext i j
  simp [d_G, DynamicGraph.complete, d0, ActiveForm_to_C1]
  by_cases h : i = j
  · simp [h]
  · simp [h]

/-- Inner products agree -/
lemma inner_C1_ActiveForm (σ τ : C1 n) :
    inner_product_C1 σ τ = ActiveForm.inner (C1_to_ActiveForm σ) (C1_to_ActiveForm τ) := by
  rfl

end CompleteGraph

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

/-! ## Main Theorems -/

/--
Hodge decomposition for the complete graph case.
Uses the graph-aware machinery specialized to DynamicGraph.complete.
-/
theorem hodge_decomposition {n : ℕ} [Fintype (Fin n)] (σ : C1 n) :
  ∃ (ϕ : C0 n) (γ : C1 n),
    (∀ i j, σ.val i j = (d0 ϕ).val i j + γ.val i j) ∧
    IsHarmonic γ ∧
    inner_product_C1 (d0 ϕ) γ = 0 := by
  -- Use the graph-aware decomposition on the complete graph
  let σ_active := C1_to_ActiveForm σ
  obtain ⟨φ, γ_active, h_decomp, h_orth_submod, h_orth_inner⟩ :=
    hodge_decomposition_graph (DynamicGraph.complete n) σ_active

  -- Convert back to C1 n
  let γ := ActiveForm_to_C1 γ_active
  use φ, γ

  constructor
  · -- Decomposition σ = d0 φ + γ
    intro i j
    have h_eq : σ_active.val.val i j = (d_G (DynamicGraph.complete n) φ + γ_active).val.val i j := by
      rw [h_decomp]
    simp [σ_active, C1_to_ActiveForm] at h_eq
    calc σ.val i j
        = (d_G (DynamicGraph.complete n) φ).val.val i j + γ_active.val.val i j := h_eq
      _ = (ActiveForm_to_C1 (d_G (DynamicGraph.complete n) φ)).val i j + γ.val i j := rfl
      _ = (d0 φ).val i j + γ.val i j := by rw [d0_eq_d_G_complete]

  constructor
  · -- γ is harmonic (divergence-free)
    intro i
    simp [γ, ActiveForm_to_C1]
    -- γ_active ⊥ ImGradient means ⟨d_G φ', γ_active⟩ = 0 for all φ'
    have h_orth_all : ∀ φ' : C0 n, ActiveForm.inner (d_G (DynamicGraph.complete n) φ') γ_active = 0 := by
      intro φ'
      rw [Submodule.mem_orthogonal] at h_orth_submod
      apply h_orth_submod
      show d_G (DynamicGraph.complete n) φ' ∈ LinearMap.range (d_G_linear (DynamicGraph.complete n))
      exact ⟨φ', rfl⟩
    -- The sum equals δ_G on the complete graph
    show δ_G (DynamicGraph.complete n) γ_active i = 0
    -- Prove via adjoint: inner ⟨d_G φ', γ⟩ = φ'ᵢ * divergence γ ᵢ = -φ'ᵢ * δ_G γ ᵢ
    have h_adj : (basis_vector i) i * divergence γ i = 0 := by
      calc (basis_vector i) i * divergence γ i
          = ∑ j, (basis_vector i) j * divergence γ j := by
              rw [Finset.sum_eq_single i]
              · intro b _ hb; simp [basis_vector, hb]
              · intro h; exact absurd (Finset.mem_univ i) h
        _ = inner_product_C1 (d0 (basis_vector i)) γ := (divergence_is_adjoint _ _).symm
        _ = inner_product_C1 (ActiveForm_to_C1 (d_G (DynamicGraph.complete n) (basis_vector i)))
                             (ActiveForm_to_C1 γ_active) := by rw [← d0_eq_d_G_complete]
        _ = ActiveForm.inner (d_G (DynamicGraph.complete n) (basis_vector i)) γ_active := rfl
        _ = 0 := h_orth_all (basis_vector i)
    -- divergence γ i = - δ_G γ_active i, so both must be zero
    have h_div_neg : divergence γ i = - δ_G (DynamicGraph.complete n) γ_active i := by
      unfold divergence δ_G γ ActiveForm_to_C1; ring
    simp [basis_vector] at h_adj
    linarith

  · -- Orthogonality
    calc inner_product_C1 (d0 φ) γ
        = inner_product_C1 (ActiveForm_to_C1 (d_G (DynamicGraph.complete n) φ)) (ActiveForm_to_C1 γ_active) := by rw [d0_eq_d_G_complete]
      _ = ActiveForm.inner (C1_to_ActiveForm (ActiveForm_to_C1 (d_G (DynamicGraph.complete n) φ)))
                           (C1_to_ActiveForm (ActiveForm_to_C1 γ_active)) := by rw [inner_C1_ActiveForm]
      _ = ActiveForm.inner (d_G (DynamicGraph.complete n) φ) γ_active := by simp [ActiveForm_C1_equiv]
      _ = 0 := h_orth_inner

end DiscreteHodge
