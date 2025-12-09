/-
# Hodge Decomposition

Every constraint field σ decomposes uniquely into:
1. A Gradient dϕ
2. A Harmonic form γ
-/

import Diaspora.Core.Calculus
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
import Mathlib.LinearAlgebra.Dimension.Finrank

open BigOperators Diaspora.Core

namespace Diaspora.Hodge

/-! ## 1. The Geometry of Active Forms -/

section GraphAware

variable {n : ℕ} [Fintype (Fin n)] (G : DynamicGraph n)

/-- ActiveForm G is finite-dimensional (subtype of finite product type). -/
noncomputable instance activeFormFiniteDimensional : FiniteDimensional ℝ (ActiveForm G) := by
  haveI : Finite (Fin n × Fin n) := inferInstance
  haveI : FiniteDimensional ℝ (Fin n × Fin n → ℝ) := inferInstance
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

/-- ActiveForm G is complete (finite-dimensional inner product spaces are complete) -/
noncomputable instance activeFormCompleteSpace : CompleteSpace (ActiveForm G) :=
  FiniteDimensional.complete ℝ (ActiveForm G)

/-! ## 2. The Gradient (Fluctuation) Subspace -/

/-- The graph gradient as a linear map: Potentials → ActiveForms -/
noncomputable def d_G_linear : (Fin n → ℝ) →ₗ[ℝ] ActiveForm G where
  toFun := d_G G
  map_add' := by
    intro φ ψ
    ext i j
    show (d_G G (φ + ψ)).val.val i j = (d_G G φ + d_G G ψ).val.val i j
    change (if (i, j) ∈ G.active_edges then (φ + ψ) j - (φ + ψ) i else 0) =
           (if (i, j) ∈ G.active_edges then φ j - φ i else 0) +
           (if (i, j) ∈ G.active_edges then ψ j - ψ i else 0)
    by_cases h : (i, j) ∈ G.active_edges <;> simp [h, Pi.add_apply]
    ring
  map_smul' := by
    intro r φ
    ext i j
    show (d_G G (r • φ)).val.val i j = (r • d_G G φ).val.val i j
    change (if (i, j) ∈ G.active_edges then (r • φ) j - (r • φ) i else 0) =
           r * (if (i, j) ∈ G.active_edges then φ j - φ i else 0)
    by_cases h : (i, j) ∈ G.active_edges <;> simp [h, Pi.smul_apply, smul_eq_mul]
    ring

/-- The subspace of Exact Forms. -/
noncomputable def ImGradient : Submodule ℝ (ActiveForm G) :=
  LinearMap.range (d_G_linear G)

noncomputable instance gradientFiniteDimensional : FiniteDimensional ℝ (ImGradient G) :=
  FiniteDimensional.finiteDimensional_submodule (ImGradient G)

noncomputable instance gradientCompleteSpace : CompleteSpace (ImGradient G) :=
  FiniteDimensional.complete ℝ (ImGradient G)

noncomputable instance gradientHasOrthogonalProjection : (ImGradient G).HasOrthogonalProjection :=
  @Submodule.HasOrthogonalProjection.ofCompleteSpace ℝ (ActiveForm G) _ _ _ (ImGradient G) _

/-! ## 3. The Harmonic (Structural) Subspace -/

/-- The orthogonal complement of the Gradient. -/
noncomputable def HarmonicSubspace : Submodule ℝ (ActiveForm G) :=
  (ImGradient G)ᗮ

/-- The projector onto the harmonic subspace. -/
noncomputable def harmonic_projector : ActiveForm G →L[ℝ] HarmonicSubspace G :=
  (ImGradient G)ᗮ.orthogonalProjection

/-! ## 4. The Decomposition Theorem -/

/-- Every active form splits uniquely into a gradient part and a harmonic part. -/
theorem hodge_decomposition_graph (σ : ActiveForm G) :
  ∃ (φ : C0 n) (γ : ActiveForm G),
    σ = d_G G φ + γ ∧
    γ ∈ HarmonicSubspace G ∧
    Diaspora.Core.ActiveForm.inner (d_G G φ) γ = 0 := by
  let γ_sub := harmonic_projector G σ
  let exact_sub := (ImGradient G).orthogonalProjection σ
  have h_sum : (exact_sub : ActiveForm G) + (γ_sub : ActiveForm G) = σ :=
    Submodule.starProjection_add_starProjection_orthogonal σ
  have h_exact_in_range : (exact_sub : ActiveForm G) ∈ ImGradient G := exact_sub.2
  unfold ImGradient at h_exact_in_range
  rw [LinearMap.mem_range] at h_exact_in_range
  obtain ⟨φ, h_phi⟩ := h_exact_in_range
  refine ⟨φ, γ_sub, ?_, γ_sub.2, ?_⟩
  · rw [← h_sum]; congr 1; exact h_phi.symm
  · have h_eq : d_G G φ = d_G_linear G φ := rfl
    rw [h_eq, h_phi]
    exact Submodule.inner_right_of_mem_orthogonal exact_sub.2 γ_sub.2

end GraphAware

/-! ## 5. Algebraic Topology Connection (Betti Numbers) -/

section TopologicalDimension

variable {n : ℕ} [Fintype (Fin n)] (G : DynamicGraph n)

omit [Fintype (Fin n)] in
/--
Active edges form a symmetric set (by DynamicGraph.symmetric)
with no loops (by DynamicGraph.no_loops).
Therefore the swap involution (i,j) ↔ (j,i) partitions active_edges into pairs,
giving even cardinality.
-/
lemma active_edges_even_card : Even G.active_edges.card := by
  let undirected_edges := G.active_edges.filter (fun (i, j) => i < j)

  have h_card : G.active_edges.card = 2 * undirected_edges.card := by
    have h_partition : G.active_edges =
      undirected_edges ∪ (undirected_edges.image (fun (i, j) => (j, i))) := by
      ext ⟨i, j⟩
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image, undirected_edges]
      constructor
      · intro h_mem
        by_cases h : i < j
        · left; exact ⟨h_mem, h⟩
        · right
          have h_neq : i ≠ j := by
            intro heq; subst heq
            exact G.no_loops i h_mem
          have h_ji : j < i := by omega
          refine ⟨(j, i), ⟨G.symmetric j i |>.mpr h_mem, h_ji⟩, rfl⟩
      · intro h_or
        cases h_or with
        | inl h_left => exact h_left.1
        | inr h_right =>
          obtain ⟨⟨k, l⟩, ⟨h_kl_mem, h_lt⟩, h_eq⟩ := h_right
          cases h_eq
          exact G.symmetric k l |>.mp h_kl_mem

    have h_disj : Disjoint undirected_edges (undirected_edges.image (fun (i, j) => (j, i))) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      ext ⟨i, j⟩
      simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and, undirected_edges]
      intro h_mem
      simp only [Finset.mem_filter, Finset.mem_image] at h_mem ⊢
      intro ⟨⟨k, l⟩, ⟨h_kl_mem, h_lt_kl⟩, h_eq⟩
      cases h_eq
      omega

    have h_image_card : (undirected_edges.image (fun (i, j) => (j, i))).card = undirected_edges.card := by
      apply Finset.card_image_of_injective
      intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
      cases h
      rfl

    rw [h_partition, Finset.card_union_of_disjoint h_disj, h_image_card]
    ring

  exact ⟨undirected_edges.card, by omega⟩

/-- The dimension of ActiveForm G equals the number of undirected edges. -/
lemma active_form_dimension [DecidableEq (Fin n)] :
    Module.finrank ℝ (ActiveForm G) = G.active_edges.card / 2 := by
  have h_even := active_edges_even_card G
  let undirected := G.active_edges.filter (fun (i, j) => i < j)
  let e : undirected → ActiveForm G := fun ⟨(i, j), h_mem⟩ =>
    ⟨{ val := fun k l =>
        if (k, l) = (i, j) then 1
        else if (k, l) = (j, i) then -1
        else 0,
       skew := by
         intro k l
         have h_lt : i < j := (Finset.mem_filter.mp h_mem).2
         split_ifs <;> simp only [Prod.mk.injEq, not_and] at * <;> first | omega | norm_num },
     by
       intro k l h_not_active
       simp only
       split_ifs with h1 h2
       · cases h1
         have : (i, j) ∈ G.active_edges := (Finset.mem_filter.mp h_mem).1
         contradiction
       · cases h2
         have : (j, i) ∈ G.active_edges := G.symmetric i j |>.mp (Finset.mem_filter.mp h_mem).1
         contradiction
       · rfl⟩

  have h_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff]
    intro l h_sum
    ext x
    obtain ⟨y, h_y⟩ := x
    obtain ⟨i, j⟩ := y
    show l ⟨(i, j), h_y⟩ = 0
    simp [Finsupp.linearCombination_apply] at h_sum
    have h_eval : ∑ x ∈ l.support, (l x • e x).val.val i j = 0 := by
      have h_extract : (∑ x ∈ l.support, l x • e x).val.val i j = ∑ x ∈ l.support, (l x • e x).val.val i j := by
        let extract_ij : ActiveForm G →+ ℝ := { toFun := fun σ => σ.val.val i j, map_zero' := rfl, map_add' := fun _ _ => rfl }
        exact map_sum extract_ij _ _
      rw [← h_extract]
      convert congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_sum)) i j
    have h_basis_val : (l ⟨(i, j), h_y⟩ • e ⟨(i, j), h_y⟩).val.val i j = l ⟨(i, j), h_y⟩ := by
      simp only [e, HSMul.hSMul, SMul.smul]; norm_num
    rw [Finset.sum_eq_single ⟨(i, j), h_y⟩] at h_eval
    · rw [h_basis_val] at h_eval; exact h_eval
    · intro b h_b_mem h_b_ne
      obtain ⟨⟨k, m⟩, h_km⟩ := b
      have h_neq : (i, j) ≠ (k, m) := fun h => h_b_ne (by cases h; rfl)
      have h_neq_swap : (i, j) ≠ (m, k) := by
        have h_ij_lt : i < j := (Finset.mem_filter.mp h_y).2
        have h_km_lt : k < m := (Finset.mem_filter.mp h_km).2
        intro heq; cases heq; omega
      simp only [e, HSMul.hSMul, SMul.smul]
      simp [h_neq, h_neq_swap]
    · intro h
      have : l ⟨(i, j), h_y⟩ = 0 := Finsupp.notMem_support_iff.mp h
      simp [this, e, HSMul.hSMul, SMul.smul]

  have h_span : Submodule.span ℝ (Set.range e) = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    rw [Submodule.mem_span_range_iff_exists_fun]
    use fun x => match x with | ⟨(i, j), _⟩ => σ.val.val i j
    ext k m
    have h_sum_comp : (∑ x : undirected, (match x with | ⟨(i, j), _⟩ => σ.val.val i j) • e x).val.val k m =
                      ∑ x : undirected, ((match x with | ⟨(i, j), _⟩ => σ.val.val i j) • e x).val.val k m := by
      let extract_km : ActiveForm G →+ ℝ := { toFun := fun σ => σ.val.val k m, map_zero' := rfl, map_add' := fun _ _ => rfl }
      exact map_sum extract_km _ _
    rw [h_sum_comp]; symm
    by_cases h_active : (k, m) ∈ G.active_edges
    · by_cases h_order : k < m
      · have h_km_mem : (k, m) ∈ undirected := by simp [undirected]; exact ⟨h_active, h_order⟩
        rw [Fintype.sum_eq_single ⟨(k, m), h_km_mem⟩]
        · simp only [e, HSMul.hSMul, SMul.smul]; norm_num
        · intro ⟨⟨i, j⟩, h_ij⟩ h_ne
          have h_neq : (k, m) ≠ (i, j) := fun h => h_ne (Subtype.eq h.symm)
          have h_neq_swap : (k, m) ≠ (j, i) := by
            have h_ij_lt : i < j := (Finset.mem_filter.mp h_ij).2
            intro heq; cases heq; omega
          simp only [e, HSMul.hSMul, SMul.smul, h_neq, h_neq_swap, ↓reduceIte, mul_zero]
      · have h_neq_km : k ≠ m := by intro h; cases h; exact G.no_loops k h_active
        have h_mk_order : m < k := by omega
        have h_mk_active : (m, k) ∈ G.active_edges := G.symmetric k m |>.mp h_active
        have h_mk_mem : (m, k) ∈ undirected := by simp [undirected]; exact ⟨h_mk_active, h_mk_order⟩
        rw [Fintype.sum_eq_single ⟨(m, k), h_mk_mem⟩]
        · simp only [e, HSMul.hSMul, SMul.smul, Prod.mk.injEq, h_neq_km, Ne.symm h_neq_km,
            and_self, ↓reduceIte, mul_neg, mul_one, σ.val.skew m k, neg_neg]
        · intro ⟨⟨i, j⟩, h_ij⟩ h_ne
          have h_neq_mk : (m, k) ≠ (i, j) := fun h => h_ne (Subtype.eq h.symm)
          have h_neq_mk_swap : (m, k) ≠ (j, i) := by
            have h_ij_lt : i < j := (Finset.mem_filter.mp h_ij).2
            intro heq; cases heq; omega
          have h_neq_km : (k, m) ≠ (i, j) := by
            have h_ij_lt : i < j := (Finset.mem_filter.mp h_ij).2
            intro heq; cases heq; omega
          have h_neq_km_swap : (k, m) ≠ (j, i) := by
            intro heq; cases heq; exact h_neq_mk rfl
          simp only [e, HSMul.hSMul, SMul.smul, h_neq_km, h_neq_km_swap, ↓reduceIte, mul_zero]
    · have h_zero : σ.val.val k m = 0 := σ.2 k m h_active
      rw [h_zero]; symm
      apply Fintype.sum_eq_zero
      intro ⟨⟨i, j⟩, h_ij⟩
      have h_neq : (k, m) ≠ (i, j) := by
        intro heq; cases heq; exact h_active (Finset.mem_filter.mp h_ij).1
      have h_neq_swap : (k, m) ≠ (j, i) := by
        have h_ij_active : (i, j) ∈ G.active_edges := (Finset.mem_filter.mp h_ij).1
        intro heq; cases heq; exact h_active (G.symmetric m k |>.mp h_ij_active)
      simp only [e, HSMul.hSMul, SMul.smul, h_neq, h_neq_swap, ↓reduceIte, mul_zero]

  have h_basis := Module.Basis.mk h_li (le_of_eq h_span.symm)
  have h_finrank : Module.finrank ℝ (ActiveForm G) = Fintype.card undirected :=
    Module.finrank_eq_card_basis h_basis
  have h_card : Fintype.card undirected = undirected.card := Fintype.card_coe _
  rw [h_finrank, h_card]
  have : G.active_edges.card = 2 * undirected.card := by
    have h_partition : G.active_edges =
      undirected ∪ (undirected.image (fun (i, j) => (j, i))) := by
      ext ⟨i, j⟩
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image, undirected]
      constructor
      · intro h_mem
        by_cases h : i < j
        · left; exact ⟨h_mem, h⟩
        · right
          have h_neq : i ≠ j := by intro heq; subst heq; exact G.no_loops i h_mem
          have h_ji : j < i := by omega
          refine ⟨(j, i), ⟨G.symmetric j i |>.mpr h_mem, h_ji⟩, rfl⟩
      · intro h_or
        cases h_or with
        | inl h => exact h.1
        | inr h => obtain ⟨⟨k, l⟩, ⟨h_kl, _⟩, h_eq⟩ := h; cases h_eq; exact G.symmetric k l |>.mp h_kl
    have h_disj : Disjoint undirected (undirected.image (fun (i, j) => (j, i))) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      ext ⟨i, j⟩
      simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and, undirected]
      intro h_mem
      simp only [Finset.mem_filter, Finset.mem_image] at h_mem ⊢
      intro ⟨⟨k, l⟩, ⟨h_kl, h_lt_kl⟩, h_eq⟩
      cases h_eq; omega
    have h_image : (undirected.image (fun (i, j) => (j, i))).card = undirected.card := by
      apply Finset.card_image_of_injective
      intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
      cases h; rfl
    rw [h_partition, Finset.card_union_of_disjoint h_disj, h_image]; ring
  omega

/--
Rank-Nullity for Graphs (additive form): dim(H1) + |V| = |E| + dim(Ker d).
-/
theorem harmonic_dimension_eq_cyclomatic
    [DecidableEq (Fin n)]
    : Module.finrank ℝ (HarmonicSubspace G) + n =
      (G.active_edges.card / 2) + (Module.finrank ℝ (LinearMap.ker (d_G_linear G))) := by
  have h_orth : IsCompl (ImGradient G) (HarmonicSubspace G) :=
    Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
  have h_dim_split := Submodule.finrank_add_eq_of_isCompl h_orth
  have h_rank_nullity := LinearMap.finrank_range_add_finrank_ker (d_G_linear G)
  have h_domain_dim : Module.finrank ℝ (Fin n → ℝ) = n := by simp only [Module.finrank_fin_fun]
  rw [h_domain_dim] at h_rank_nullity
  have h_active_dim := active_form_dimension G
  rw [h_active_dim] at h_dim_split
  rw [← ImGradient] at h_rank_nullity
  omega 

end TopologicalDimension

/-! ## 6. Complete Graph Specialization -/

section CompleteGraph

variable {n : ℕ} [Fintype (Fin n)]

lemma IsHarmonic_iff_divergence_zero (σ : C1 n) :
  IsHarmonic σ ↔ divergence σ = (fun _ => 0 : C0 n) := by
  unfold IsHarmonic divergence
  apply Iff.intro
  · intro h; funext i; simp [h i]
  · intro h i
    have := congr_fun h i
    simp at this
    linarith

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
  ext i j
  simp [ActiveForm_to_C1, C1_to_ActiveForm]

omit [Fintype (Fin n)] in
lemma d0_eq_d_G_complete (φ : C0 n) :
    ActiveForm_to_C1 (d_G (DynamicGraph.complete n) φ) = d0 φ := by
  ext i j
  simp [ActiveForm_to_C1, d_G, d0, DynamicGraph.complete]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

lemma inner_C1_ActiveForm (σ τ : C1 n) : 
    inner_product_C1 σ τ = Diaspora.Core.ActiveForm.inner (C1_to_ActiveForm σ) (C1_to_ActiveForm τ) := rfl

/--
The Classical Hodge Decomposition (for the complete graph).
This is the version used by most legacy files, now proved via the general graph theory.
-/
theorem hodge_decomposition {n : ℕ} [Fintype (Fin n)] (σ : C1 n) :
  ∃ (ϕ : C0 n) (γ : C1 n),
    (∀ i j, σ.val i j = (d0 ϕ).val i j + γ.val i j) ∧
    IsHarmonic γ ∧
    inner_product_C1 (d0 ϕ) γ = 0 := by
  let σ_act := C1_to_ActiveForm σ
  obtain ⟨ϕ, γ_act, h_eq, h_harm_sub, h_orth⟩ := hodge_decomposition_graph (DynamicGraph.complete n) σ_act
  let γ := ActiveForm_to_C1 γ_act
  use ϕ, γ
  constructor
  · intro i j
    have h_sigma : σ.val i j = σ_act.val.val i j := rfl
    have h_decomp : σ_act.val.val i j = (d_G (DynamicGraph.complete n) ϕ + γ_act).val.val i j :=
      congr_arg (fun x => x.val.val i j) h_eq
    have h_add : (d_G (DynamicGraph.complete n) ϕ + γ_act).val.val i j =
                 (d_G (DynamicGraph.complete n) ϕ).val.val i j + γ_act.val.val i j := rfl
    rw [h_sigma, h_decomp, h_add]
    have h_d0_full := d0_eq_d_G_complete ϕ
    have h_d0 : (d_G (DynamicGraph.complete n) ϕ).val.val i j = (d0 ϕ).val i j := by
      have := congr_arg (fun (x : C1 n) => x.val i j) h_d0_full
      exact this
    rw [h_d0]
    rfl
  
  constructor
  · intro i
    simp [γ, ActiveForm_to_C1]
    have h_orth_all : ∀ φ' : C0 n, Diaspora.Core.ActiveForm.inner (d_G (DynamicGraph.complete n) φ') γ_act = 0 := by
      intro φ'
      rw [HarmonicSubspace, Submodule.mem_orthogonal] at h_harm_sub
      apply h_harm_sub
      show d_G (DynamicGraph.complete n) φ' ∈ LinearMap.range (d_G_linear (DynamicGraph.complete n))
      exact ⟨φ', rfl⟩
    show δ_G (DynamicGraph.complete n) γ_act i = 0
    have h_adj : (basis_vector i) i * divergence γ i = 0 := by
      calc (basis_vector i) i * divergence γ i
          = ∑ j, (basis_vector i) j * divergence γ j := by
              rw [Finset.sum_eq_single i]
              · intro b _ hb; simp [basis_vector, hb]
              · intro h; exact absurd (Finset.mem_univ i) h
        _ = inner_product_C1 (d0 (basis_vector i)) γ := (divergence_is_adjoint _ _).symm
        _ = inner_product_C1 (ActiveForm_to_C1 (d_G (DynamicGraph.complete n) (basis_vector i)))
                             (ActiveForm_to_C1 γ_act) := by rw [← d0_eq_d_G_complete]
        _ = Diaspora.Core.ActiveForm.inner (d_G (DynamicGraph.complete n) (basis_vector i)) γ_act := rfl
        _ = 0 := h_orth_all (basis_vector i)
    have h_div_neg : divergence γ i = - δ_G (DynamicGraph.complete n) γ_act i := by
      unfold divergence δ_G γ ActiveForm_to_C1; ring
    simp [basis_vector] at h_adj
    linarith

  · rw [inner_C1_ActiveForm]
    rw [← d0_eq_d_G_complete]
    exact h_orth

end CompleteGraph

/-! ## 7. Supporting Lemmas -/

lemma inner_product_C1_comm {n : ℕ} [Fintype (Fin n)] (σ τ : C1 n) :
  inner_product_C1 σ τ = inner_product_C1 τ σ := by
  unfold inner_product_C1
  congr 1
  congr 1
  ext i
  congr 1
  ext j
  ring


lemma d0_add {n : ℕ} (ϕ ψ : C0 n) :
  ∀ i j, (d0 (fun i => ϕ i + ψ i)).val i j = (d0 ϕ).val i j + (d0 ψ).val i j := by
  intro i j
  simp [d0]
  ring

lemma d0_smul {n : ℕ} (c : ℝ) (ϕ : C0 n) :
  ∀ i j, (d0 (fun i => c * ϕ i)).val i j = c * (d0 ϕ).val i j := by
  intro i j
  simp [d0]
  ring

lemma norm_sq_add {n : ℕ} [Fintype (Fin n)] (A B : C1 n) :
  norm_sq { val := fun i j => A.val i j + B.val i j,
            skew := by intro i j; rw [A.skew, B.skew]; ring } =
  norm_sq A + 2 * inner_product_C1 A B + norm_sq B := by
  unfold norm_sq inner_product_C1
  simp only [Finset.sum_add_distrib, mul_add, add_mul]
  have h_comm : ∀ i j, B.val i j * A.val i j = A.val i j * B.val i j := fun i j => mul_comm _ _
  simp only [h_comm]
  ring_nf

lemma laplacian_expansion {n : ℕ} [Fintype (Fin n)] (ϕ : C0 n) (i : Fin n) :
  graph_laplacian ϕ i = - ∑ j : Fin n, (ϕ j - ϕ i) := by
  unfold graph_laplacian divergence d0
  rfl

end Diaspora.Hodge
