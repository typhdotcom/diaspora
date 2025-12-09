import Diaspora.Hodge.Decomposition
import Diaspora.Dynamics.Plasticity
import Diaspora.Core.Weighted
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

open BigOperators Matrix Diaspora.Core Diaspora.Hodge Diaspora.Dynamics

namespace Diaspora.Models

/-- Graph Laplacian: L_ii = degree(i), L_ij = -1 if (i,j) active. -/
noncomputable def laplacianMatrix {n : ℕ} (G : DynamicGraph n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    if i = j then
      (Finset.univ.filter (fun k => (i, k) ∈ G.active_edges)).card
    else if (i, j) ∈ G.active_edges then
      -1
    else
      0

lemma laplacianMatrix_isSymm {n : ℕ} (G : DynamicGraph n) : (laplacianMatrix G).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  unfold laplacianMatrix
  by_cases hij : i = j
  · simp [hij]
  · have hji : j ≠ i := Ne.symm hij
    simp only [hij, hji, ↓reduceIte]
    by_cases h : (i, j) ∈ G.active_edges
    · have : (j, i) ∈ G.active_edges := G.symmetric i j |>.mp h
      simp [h, this]
    · have : (j, i) ∉ G.active_edges := fun hc => h (G.symmetric j i |>.mp hc)
      simp [h, this]

lemma isSymm_isHermitian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h : A.IsSymm) : A.IsHermitian :=
  h

/-- Eigenvalues of the graph Laplacian. -/
noncomputable def graphSpectrum {n : ℕ} (G : DynamicGraph n) : Multiset ℝ :=
  let hH : (laplacianMatrix G).IsHermitian := isSymm_isHermitian _ (laplacianMatrix_isSymm G)
  (Finset.univ : Finset (Fin n)).val.map hH.eigenvalues

/-! ## 1. Micro vs Macro States -/

structure Microstate (n : ℕ) where
  weights : WeightedGraph n
  sigma   : C1 n
  phi     : C0 n

/-- Observable state: thresholded topology + visible fields + spectrum. -/
structure Macrostate (n : ℕ) where
  topology : DynamicGraph n
  visible_sigma : ActiveForm topology
  spectrum : Multiset ℝ

/-- Project microstate to macrostate via threshold ε. -/
noncomputable def observe {n : ℕ} (S : Microstate n) (ε : ℝ) : Macrostate n :=
  let G := to_dynamic S.weights ε
  { topology := G, visible_sigma := d_G G S.phi, spectrum := graphSpectrum G }

/-! ## 2. Dimensional Analysis -/

section DimensionalAnalysis

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
variable (G : DynamicGraph n)

/-- A graph with no cycles (tree/forest): dim(Harmonic) = 0. -/
def IsVoidTopology : Prop :=
  Module.finrank ℝ (HarmonicSubspace G) = 0

/-- A graph supporting non-trivial Harmonic forms: dim(Harmonic) > 0. -/
def AllowsGenesis : Prop :=
  Module.finrank ℝ (HarmonicSubspace G) > 0

omit [DecidableEq (Fin n)] in
/-- In a tree, every constraint is exact. -/
theorem void_implies_exactness (h_void : IsVoidTopology G) (σ : ActiveForm G) :
  σ ∈ ImGradient G := by
  -- The active form space decomposes into Gradient ⊕ Harmonic
  obtain ⟨φ, γ, h_decomp, h_harm, _⟩ := hodge_decomposition_graph G σ
  
  -- If Harmonic dimension is 0, then γ must be 0
  have h_γ_zero : γ = 0 := by
    rw [IsVoidTopology] at h_void
    have h_sub : (HarmonicSubspace G) = ⊥ := Submodule.finrank_eq_zero.mp h_void
    rw [h_sub] at h_harm
    exact (Submodule.mem_bot ℝ).mp h_harm
  
  -- Therefore σ = dφ + 0 = dφ
  rw [h_decomp, h_γ_zero, add_zero]
  exact LinearMap.mem_range.mpr ⟨φ, rfl⟩

/-! ## 3. Generic Structure -/

omit [DecidableEq (Fin n)] in
/-- If dim(Harmonic) > 0, then dim(Exact) < dim(ActiveForm). -/
theorem structure_is_generic (h_genesis : AllowsGenesis G) :
  Module.finrank ℝ (ImGradient G) < Module.finrank ℝ (ActiveForm G) := by
  -- Recall the dimension split: dim(Active) = dim(Exact) + dim(Harmonic)
  have h_orth : IsCompl (ImGradient G) (HarmonicSubspace G) :=
    Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
  have h_split := Submodule.finrank_add_eq_of_isCompl h_orth

  rw [AllowsGenesis] at h_genesis

  -- If dim(Harmonic) > 0, then dim(Exact) + dim(Harmonic) > dim(Exact)
  omega

end DimensionalAnalysis

/-! ## 4. Cyclomatic Condition -/

/-- The graph has at least one edge more than a spanning tree. -/
def HasObserver {n : ℕ} (G : DynamicGraph n) : Prop :=
  G.active_edges.card / 2 ≥ n 

/-- If |E| ≥ |V| and graph is connected, then dim(Harmonic) ≥ 1. -/
theorem observer_creates_mass {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
    (G : DynamicGraph n)
    (h_observer : HasObserver G)
    (h_connected : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1) :
    AllowsGenesis G := by
  rw [AllowsGenesis]
  -- Use the Algebraic Bridge from HodgeDecomposition
  have h_dim := harmonic_dimension_eq_cyclomatic (G := G)
  rw [h_connected] at h_dim
  rw [HasObserver] at h_observer

  -- dim(H) = |E| - |V| + 1
  -- If |E| >= |V|, then |E| - |V| >= 0, so dim(H) >= 1
  omega

/-! ## 5. Dynamics (Plasticity) -/

/-- Evolve microstate via plasticity. -/
noncomputable def evolve_micro {n : ℕ} (S : Microstate n) (η : ℝ)
    (h_eta : η ≥ 0)
    (h_total : ∑ x, ∑ y, (S.weights.weights x y + η * raw_strain S.phi S.sigma x y) > 0) :
    Microstate n :=
  let new_weights_raw := plasticity_step S.weights S.phi S.sigma η
  let new_WG : WeightedGraph n := {
    weights := new_weights_raw,
    symmetric := plasticity_step_symm S.weights S.phi S.sigma η,
    nonneg := plasticity_step_nonneg S.weights S.phi S.sigma η h_eta h_total,
    total_capacity_fixed := by
      show ∑ i, ∑ j, plasticity_step S.weights S.phi S.sigma η i j = (n : ℝ)^2
      unfold plasticity_step
      simp only
      have h_factor : ∀ (c : ℝ) (f : Fin n → Fin n → ℝ), 
          ∑ i, ∑ j, f i j * c = (∑ i, ∑ j, f i j) * c := fun _ _ => by simp_rw [Finset.sum_mul]
      rw [h_factor]
      rw [mul_div_assoc', mul_div_cancel_left_of_imp]
      intro h; exact absurd h (ne_of_gt h_total)
  }
  { S with weights := new_WG }

-- Witness data for the theorem (top-level for unfolding)

noncomputable def void_W_val : Fin 3 → Fin 3 → ℝ := fun i j =>
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 2
  else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then 2
  else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then 1/2
  else 0

def void_sigma1_val : Fin 3 → Fin 3 → ℝ := fun i j =>
  if i = 0 ∧ j = 2 then 2
  else if i = 2 ∧ j = 0 then -2
  else 0

def void_sigma2_val : Fin 3 → Fin 3 → ℝ := fun _ _ => 0

def void_phi : C0 3 := fun _ => 0

@[simp] lemma void_W_val_00 : void_W_val 0 0 = 0 := by unfold void_W_val; simp
@[simp] lemma void_W_val_01 : void_W_val 0 1 = 2 := by unfold void_W_val; simp
@[simp] lemma void_W_val_02 : void_W_val 0 2 = 1/2 := by unfold void_W_val; simp
@[simp] lemma void_W_val_10 : void_W_val 1 0 = 2 := by unfold void_W_val; simp
@[simp] lemma void_W_val_11 : void_W_val 1 1 = 0 := by unfold void_W_val; simp
@[simp] lemma void_W_val_12 : void_W_val 1 2 = 2 := by unfold void_W_val; simp
@[simp] lemma void_W_val_20 : void_W_val 2 0 = 1/2 := by unfold void_W_val; simp
@[simp] lemma void_W_val_21 : void_W_val 2 1 = 2 := by unfold void_W_val; simp
@[simp] lemma void_W_val_22 : void_W_val 2 2 = 0 := by unfold void_W_val; simp

@[simp] lemma void_sigma1_val_00 : void_sigma1_val 0 0 = 0 := by unfold void_sigma1_val; simp
@[simp] lemma void_sigma1_val_01 : void_sigma1_val 0 1 = 0 := by unfold void_sigma1_val; simp
@[simp] lemma void_sigma1_val_02 : void_sigma1_val 0 2 = 2 := by unfold void_sigma1_val; simp
@[simp] lemma void_sigma1_val_10 : void_sigma1_val 1 0 = 0 := by unfold void_sigma1_val; simp
@[simp] lemma void_sigma1_val_11 : void_sigma1_val 1 1 = 0 := by unfold void_sigma1_val; simp
@[simp] lemma void_sigma1_val_12 : void_sigma1_val 1 2 = 0 := by unfold void_sigma1_val; simp
@[simp] lemma void_sigma1_val_20 : void_sigma1_val 2 0 = -2 := by unfold void_sigma1_val; simp
@[simp] lemma void_sigma1_val_21 : void_sigma1_val 2 1 = 0 := by unfold void_sigma1_val; simp
@[simp] lemma void_sigma1_val_22 : void_sigma1_val 2 2 = 0 := by unfold void_sigma1_val; simp

@[simp] lemma void_phi_val (i : Fin 3) : void_phi i = 0 := rfl
@[simp] lemma void_sigma2_val_eq (i j : Fin 3) : void_sigma2_val i j = 0 := rfl

/-- Same observation now, different observations after evolution. -/
theorem observable_present_undetermines_future :
    ∃ (n : ℕ) (ε η : ℝ) (S1 S2 : Microstate n)
      (h_eta : η ≥ 0)
      (h1_total : ∑ x, ∑ y, (S1.weights.weights x y + η * raw_strain S1.phi S1.sigma x y) > 0)
      (h2_total : ∑ x, ∑ y, (S2.weights.weights x y + η * raw_strain S2.phi S2.sigma x y) > 0),
    η > 0 ∧
    observe S1 ε = observe S2 ε ∧
    observe (evolve_micro S1 η h_eta h1_total) ε ≠
    observe (evolve_micro S2 η h_eta h2_total) ε := by
  use 3, 1, 1/4

  have W_symm : ∀ i j, void_W_val i j = void_W_val j i := by
    intro i j; unfold void_W_val; fin_cases i <;> fin_cases j <;> simp

  have W_nonneg : ∀ i j, 0 ≤ void_W_val i j := by
    intro i j; unfold void_W_val; fin_cases i <;> fin_cases j <;> simp

  have W_total : ∑ i, ∑ j, void_W_val i j = (3 : ℝ)^2 := by
    simp only [Fin.sum_univ_three, void_W_val_00, void_W_val_01, void_W_val_02,
               void_W_val_10, void_W_val_11, void_W_val_12,
               void_W_val_20, void_W_val_21, void_W_val_22]
    norm_num

  let W : WeightedGraph 3 := ⟨void_W_val, W_symm, W_nonneg, W_total⟩

  have sigma1_skew : ∀ i j, void_sigma1_val i j = -void_sigma1_val j i := by
    intro i j; unfold void_sigma1_val; fin_cases i <;> fin_cases j <;> simp

  let sigma1 : C1 3 := ⟨void_sigma1_val, sigma1_skew⟩

  have sigma2_skew : ∀ i j, void_sigma2_val i j = -void_sigma2_val j i := by
    intro i j; unfold void_sigma2_val; ring

  let sigma2 : C1 3 := ⟨void_sigma2_val, sigma2_skew⟩

  let S1 : Microstate 3 := ⟨W, sigma1, void_phi⟩
  let S2 : Microstate 3 := ⟨W, sigma2, void_phi⟩

  use S1, S2

  have h_eta : (1 : ℝ)/4 ≥ 0 := by norm_num
  use h_eta

  have hS1w : S1.weights.weights = void_W_val := rfl
  have hS1s : S1.sigma.val = void_sigma1_val := rfl
  have hS1p : S1.phi = void_phi := rfl
  have hS2w : S2.weights.weights = void_W_val := rfl
  have hS2s : S2.sigma.val = void_sigma2_val := rfl
  have hS2p : S2.phi = void_phi := rfl

  have h1_total : ∑ x, ∑ y, (S1.weights.weights x y + (1/4) * raw_strain S1.phi S1.sigma x y) > 0 := by
    simp only [hS1w, hS1s, hS1p, Fin.sum_univ_three, raw_strain, d0,
               void_W_val_00, void_W_val_01, void_W_val_02, void_W_val_10, void_W_val_11, void_W_val_12,
               void_W_val_20, void_W_val_21, void_W_val_22, void_phi_val,
               void_sigma1_val_00, void_sigma1_val_01, void_sigma1_val_02,
               void_sigma1_val_10, void_sigma1_val_11, void_sigma1_val_12,
               void_sigma1_val_20, void_sigma1_val_21, void_sigma1_val_22]
    norm_num
  use h1_total

  have h2_total : ∑ x, ∑ y, (S2.weights.weights x y + (1/4) * raw_strain S2.phi S2.sigma x y) > 0 := by
    simp only [hS2w, hS2s, hS2p, Fin.sum_univ_three, raw_strain, d0,
               void_W_val_00, void_W_val_01, void_W_val_02, void_W_val_10, void_W_val_11, void_W_val_12,
               void_W_val_20, void_W_val_21, void_W_val_22, void_phi_val, void_sigma2_val_eq]
    norm_num
  use h2_total

  refine ⟨by norm_num, ?_, ?_⟩

  · rfl

  · intro h_eq
    have key : to_dynamic (evolve_micro S1 (1/4) h_eta h1_total).weights 1 ≠
               to_dynamic (evolve_micro S2 (1/4) h_eta h2_total).weights 1 := by
      intro h_topo_eq
      have h_edges : (to_dynamic (evolve_micro S1 (1/4) h_eta h1_total).weights 1).active_edges =
                     (to_dynamic (evolve_micro S2 (1/4) h_eta h2_total).weights 1).active_edges := by
        rw [h_topo_eq]

      have hW : W.weights = void_W_val := rfl
      have hs1 : sigma1.val = void_sigma1_val := rfl
      have hs2 : sigma2.val = void_sigma2_val := rfl

      have S1_weight_02 : plasticity_step W void_phi sigma1 (1/4) 0 2 = 27/22 := by
        unfold plasticity_step raw_strain d0
        simp only [hW, hs1, Fin.sum_univ_three,
                   void_W_val_00, void_W_val_01, void_W_val_02, void_W_val_10, void_W_val_11, void_W_val_12,
                   void_W_val_20, void_W_val_21, void_W_val_22, void_phi_val,
                   void_sigma1_val_00, void_sigma1_val_01, void_sigma1_val_02,
                   void_sigma1_val_10, void_sigma1_val_11, void_sigma1_val_12,
                   void_sigma1_val_20, void_sigma1_val_21, void_sigma1_val_22]
        norm_num

      have S1_crosses : plasticity_step W void_phi sigma1 (1/4) 0 2 ≥ 1 := by
        rw [S1_weight_02]; norm_num

      have S2_weight_02 : plasticity_step W void_phi sigma2 (1/4) 0 2 = 1/2 := by
        unfold plasticity_step raw_strain d0
        simp only [hW, hs2, Fin.sum_univ_three,
                   void_W_val_00, void_W_val_01, void_W_val_02, void_W_val_10, void_W_val_11, void_W_val_12,
                   void_W_val_20, void_W_val_21, void_W_val_22, void_phi_val, void_sigma2_val_eq]
        norm_num

      have S2_stays : plasticity_step W void_phi sigma2 (1/4) 0 2 < 1 := by
        rw [S2_weight_02]; norm_num

      have h02_in_S1 : ((0 : Fin 3), (2 : Fin 3)) ∈
          (to_dynamic (evolve_micro S1 (1/4) h_eta h1_total).weights 1).active_edges := by
        unfold to_dynamic
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_, ?_⟩
        · show plasticity_step S1.weights S1.phi S1.sigma (1/4) 0 2 ≥ 1
          exact S1_crosses
        · decide

      have h02_not_in_S2 : ((0 : Fin 3), (2 : Fin 3)) ∉
          (to_dynamic (evolve_micro S2 (1/4) h_eta h2_total).weights 1).active_edges := by
        unfold to_dynamic
        rw [Finset.mem_filter]
        intro ⟨_, h_ge, _⟩
        have h_evolved : plasticity_step S2.weights S2.phi S2.sigma (1/4) 0 2 ≥ 1 := h_ge
        have : plasticity_step W void_phi sigma2 (1/4) 0 2 ≥ 1 := h_evolved
        linarith [S2_stays]

      rw [h_edges] at h02_in_S1
      exact h02_not_in_S2 h02_in_S1

    apply key
    have : (observe (evolve_micro S1 (1/4) h_eta h1_total) 1).topology =
           (observe (evolve_micro S2 (1/4) h_eta h2_total) 1).topology := by
      rw [h_eq]
    simp only [observe] at this
    exact this

end Diaspora.Models
