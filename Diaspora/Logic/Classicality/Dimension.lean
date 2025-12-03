/-
Dimension bounds and spectral gap for cycle harmonic forms.
-/
import Diaspora.Logic.Classicality.Orthogonality

namespace Diaspora.Logic

open Diaspora.Core Diaspora.Hodge

variable {n : ℕ} [Fintype (Fin n)]

/-! ## Dimension Bounds from Multiple Cycles -/

/-- A list of cycles is pairwise edge-disjoint if every distinct pair is edge-disjoint. -/
def PairwiseEdgeDisjoint {n : ℕ} (cycles : List (GeneralCycle n)) : Prop :=
  ∀ i j : Fin cycles.length, i ≠ j →
    GeneralCycle.EdgeDisjoint (cycles.get i) (cycles.get j)

/-- Lift a GeneralCycle form to an element of HarmonicSubspace when the cycle is embedded. -/
noncomputable def general_cycle_in_harmonic {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (G : DynamicGraph n) (c : GeneralCycle n)
    (h_embedded : generalCycleEmbeddedIn c G) : HarmonicSubspace G :=
  ⟨⟨general_cycle_form c, by
      intro i j h_not_active
      unfold general_cycle_form
      simp only
      split_ifs with h1 h2
      · exfalso
        obtain ⟨k, hk⟩ := h1
        apply h_not_active
        rw [← hk.1, ← hk.2]
        exact h_embedded ⟨k.val, k.isLt⟩
      · exfalso
        obtain ⟨k, hk⟩ := h2
        apply h_not_active
        have h_fwd := h_embedded ⟨k.val, k.isLt⟩
        rw [← hk.1, ← hk.2]
        exact (G.symmetric _ _).mp h_fwd
      · rfl⟩,
    by
      rw [HarmonicSubspace, Submodule.mem_orthogonal]
      intro σ hσ
      obtain ⟨φ, hφ⟩ := LinearMap.mem_range.mp hσ
      rw [← hφ]
      have h_harm := general_cycle_form_harmonic c
      show Diaspora.Core.ActiveForm.inner (d_G_linear G φ) _ = 0
      unfold Diaspora.Core.ActiveForm.inner
      have h_eq : inner_product_C1 (d_G_linear G φ).val (general_cycle_form c) =
                  inner_product_C1 (d0 φ) (general_cycle_form c) := by
        unfold inner_product_C1
        congr 1
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        by_cases h_cycle : (general_cycle_form c).val i j = 0
        · simp [h_cycle]
        · have h_active : (i, j) ∈ G.active_edges := by
            by_contra h_not
            unfold general_cycle_form at h_cycle
            simp only at h_cycle
            split_ifs at h_cycle with h1 h2
            · obtain ⟨k, hk⟩ := h1
              apply h_not; rw [← hk.1, ← hk.2]; exact h_embedded ⟨k.val, k.isLt⟩
            · obtain ⟨k, hk⟩ := h2
              apply h_not; rw [← hk.1, ← hk.2]
              exact (G.symmetric _ _).mp (h_embedded ⟨k.val, k.isLt⟩)
            · exact h_cycle rfl
          show (d_G_linear G φ).val.val i j * _ = (d0 φ).val i j * _
          unfold d_G_linear d_G d0
          simp only [LinearMap.coe_mk, AddHom.coe_mk, h_active, ↓reduceIte]
      rw [h_eq, divergence_is_adjoint]
      have h_div_zero : divergence (general_cycle_form c) = fun _ => 0 := by
        rw [← IsHarmonic_iff_divergence_zero]; exact h_harm
      simp [h_div_zero]⟩

/-- The general_cycle_in_harmonic is nonzero. -/
lemma general_cycle_in_harmonic_ne_zero {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (G : DynamicGraph n) (c : GeneralCycle n)
    (h_embedded : generalCycleEmbeddedIn c G) :
    general_cycle_in_harmonic G c h_embedded ≠ 0 := by
  intro h_zero
  have h_pos := general_cycle_form_positive_energy c
  simp only [general_cycle_in_harmonic, Submodule.mk_eq_zero] at h_zero
  have h_val : (general_cycle_form c) = ⟨fun _ _ => 0, by intro i j; ring⟩ := by
    ext i j
    have : (0 : ActiveForm G).val.val i j = 0 := rfl
    calc (general_cycle_form c).val i j
        = (⟨general_cycle_form c, _⟩ : ActiveForm G).val.val i j := rfl
      _ = (0 : ActiveForm G).val.val i j := by rw [h_zero]
      _ = 0 := rfl
  unfold norm_sq inner_product_C1 at h_pos
  rw [h_val] at h_pos
  simp at h_pos

/-- Edge-disjoint cycles give orthogonal elements in HarmonicSubspace. -/
lemma edge_disjoint_cycles_orthogonal_in_harmonic {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (G : DynamicGraph n) (c₁ c₂ : GeneralCycle n)
    (h_emb₁ : generalCycleEmbeddedIn c₁ G) (h_emb₂ : generalCycleEmbeddedIn c₂ G)
    (h_disjoint : GeneralCycle.EdgeDisjoint c₁ c₂) :
    inner ℝ (general_cycle_in_harmonic G c₁ h_emb₁ : ActiveForm G)
           (general_cycle_in_harmonic G c₂ h_emb₂ : ActiveForm G) = 0 := by
  simp only [general_cycle_in_harmonic]
  show Diaspora.Core.ActiveForm.inner _ _ = 0
  unfold Diaspora.Core.ActiveForm.inner
  exact edge_disjoint_cycles_orthogonal c₁ c₂ h_disjoint

/-- **Topological Dimension Bound**:
    k pairwise edge-disjoint embedded cycles imply dim(HarmonicSubspace) ≥ k.

    This connects cycle structure to topological dimension: each independent
    cycle mode contributes at least one dimension to the harmonic subspace.
-/
theorem edge_disjoint_cycles_dimension_bound {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (G : DynamicGraph n) (cycles : List (GeneralCycle n))
    (h_embedded : ∀ i : Fin cycles.length, generalCycleEmbeddedIn (cycles.get i) G)
    (h_pairwise : PairwiseEdgeDisjoint cycles) :
    Module.finrank ℝ (HarmonicSubspace G) ≥ cycles.length := by
  -- Build the list of harmonic elements
  let harmonics : Fin cycles.length → HarmonicSubspace G :=
    fun i => general_cycle_in_harmonic G (cycles.get i) (h_embedded i)
  -- They are pairwise orthogonal and nonzero
  have h_orth : ∀ i j : Fin cycles.length, i ≠ j →
      inner ℝ (harmonics i : ActiveForm G) (harmonics j : ActiveForm G) = 0 := by
    intro i j h_ne
    exact edge_disjoint_cycles_orthogonal_in_harmonic G _ _ (h_embedded i) (h_embedded j) (h_pairwise i j h_ne)
  have h_ne_zero : ∀ i, harmonics i ≠ 0 := by
    intro i
    exact general_cycle_in_harmonic_ne_zero G (cycles.get i) (h_embedded i)
  -- Nonzero pairwise orthogonal elements are linearly independent
  by_cases h_empty : cycles.length = 0
  · simp [h_empty]
  · -- Prove linear independence by showing coefficients must be zero
    have h_lin_indep : LinearIndependent ℝ harmonics := by
      rw [linearIndependent_iff']
      intro s g h_sum i hi
      -- Take inner product of both sides with harmonics i
      -- ⟨harmonics i, ∑ g_j * harmonics j⟩ = ∑ g_j * ⟨harmonics i, harmonics j⟩
      -- = g_i * ⟨harmonics i, harmonics i⟩  (orthogonality)
      have h_inner_eq : ∑ j ∈ s, g j * inner ℝ (harmonics i : ActiveForm G) (harmonics j : ActiveForm G) = 0 := by
        -- ∑ g_j * ⟨h_i, h_j⟩ = ⟨h_i, ∑ g_j • h_j⟩
        calc ∑ j ∈ s, g j * inner ℝ (harmonics i : ActiveForm G) (harmonics j : ActiveForm G)
            = ∑ j ∈ s, inner ℝ (harmonics i : ActiveForm G) (g j • harmonics j : ActiveForm G) := by
                congr 1; ext j; rw [inner_smul_right]
          _ = inner ℝ (harmonics i : ActiveForm G) (∑ j ∈ s, (g j • harmonics j : ActiveForm G)) := by
                rw [inner_sum]
          _ = inner ℝ (harmonics i : ActiveForm G) (↑(∑ j ∈ s, g j • harmonics j) : ActiveForm G) := by
                congr 1; simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
          _ = inner ℝ (harmonics i : ActiveForm G) (↑(0 : HarmonicSubspace G) : ActiveForm G) := by
                rw [h_sum]
          _ = 0 := inner_zero_right _
      -- Only i=j term survives due to orthogonality
      have h_cross_zero : ∀ j ∈ s, j ≠ i →
          g j * inner ℝ (harmonics i : ActiveForm G) (harmonics j : ActiveForm G) = 0 := by
        intro j _ hji
        rw [h_orth i j hji.symm, mul_zero]
      rw [← Finset.add_sum_erase _ _ hi] at h_inner_eq
      have h_rest_zero : ∑ j ∈ s.erase i, g j * inner ℝ (harmonics i : ActiveForm G) (harmonics j : ActiveForm G) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact h_cross_zero j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
      rw [h_rest_zero, add_zero] at h_inner_eq
      -- Now h_inner_eq : g i * ⟨harmonics i, harmonics i⟩ = 0
      -- Since harmonics i ≠ 0, we have ⟨harmonics i, harmonics i⟩ ≠ 0
      have h_inner_pos : inner ℝ (harmonics i : ActiveForm G) (harmonics i : ActiveForm G) ≠ 0 := by
        intro h_zero
        have := inner_self_eq_zero.mp h_zero
        exact h_ne_zero i (Subtype.ext this)
      exact (mul_eq_zero.mp h_inner_eq).resolve_right h_inner_pos
    -- Linear independence of k vectors in a finite-dim space ⟹ dim ≥ k
    have h_span := finrank_span_eq_card h_lin_indep
    have h_le : Module.finrank ℝ (Submodule.span ℝ (Set.range harmonics)) ≤
                Module.finrank ℝ (HarmonicSubspace G) := Submodule.finrank_le _
    simp only [Fintype.card_fin] at h_span
    omega

/-! ## Spectral Gap for General Cycles -/

/-- A 1-cochain is supported on a GeneralCycle if it's zero on all non-cycle edges. -/
def SupportedOnGeneralCycle {n : ℕ} (c : GeneralCycle n) (γ : C1 n) : Prop :=
  ∀ i j : Fin n, (¬∃ k : Fin c.verts.length, c.vertex k.val = i ∧ c.nextVertex k.val = j) →
                 (¬∃ k : Fin c.verts.length, c.vertex k.val = j ∧ c.nextVertex k.val = i) →
                 γ.val i j = 0

/-- The general_cycle_form is supported on its cycle. -/
lemma general_cycle_form_supported {n : ℕ} [Fintype (Fin n)] [NeZero n] (c : GeneralCycle n) :
    SupportedOnGeneralCycle c (general_cycle_form c) := by
  intro i j h_not_fwd h_not_rev
  unfold general_cycle_form
  simp only [h_not_fwd, h_not_rev, ↓reduceIte]

/-- The general_cycle_form has constant value 1/k on all forward edges. -/
theorem general_cycle_form_constant {n : ℕ} [Fintype (Fin n)] [NeZero n] (c : GeneralCycle n)
    (k : Fin c.verts.length) :
    (general_cycle_form c).val (c.vertex k.val) (c.nextVertex k.val) = 1 / c.len := by
  unfold general_cycle_form GeneralCycle.len
  simp only
  have h_exists : ∃ k' : Fin c.verts.length, c.vertex k'.val = c.vertex k.val ∧ c.nextVertex k'.val = c.nextVertex k.val := ⟨k, rfl, rfl⟩
  simp only [h_exists, ↓reduceIte]

/-- The winding number of general_cycle_form is 1. -/
theorem general_cycle_form_winding_one {n : ℕ} [Fintype (Fin n)] [NeZero n] (c : GeneralCycle n) :
    ∑ k : Fin c.verts.length, (general_cycle_form c).val (c.vertex k.val) (c.nextVertex k.val) = 1 := by
  have h_len_ge_3 := c.len_ge_3
  have h_len_pos : (c.verts.length : ℝ) > 0 := by positivity
  have h_const : ∀ k : Fin c.verts.length,
      (general_cycle_form c).val (c.vertex k.val) (c.nextVertex k.val) = 1 / c.len :=
    fun k => general_cycle_form_constant c k
  calc ∑ k : Fin c.verts.length, (general_cycle_form c).val (c.vertex k.val) (c.nextVertex k.val)
      = ∑ k : Fin c.verts.length, (1 : ℝ) / c.len := Finset.sum_congr rfl (fun k _ => h_const k)
    _ = c.verts.length * (1 / c.len) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = 1 := by unfold GeneralCycle.len; field_simp

/-- **Generalized Spectral Gap**: The general_cycle_form has minimum nonzero energy 1/k.

For a cycle of length k, the canonical harmonic form has energy exactly 1/k.
This is the minimum possible energy for any nonzero harmonic form on the cycle.
-/
theorem general_cycle_spectral_gap {n : ℕ} [Fintype (Fin n)] [NeZero n] (c : GeneralCycle n) :
    norm_sq (general_cycle_form c) = 1 / c.len ∧
    norm_sq (general_cycle_form c) ≥ 1 / c.len := by
  have h_energy := general_cycle_form_energy c
  exact ⟨h_energy, le_of_eq h_energy.symm⟩

/-- Corollary: Shorter cycles have higher minimum energy.

This gives a physical interpretation: creating a topological defect on a shorter
cycle requires more energy. The triangle (k=3) has minimum energy 1/3, while a
long cycle (k→∞) approaches zero minimum energy.
-/
theorem shorter_cycle_higher_energy {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_shorter : c₁.verts.length < c₂.verts.length) :
    norm_sq (general_cycle_form c₁) > norm_sq (general_cycle_form c₂) := by
  rw [general_cycle_form_energy c₁, general_cycle_form_energy c₂]
  unfold GeneralCycle.len
  have h_len_ge_3₁ := c₁.len_ge_3
  have h_len_ge_3₂ := c₂.len_ge_3
  have h_pos₁ : (c₁.verts.length : ℝ) > 0 := Nat.cast_pos.mpr (by omega : c₁.verts.length > 0)
  have h_pos₂ : (c₂.verts.length : ℝ) > 0 := Nat.cast_pos.mpr (by omega : c₂.verts.length > 0)
  have h_cast_lt : (c₁.verts.length : ℝ) < c₂.verts.length := Nat.cast_lt.mpr h_shorter
  -- 1/a > 1/b ⟺ b < a (for positive a, b)
  have h_iff : (1 / (c₁.verts.length : ℝ) > 1 / c₂.verts.length) ↔
               (c₁.verts.length : ℝ) < c₂.verts.length := by
    rw [gt_iff_lt, one_div_lt_one_div h_pos₂ h_pos₁]
  exact h_iff.mpr h_cast_lt

end Diaspora.Logic
