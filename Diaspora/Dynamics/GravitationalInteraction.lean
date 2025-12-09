import Diaspora.Dynamics.GravitationalStability

/-!
# Advanced Gravitational Interactions

## Main Results

- `gravitational_neutrality`: Annihilated pairs have zero interaction with all cycles
- `reduced_mass_formula`: μ = 1/(n₁+n₂)
- `max_shared_edges`: A cycle can share at most n edges total
-/

namespace Diaspora.Dynamics.GravitationalInteraction

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics

variable {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]

/-! ## Gravitational Neutrality -/

omit [DecidableEq (Fin n)] [NeZero n] in
/-- Helper: If norm_sq σ = 0, then σ is zero everywhere. -/
theorem norm_sq_zero_implies_zero (σ : C1 n) (h : norm_sq σ = 0) :
    ∀ i j : Fin n, σ.val i j = 0 := by
  intro i j
  have h_expand : norm_sq σ = (1/2) * ∑ i : Fin n, ∑ j : Fin n, (σ.val i j)^2 := by
    unfold norm_sq inner_product_C1
    congr 1; congr 1
    ext i'; congr 1; ext j'
    ring
  rw [h] at h_expand
  have h_sum_zero : ∑ i : Fin n, ∑ j : Fin n, (σ.val i j)^2 = 0 := by linarith
  have h_term_nonneg : ∀ i j : Fin n, (σ.val i j)^2 ≥ 0 := fun i j => sq_nonneg _
  have h_all_zero : ∀ i' j' : Fin n, (σ.val i' j')^2 = 0 := by
    by_contra h_ne
    push_neg at h_ne
    obtain ⟨i', j', h_ne'⟩ := h_ne
    have h_pos : (σ.val i' j')^2 > 0 := (h_term_nonneg i' j').lt_of_ne' h_ne'
    have h_ge : ∑ i : Fin n, ∑ j : Fin n, (σ.val i j)^2 ≥ (σ.val i' j')^2 := by
      calc ∑ i : Fin n, ∑ j : Fin n, (σ.val i j)^2
          ≥ ∑ j : Fin n, (σ.val i' j)^2 :=
            Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
              (Finset.mem_univ i')
        _ ≥ (σ.val i' j')^2 :=
            Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ j')
    linarith
  exact sq_eq_zero_iff.mp (h_all_zero i j)

/-- Annihilated pairs have zero gravitational interaction with other cycles. -/
theorem gravitational_neutrality (c₁ c₂ c₃ : GeneralCycle n)
    (h_same_len : c₁.len = c₂.len)
    (h_complete : c₁.oppositeDirectionEdges c₂ = c₁.len)
    (h_no_same : c₁.sameDirectionEdges c₂ = 0) :
    inner_product_C1 (cycle_sum c₁ c₂) (general_cycle_form c₃) = 0 := by
  have h_zero_norm := complete_overlap_annihilation c₁ c₂ h_same_len h_complete h_no_same
  have h_sum_zero := norm_sq_zero_implies_zero (cycle_sum c₁ c₂) h_zero_norm
  unfold inner_product_C1
  have h_all_zero : ∀ i j : Fin n,
      (cycle_sum c₁ c₂).val i j * (general_cycle_form c₃).val i j = 0 := by
    intro i j
    rw [h_sum_zero i j]
    ring
  simp_rw [h_all_zero, Finset.sum_const_zero, mul_zero]

/-- Corollary: Annihilated pairs have zero combined form everywhere. -/
theorem annihilated_pair_zero_form (c₁ c₂ : GeneralCycle n)
    (h_same_len : c₁.len = c₂.len)
    (h_complete : c₁.oppositeDirectionEdges c₂ = c₁.len)
    (h_no_same : c₁.sameDirectionEdges c₂ = 0) :
    ∀ i j : Fin n, (cycle_sum c₁ c₂).val i j = 0 := by
  have h_zero_norm := complete_overlap_annihilation c₁ c₂ h_same_len h_complete h_no_same
  exact norm_sq_zero_implies_zero (cycle_sum c₁ c₂) h_zero_norm

/-- An annihilated pair contributes zero to any energy calculation. -/
theorem annihilated_pair_no_contribution (c₁ c₂ : GeneralCycle n) (γ : C1 n)
    (h_same_len : c₁.len = c₂.len)
    (h_complete : c₁.oppositeDirectionEdges c₂ = c₁.len)
    (h_no_same : c₁.sameDirectionEdges c₂ = 0) :
    inner_product_C1 (cycle_sum c₁ c₂) γ = 0 := by
  have h_zero := annihilated_pair_zero_form c₁ c₂ h_same_len h_complete h_no_same
  unfold inner_product_C1
  have h_all : ∀ i j : Fin n, (cycle_sum c₁ c₂).val i j * γ.val i j = 0 := by
    intro i j; rw [h_zero i j]; ring
  simp_rw [h_all, Finset.sum_const_zero, mul_zero]

/-! ## Reduced Mass -/

/-- The **reduced mass** of a two-cycle system: μ = m₁·m₂/(m₁ + m₂) -/
noncomputable def reduced_mass (n₁ n₂ : ℕ) : ℝ :=
  mass_of_cycle n₁ * mass_of_cycle n₂ / (mass_of_cycle n₁ + mass_of_cycle n₂)

/-- Reduced mass in terms of cycle lengths: μ = 1/(n₁ + n₂) -/
theorem reduced_mass_formula (n₁ n₂ : ℕ) (h₁ : n₁ > 0) (h₂ : n₂ > 0) :
    reduced_mass n₁ n₂ = 1 / (n₁ + n₂) := by
  unfold reduced_mass mass_of_cycle
  have h₁' : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h₁)
  have h₂' : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h₂)
  have h_sum_ne : (n₁ : ℝ) + n₂ ≠ 0 := by positivity
  field_simp [h₁', h₂', h_sum_ne]
  ring

/-- Reduced mass is symmetric. -/
theorem reduced_mass_symmetric (n₁ n₂ : ℕ) :
    reduced_mass n₁ n₂ = reduced_mass n₂ n₁ := by
  unfold reduced_mass
  ring

/-- For equal-size cycles, μ = m/2. -/
theorem reduced_mass_equal (m : ℕ) (h : m > 0) :
    reduced_mass m m = mass_of_cycle m / 2 := by
  unfold reduced_mass mass_of_cycle
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h)
  field_simp [hm]
  ring

/-- Binding energy in terms of reduced mass. -/
theorem binding_via_reduced_mass (n₁ n₂ k : ℕ) (h₁ : n₁ > 0) (h₂ : n₂ > 0) :
    sharing_energy_reduction n₁ n₂ k =
    (k : ℝ) * 2 * (mass_of_cycle n₁ + mass_of_cycle n₂) * reduced_mass n₁ n₂ := by
  unfold sharing_energy_reduction reduced_mass mass_of_cycle
  have h₁' : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h₁)
  have h₂' : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h₂)
  have h_sum_ne : (n₁ : ℝ) + n₂ ≠ 0 := by positivity
  field_simp [h₁', h₂', h_sum_ne]

/-! ## Gravitational Field Interpretation -/

/-- The "gravitational field" at an edge due to a cycle is its harmonic form value. -/
noncomputable def gravitational_field (c : GeneralCycle n) (i j : Fin n) : ℝ :=
  (general_cycle_form c).val i j

omit [DecidableEq (Fin n)] in
/-- Combined gravitational field of multiple cycles is additive (superposition). -/
theorem gravitational_field_superposition (c₁ c₂ : GeneralCycle n) (i j : Fin n) :
    gravitational_field c₁ i j + gravitational_field c₂ i j =
    (cycle_sum c₁ c₂).val i j := by
  unfold gravitational_field cycle_sum
  rfl

/-- Annihilated pairs have zero gravitational field everywhere. -/
theorem annihilated_zero_field (c₁ c₂ : GeneralCycle n)
    (h_same_len : c₁.len = c₂.len)
    (h_complete : c₁.oppositeDirectionEdges c₂ = c₁.len)
    (h_no_same : c₁.sameDirectionEdges c₂ = 0)
    (i j : Fin n) :
    gravitational_field c₁ i j + gravitational_field c₂ i j = 0 := by
  rw [gravitational_field_superposition]
  exact annihilated_pair_zero_form c₁ c₂ h_same_len h_complete h_no_same i j

/-! ## Binding Saturation (Statement) -/

omit [Fintype (Fin n)] [NeZero n] in
/-- A cycle can share at most n edges total (same + opposite). -/
theorem max_shared_edges (c₁ c₂ : GeneralCycle n) :
    c₁.sameDirectionEdges c₂ + c₁.oppositeDirectionEdges c₂ ≤ c₁.len := by
  unfold GeneralCycle.sameDirectionEdges GeneralCycle.oppositeDirectionEdges GeneralCycle.len
  have h_bound : ∀ (s₁ s₂ : Finset (Fin c₁.verts.length × Fin c₂.verts.length)),
      (∀ q₁ q₂ : Fin c₁.verts.length × Fin c₂.verts.length, q₁ ∈ s₁ → q₂ ∈ s₁ → q₁.1 = q₂.1 → q₁ = q₂) →
      (∀ q₁ q₂ : Fin c₁.verts.length × Fin c₂.verts.length, q₁ ∈ s₂ → q₂ ∈ s₂ → q₁.1 = q₂.1 → q₁ = q₂) →
      (∀ q₁ q₂ : Fin c₁.verts.length × Fin c₂.verts.length, q₁ ∈ s₁ → q₂ ∈ s₂ → q₁.1 ≠ q₂.1) →
      s₁.card + s₂.card ≤ c₁.verts.length := by
    intro s₁ s₂ h_inj₁ h_inj₂ h_disj
    have h_img₁ : (s₁.image Prod.fst).card = s₁.card :=
      Finset.card_image_of_injOn (fun x hx y hy h => h_inj₁ x y hx hy h)
    have h_img₂ : (s₂.image Prod.fst).card = s₂.card :=
      Finset.card_image_of_injOn (fun x hx y hy h => h_inj₂ x y hx hy h)
    have h_disjoint : Disjoint (s₁.image Prod.fst) (s₂.image Prod.fst) := by
      rw [Finset.disjoint_iff_ne]
      intro k₁ hk₁ k₂ hk₂ h_eq
      simp only [Finset.mem_image] at hk₁ hk₂
      obtain ⟨q₁, hq₁, hq₁'⟩ := hk₁
      obtain ⟨q₂, hq₂, hq₂'⟩ := hk₂
      have h_fst_eq : q₁.1 = q₂.1 := by rw [hq₁', hq₂']; exact h_eq
      exact h_disj q₁ q₂ hq₁ hq₂ h_fst_eq
    calc s₁.card + s₂.card
        = (s₁.image Prod.fst).card + (s₂.image Prod.fst).card := by rw [h_img₁, h_img₂]
      _ = (s₁.image Prod.fst ∪ s₂.image Prod.fst).card := by
          rw [Finset.card_union_of_disjoint h_disjoint]
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = c₁.verts.length := by simp
  apply h_bound
  · intro p₁ p₂ hp₁ hp₂ h_eq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
    have h_v_eq : c₂.vertex p₁.2.val = c₂.vertex p₂.2.val := by
      rw [← hp₁.1, ← hp₂.1, h_eq]
    have h_nodup := c₂.nodup
    unfold GeneralCycle.vertex at h_v_eq
    have h_idx := h_nodup.get_inj_iff.mp h_v_eq
    simp only [Fin.ext_iff, Nat.mod_eq_of_lt p₁.2.isLt, Nat.mod_eq_of_lt p₂.2.isLt] at h_idx
    exact Prod.ext h_eq (Fin.ext h_idx)
  · intro p₁ p₂ hp₁ hp₂ h_eq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
    have h_v_eq : c₂.nextVertex p₁.2.val = c₂.nextVertex p₂.2.val := by
      rw [← hp₁.1, ← hp₂.1, h_eq]
    have h_nodup := c₂.nodup
    unfold GeneralCycle.nextVertex at h_v_eq
    have h_idx := h_nodup.get_inj_iff.mp h_v_eq
    simp only [Fin.ext_iff] at h_idx
    have h_len := c₂.len_ge_3
    have h_eq' : p₁.2.val = p₂.2.val := by
      have ha := p₁.2.isLt
      have hb := p₂.2.isLt
      cases Nat.lt_or_ge (p₁.2.val + 1) c₂.verts.length with
      | inl ha1 =>
        cases Nat.lt_or_ge (p₂.2.val + 1) c₂.verts.length with
        | inl hb1 =>
          rw [Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt hb1] at h_idx; omega
        | inr hb1 =>
          rw [Nat.mod_eq_of_lt ha1, Nat.mod_eq_sub_mod hb1] at h_idx
          have : p₂.2.val + 1 - c₂.verts.length < c₂.verts.length := by omega
          rw [Nat.mod_eq_of_lt this] at h_idx; omega
      | inr ha1 =>
        cases Nat.lt_or_ge (p₂.2.val + 1) c₂.verts.length with
        | inl hb1 =>
          rw [Nat.mod_eq_sub_mod ha1, Nat.mod_eq_of_lt hb1] at h_idx
          have : p₁.2.val + 1 - c₂.verts.length < c₂.verts.length := by omega
          rw [Nat.mod_eq_of_lt this] at h_idx; omega
        | inr hb1 =>
          have ha' : p₁.2.val + 1 - c₂.verts.length < c₂.verts.length := by omega
          have hb' : p₂.2.val + 1 - c₂.verts.length < c₂.verts.length := by omega
          rw [Nat.mod_eq_sub_mod ha1, Nat.mod_eq_of_lt ha',
              Nat.mod_eq_sub_mod hb1, Nat.mod_eq_of_lt hb'] at h_idx; omega
    exact Prod.ext h_eq (Fin.ext h_eq')
  · intro p₁ p₂ hp₁ hp₂ h_eq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
    have h_v : c₂.vertex p₁.2.val = c₂.nextVertex p₂.2.val := by
      calc c₂.vertex p₁.2.val = c₁.vertex p₁.1.val := hp₁.1.symm
        _ = c₁.vertex p₂.1.val := by rw [h_eq]
        _ = c₂.nextVertex p₂.2.val := hp₂.1
    have h_n : c₂.nextVertex p₁.2.val = c₂.vertex p₂.2.val := by
      calc c₂.nextVertex p₁.2.val = c₁.nextVertex p₁.1.val := hp₁.2.symm
        _ = c₁.nextVertex p₂.1.val := by rw [h_eq]
        _ = c₂.vertex p₂.2.val := hp₂.2
    have h_nodup := c₂.nodup
    unfold GeneralCycle.vertex GeneralCycle.nextVertex at h_v h_n
    have h_idx1 := h_nodup.get_inj_iff.mp h_v
    have h_idx2 := h_nodup.get_inj_iff.mp h_n
    simp only [Fin.ext_iff] at h_idx1 h_idx2
    have h_len := c₂.len_ge_3
    have h_p1_mod : p₁.2.val = (p₂.2.val + 1) % c₂.verts.length := by
      rw [Nat.mod_eq_of_lt p₁.2.isLt] at h_idx1; exact h_idx1
    have h_p2_mod : p₂.2.val = (p₁.2.val + 1) % c₂.verts.length := by
      rw [Nat.mod_eq_of_lt p₂.2.isLt] at h_idx2; exact h_idx2.symm
    have h_cycle : (p₁.2.val + 2) % c₂.verts.length = p₁.2.val := by
      have h1_mod : 1 % c₂.verts.length = 1 := Nat.mod_eq_of_lt (by omega)
      calc (p₁.2.val + 2) % c₂.verts.length
          = ((p₁.2.val + 1) + 1) % c₂.verts.length := by ring_nf
        _ = ((p₁.2.val + 1) % c₂.verts.length + 1) % c₂.verts.length := by
            rw [Nat.add_mod (p₁.2.val + 1) 1, h1_mod]
        _ = (p₂.2.val + 1) % c₂.verts.length := by rw [← h_p2_mod]
        _ = p₁.2.val := h_p1_mod.symm
    cases Nat.lt_or_ge (p₁.2.val + 2) c₂.verts.length with
    | inl h_small => rw [Nat.mod_eq_of_lt h_small] at h_cycle; omega
    | inr h_big =>
      have h_sub_lt : p₁.2.val + 2 - c₂.verts.length < c₂.verts.length := by
        have : p₁.2.val < c₂.verts.length := p₁.2.isLt; omega
      rw [Nat.mod_eq_sub_mod h_big, Nat.mod_eq_of_lt h_sub_lt] at h_cycle; omega

end Diaspora.Dynamics.GravitationalInteraction
