import Diaspora.Logic.Classicality.Orthogonality

/-!
# Gravity: Edge-Sharing as Attraction

Cycles reduce combined energy by sharing edges with opposite orientation.
-/

namespace Diaspora.Dynamics

open Diaspora.Core Diaspora.Logic Diaspora.Hodge

/-- Energy reduction from sharing k edges with opposite orientation: 2k/(n₁·n₂) -/
noncomputable def sharing_energy_reduction (n₁ n₂ k : ℕ) : ℝ :=
  2 * (k : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))

/-- Opposite-orientation edge sharing reduces combined energy. -/
theorem sharing_reduces_energy {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_opp : c₁.oppositeDirectionEdges c₂ > 0)
    (h_same : c₁.sameDirectionEdges c₂ = 0) :
    norm_sq (cycle_sum c₁ c₂) < norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) := by
  apply negative_overlap_reduces_energy
  unfold GeneralCycle.signedOverlap
  simp only [h_same]
  omega

/-- The binding energy formula: energy saved = 2k/(n₁·n₂) -/
theorem gravity_binding_energy {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_same : c₁.sameDirectionEdges c₂ = 0) :
    norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) - norm_sq (cycle_sum c₁ c₂) =
    sharing_energy_reduction c₁.len c₂.len (c₁.oppositeDirectionEdges c₂) := by
  rw [combined_cycle_energy_formula, general_cycle_form_energy, general_cycle_form_energy]
  unfold sharing_energy_reduction GeneralCycle.signedOverlap
  simp only [h_same, CharP.cast_eq_zero, zero_sub, Int.cast_neg, Int.cast_natCast]
  ring

/-- Complete opposite-direction overlap gives zero combined energy. -/
theorem complete_overlap_annihilation {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_same_len : c₁.len = c₂.len)
    (h_complete_opp : c₁.oppositeDirectionEdges c₂ = c₁.len)
    (h_no_same : c₁.sameDirectionEdges c₂ = 0) :
    norm_sq (cycle_sum c₁ c₂) = 0 := by
  rw [combined_cycle_energy_formula]
  unfold GeneralCycle.signedOverlap
  simp only [h_no_same, CharP.cast_eq_zero, zero_sub, h_complete_opp, Int.cast_neg, Int.cast_natCast]
  have h_len1 : (0 : ℝ) < c₁.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₁.len_ge_3)
  have h_len2 : (0 : ℝ) < c₂.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₂.len_ge_3)
  rw [h_same_len]
  field_simp
  ring

/-- Disjoint cycles have additive energy. -/
theorem disjoint_additive_energy {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_disjoint : c₁.signedOverlap c₂ = 0) :
    norm_sq (cycle_sum c₁ c₂) = norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) := by
  rw [combined_cycle_energy]
  rw [cycle_inner_product_formula, h_disjoint]
  simp only [Int.cast_zero, zero_div, mul_zero, add_zero]

/-- More opposite-direction shared edges = more energy reduction. -/
theorem gravity_is_edge_sharing {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n) :
    ∀ k : ℕ,
      (c₁.oppositeDirectionEdges c₂ = k ∧ c₁.sameDirectionEdges c₂ = 0) →
      norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) - norm_sq (cycle_sum c₁ c₂) =
      sharing_energy_reduction c₁.len c₂.len k := by
  intro k ⟨h_opp, h_same⟩
  rw [← h_opp]
  exact gravity_binding_energy c₁ c₂ h_same

/-! ## Three-Body Gravity: Pairwise Additivity -/

/-- The sum of three cycle forms as a C1 cochain. -/
noncomputable def cycle_sum3 {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ c₃ : GeneralCycle n) : C1 n := {
  val := fun i j => (general_cycle_form c₁).val i j +
                    (general_cycle_form c₂).val i j +
                    (general_cycle_form c₃).val i j
  skew := by
    intro i j
    rw [(general_cycle_form c₁).skew, (general_cycle_form c₂).skew, (general_cycle_form c₃).skew]
    ring
}

/-- Energy of three cycles = sum of individual energies + pairwise interactions. -/
theorem three_cycle_energy_pairwise {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ c₃ : GeneralCycle n) :
    norm_sq (cycle_sum3 c₁ c₂ c₃) =
      norm_sq (general_cycle_form c₁) +
      norm_sq (general_cycle_form c₂) +
      norm_sq (general_cycle_form c₃) +
      2 * inner_product_C1 (general_cycle_form c₁) (general_cycle_form c₂) +
      2 * inner_product_C1 (general_cycle_form c₁) (general_cycle_form c₃) +
      2 * inner_product_C1 (general_cycle_form c₂) (general_cycle_form c₃) := by
  unfold norm_sq inner_product_C1 cycle_sum3
  have h_expand : ∀ i j : Fin n,
      ((general_cycle_form c₁).val i j + (general_cycle_form c₂).val i j +
       (general_cycle_form c₃).val i j) *
      ((general_cycle_form c₁).val i j + (general_cycle_form c₂).val i j +
       (general_cycle_form c₃).val i j) =
      (general_cycle_form c₁).val i j * (general_cycle_form c₁).val i j +
      (general_cycle_form c₂).val i j * (general_cycle_form c₂).val i j +
      (general_cycle_form c₃).val i j * (general_cycle_form c₃).val i j +
      2 * (general_cycle_form c₁).val i j * (general_cycle_form c₂).val i j +
      2 * (general_cycle_form c₁).val i j * (general_cycle_form c₃).val i j +
      2 * (general_cycle_form c₂).val i j * (general_cycle_form c₃).val i j := by
    intro i j; ring
  simp_rw [h_expand, Finset.sum_add_distrib]
  have h_factor : ∀ (γ₁ γ₂ : C1 n),
      ∑ i : Fin n, ∑ j : Fin n, 2 * γ₁.val i j * γ₂.val i j =
      2 * ∑ i : Fin n, ∑ j : Fin n, γ₁.val i j * γ₂.val i j := by
    intro γ₁ γ₂
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  simp_rw [h_factor]
  ring

/-- Three disjoint cycles have purely additive energy. -/
theorem three_disjoint_additive_energy {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ c₃ : GeneralCycle n)
    (h₁₂ : c₁.signedOverlap c₂ = 0)
    (h₁₃ : c₁.signedOverlap c₃ = 0)
    (h₂₃ : c₂.signedOverlap c₃ = 0) :
    norm_sq (cycle_sum3 c₁ c₂ c₃) =
      norm_sq (general_cycle_form c₁) +
      norm_sq (general_cycle_form c₂) +
      norm_sq (general_cycle_form c₃) := by
  rw [three_cycle_energy_pairwise]
  have h₁₂' : inner_product_C1 (general_cycle_form c₁) (general_cycle_form c₂) = 0 := by
    rw [cycle_inner_product_formula, h₁₂]; simp
  have h₁₃' : inner_product_C1 (general_cycle_form c₁) (general_cycle_form c₃) = 0 := by
    rw [cycle_inner_product_formula, h₁₃]; simp
  have h₂₃' : inner_product_C1 (general_cycle_form c₂) (general_cycle_form c₃) = 0 := by
    rw [cycle_inner_product_formula, h₂₃]; simp
  rw [h₁₂', h₁₃', h₂₃']
  ring

/-! ## Mass-Energy Equivalence -/

/-- Mass of an n-cycle: m = 1/n. -/
noncomputable def mass_of_cycle (n : ℕ) : ℝ := 1 / n

/-- Energy of a cycle equals its mass. -/
theorem mass_energy_equivalence {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c : GeneralCycle n) (h_len : c.len = n) :
    norm_sq (general_cycle_form c) = mass_of_cycle n := by
  rw [general_cycle_form_energy, mass_of_cycle, h_len]

/-! ## The Gravitational Force Law -/

/-- Gravitational force per shared edge: F = 2/(n₁·n₂). -/
noncomputable def gravitational_force (n₁ n₂ : ℕ) : ℝ :=
  2 / ((n₁ : ℝ) * (n₂ : ℝ))

/-- F = 2·m₁·m₂. -/
theorem gravitational_force_is_product_of_masses (n₁ n₂ : ℕ) (h₁ : n₁ > 0) (h₂ : n₂ > 0) :
    gravitational_force n₁ n₂ = 2 * mass_of_cycle n₁ * mass_of_cycle n₂ := by
  unfold gravitational_force mass_of_cycle
  have h₁' : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h₁)
  have h₂' : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h₂)
  field_simp [h₁', h₂']

/-- Binding energy per shared edge equals the gravitational force. -/
theorem binding_energy_per_edge {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n) :
    sharing_energy_reduction c₁.len c₂.len (c₁.oppositeDirectionEdges c₂) =
    (c₁.oppositeDirectionEdges c₂ : ℝ) * gravitational_force c₁.len c₂.len := by
  unfold sharing_energy_reduction gravitational_force
  ring

/-! ## Repulsion: Same-Direction Sharing -/

/-- Same-direction edge sharing increases energy. -/
theorem repulsion_is_same_direction {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_same : c₁.sameDirectionEdges c₂ > 0)
    (h_opp : c₁.oppositeDirectionEdges c₂ = 0) :
    norm_sq (cycle_sum c₁ c₂) > norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) := by
  apply positive_overlap_increases_energy
  unfold GeneralCycle.signedOverlap
  simp only [h_opp]
  omega

/-- Sign of overlap determines attraction vs repulsion. -/
theorem gravity_sign_determines_interaction {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n) :
    (c₁.signedOverlap c₂ < 0 → norm_sq (cycle_sum c₁ c₂) < norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂)) ∧
    (c₁.signedOverlap c₂ > 0 → norm_sq (cycle_sum c₁ c₂) > norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂)) ∧
    (c₁.signedOverlap c₂ = 0 → norm_sq (cycle_sum c₁ c₂) = norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂)) :=
  ⟨negative_overlap_reduces_energy c₁ c₂,
   positive_overlap_increases_energy c₁ c₂,
   zero_overlap_additive c₁ c₂⟩

/-! ## Mass Bounds and Quantization -/

/-- Maximum mass = 1/3 (the triangle). -/
theorem maximum_mass : mass_of_cycle 3 = 1/3 := by
  unfold mass_of_cycle
  norm_num

/-- Longer cycles have less mass: n₁ < n₂ → m(n₁) > m(n₂). -/
theorem mass_decreases_with_length (n₁ n₂ : ℕ) (h₁ : n₁ > 0) (h₂ : n₂ > 0) (h_lt : n₁ < n₂) :
    mass_of_cycle n₁ > mass_of_cycle n₂ := by
  unfold mass_of_cycle
  have h₁' : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr h₁
  have h₂' : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr h₂
  have h_lt' : (n₁ : ℝ) < n₂ := Nat.cast_lt.mpr h_lt
  exact one_div_lt_one_div_of_lt h₁' h_lt'

/-- Mass gap between consecutive cycles: 1/(n·(n+1)). -/
theorem mass_gap (n : ℕ) (h : n ≥ 3) :
    mass_of_cycle n - mass_of_cycle (n + 1) = 1 / (n * (n + 1)) := by
  unfold mass_of_cycle
  have hn : (n : ℝ) ≠ 0 := by
    have : n > 0 := by omega
    exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp this)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by
    have : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega : n > 0)
    linarith
  field_simp
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, one_mul]

/-- Chains mass-energy, attraction, and force law. -/
theorem the_diaspora_correspondence_extended {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_opp : c₁.oppositeDirectionEdges c₂ > 0)
    (h_same : c₁.sameDirectionEdges c₂ = 0)
    (h₁ : c₁.len > 0) (h₂ : c₂.len > 0) :
    -- 1. Mass equals energy
    (norm_sq (general_cycle_form c₁) = mass_of_cycle c₁.len) ∧
    (norm_sq (general_cycle_form c₂) = mass_of_cycle c₂.len) ∧
    -- 2. Overlapping reduces energy (attraction)
    (norm_sq (cycle_sum c₁ c₂) < norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂)) ∧
    -- 3. Force is proportional to product of masses
    (gravitational_force c₁.len c₂.len = 2 * mass_of_cycle c₁.len * mass_of_cycle c₂.len) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [general_cycle_form_energy, mass_of_cycle]
  · rw [general_cycle_form_energy, mass_of_cycle]
  · exact sharing_reduces_energy c₁ c₂ h_opp h_same
  · exact gravitational_force_is_product_of_masses c₁.len c₂.len h₁ h₂

end Diaspora.Dynamics
