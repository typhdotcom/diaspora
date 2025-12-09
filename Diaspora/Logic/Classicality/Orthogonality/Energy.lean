/-
Combined cycle energy formulas: ‖γ₁ + γ₂‖² = ‖γ₁‖² + ‖γ₂‖² + 2⟨γ₁, γ₂⟩.
-/
import Diaspora.Logic.Classicality.Orthogonality.InnerProduct

namespace Diaspora.Logic

open Diaspora.Core Diaspora.Hodge

variable {n : ℕ} [Fintype (Fin n)]

/-- The sum of two cycle forms as a C1 cochain. -/
noncomputable def cycle_sum {n : ℕ} [Fintype (Fin n)] [NeZero n] (c₁ c₂ : GeneralCycle n) : C1 n := {
  val := fun i j => (general_cycle_form c₁).val i j + (general_cycle_form c₂).val i j
  skew := by intro i j; rw [(general_cycle_form c₁).skew, (general_cycle_form c₂).skew]; ring
}

/-- Combined energy formula: ‖γ₁ + γ₂‖² = ‖γ₁‖² + ‖γ₂‖² + 2⟨γ₁, γ₂⟩ -/
theorem combined_cycle_energy {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n) :
    norm_sq (cycle_sum c₁ c₂) = norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) +
        2 * inner_product_C1 (general_cycle_form c₁) (general_cycle_form c₂) := by
  unfold norm_sq inner_product_C1 cycle_sum
  have h_expand : ∀ i j : Fin n,
      ((general_cycle_form c₁).val i j + (general_cycle_form c₂).val i j) *
      ((general_cycle_form c₁).val i j + (general_cycle_form c₂).val i j) =
      (general_cycle_form c₁).val i j * (general_cycle_form c₁).val i j +
      2 * (general_cycle_form c₁).val i j * (general_cycle_form c₂).val i j +
      (general_cycle_form c₂).val i j * (general_cycle_form c₂).val i j := by
    intro i j; ring
  simp_rw [h_expand, Finset.sum_add_distrib]
  have h_factor : ∀ s : Finset (Fin n), ∀ t : Finset (Fin n),
      ∑ i ∈ s, ∑ j ∈ t, 2 * (general_cycle_form c₁).val i j * (general_cycle_form c₂).val i j =
      2 * ∑ i ∈ s, ∑ j ∈ t, (general_cycle_form c₁).val i j * (general_cycle_form c₂).val i j := by
    intro s t
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  simp_rw [h_factor]
  ring

/-- Combined cycle energy using signedOverlap: explicit formula. -/
theorem combined_cycle_energy_formula {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n) :
    norm_sq (cycle_sum c₁ c₂) = 1 / c₁.len + 1 / c₂.len +
        2 * (c₁.signedOverlap c₂ : ℝ) / (c₁.len * c₂.len) := by
  rw [combined_cycle_energy, cycle_inner_product_formula,
      general_cycle_form_energy, general_cycle_form_energy]
  ring

/-- When overlap is negative, combined energy is less than sum of individual energies. -/
theorem negative_overlap_reduces_energy {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h : c₁.signedOverlap c₂ < 0) :
    norm_sq (cycle_sum c₁ c₂) < norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) := by
  rw [combined_cycle_energy]
  have h_len1 : (0 : ℝ) < c₁.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₁.len_ge_3)
  have h_len2 : (0 : ℝ) < c₂.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₂.len_ge_3)
  have h_prod_pos : (0 : ℝ) < c₁.len * c₂.len := mul_pos h_len1 h_len2
  have h_inner_neg : inner_product_C1 (general_cycle_form c₁) (general_cycle_form c₂) < 0 := by
    rw [cycle_inner_product_formula]
    apply div_neg_of_neg_of_pos
    · exact Int.cast_lt_zero.mpr h
    · exact h_prod_pos
  linarith

/-- When overlap is positive, combined energy exceeds sum of individual energies. -/
theorem positive_overlap_increases_energy {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h : c₁.signedOverlap c₂ > 0) :
    norm_sq (cycle_sum c₁ c₂) > norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) := by
  rw [combined_cycle_energy]
  have h_len1 : (0 : ℝ) < c₁.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₁.len_ge_3)
  have h_len2 : (0 : ℝ) < c₂.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₂.len_ge_3)
  have h_prod_pos : (0 : ℝ) < c₁.len * c₂.len := mul_pos h_len1 h_len2
  have h_inner_pos : inner_product_C1 (general_cycle_form c₁) (general_cycle_form c₂) > 0 := by
    rw [cycle_inner_product_formula]
    apply div_pos
    · exact Int.cast_pos.mpr h
    · exact h_prod_pos
  linarith

/-- When overlap is zero, combined energy equals sum of individual energies. -/
theorem zero_overlap_additive {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h : c₁.signedOverlap c₂ = 0) :
    norm_sq (cycle_sum c₁ c₂) = norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) := by
  rw [combined_cycle_energy]
  have h_len1 : (0 : ℝ) < c₁.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₁.len_ge_3)
  have h_len2 : (0 : ℝ) < c₂.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₂.len_ge_3)
  have h_prod_pos : (0 : ℝ) < c₁.len * c₂.len := mul_pos h_len1 h_len2
  have h_inner_zero : inner_product_C1 (general_cycle_form c₁) (general_cycle_form c₂) = 0 := by
    rw [cycle_inner_product_formula, h]
    simp
  linarith

end Diaspora.Logic
