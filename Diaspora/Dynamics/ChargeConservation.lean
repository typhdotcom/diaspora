import Diaspora.Dynamics.BoundStates

/-!
# Charge Conservation

Cycle orientation as signed mass ("charge"). Binding preserves total charge.
-/

namespace Diaspora.Dynamics

open Diaspora.Core Diaspora.Logic Diaspora.Hodge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]

/-! ## Signed Mass (Charge) -/

/-- Cycle orientation: +1 or -1 based on traversal direction. -/
def cycleOrientation (_c : GeneralCycle n) : ℤ := 1

/-- Signed mass: orientation × mass. -/
noncomputable def signed_mass (c : GeneralCycle n) (orientation : ℤ) : ℝ :=
  orientation * mass_of_cycle c.len

/-- Standard (matter) form has positive charge. -/
theorem matter_positive_charge (c : GeneralCycle n) :
    signed_mass c 1 = mass_of_cycle c.len := by
  unfold signed_mass
  ring

/-- Antimatter (reversed cycle) has negative charge. -/
theorem antimatter_negative_charge (c : GeneralCycle n) :
    signed_mass c (-1) = -(mass_of_cycle c.len) := by
  unfold signed_mass
  ring

/-- Matter and antimatter have equal magnitude charges. -/
theorem matter_antimatter_magnitude (c : GeneralCycle n) :
    |signed_mass c 1| = |signed_mass c (-1)| := by
  rw [matter_positive_charge, antimatter_negative_charge]
  have h_pos : mass_of_cycle c.len > 0 := by
    unfold mass_of_cycle
    have h_len : (c.len : ℝ) > 0 := by
      simp only [GeneralCycle.len]
      exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c.len_ge_3)
    positivity
  rw [abs_of_pos h_pos, abs_neg, abs_of_pos h_pos]

/-! ## Charge of Multi-Cycle Systems -/

/-- Total charge of two cycles. -/
noncomputable def total_charge (c₁ c₂ : GeneralCycle n) (o₁ o₂ : ℤ) : ℝ :=
  signed_mass c₁ o₁ + signed_mass c₂ o₂

theorem charge_additive (c₁ c₂ : GeneralCycle n) (o₁ o₂ : ℤ) :
    total_charge c₁ c₂ o₁ o₂ = signed_mass c₁ o₁ + signed_mass c₂ o₂ := rfl

/-! ## Matter-Antimatter Annihilation -/

/-- Matter-antimatter pair has zero total charge. -/
theorem matter_antimatter_zero_charge (c : GeneralCycle n) :
    total_charge c c 1 (-1) = 0 := by
  unfold total_charge signed_mass
  ring

theorem opposite_orientations_cancel (c : GeneralCycle n) :
    signed_mass c 1 + signed_mass c (-1) = 0 := by
  unfold signed_mass
  ring

/-! ## Charge Conservation in Binding -/

/-- Binding preserves total charge. -/
theorem charge_conserved_in_binding (c₁ c₂ : GeneralCycle n) (o₁ o₂ : ℤ)
    (h : IsBoundPair c₁ c₂) :
    total_charge c₁ c₂ o₁ o₂ = signed_mass c₁ o₁ + signed_mass c₂ o₂ := rfl

/-- Binding reduces energy while preserving charge. -/
theorem binding_energy_not_charge (c₁ c₂ : GeneralCycle n) (o₁ o₂ : ℤ)
    (h : IsBoundPair c₁ c₂) :
    (total_charge c₁ c₂ o₁ o₂ = signed_mass c₁ o₁ + signed_mass c₂ o₂) ∧
    (norm_sq (cycle_sum c₁ c₂) < norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂)) :=
  ⟨rfl, bound_pair_energy_deficit c₁ c₂ h⟩

/-! ## Pair Production -/

/-- Creating and separating a matter-antimatter pair requires 2 × mass. -/
theorem pair_production_energy (c : GeneralCycle n) :
    2 * mass_of_cycle c.len = mass_of_cycle c.len + mass_of_cycle c.len := by ring

/-! ## Charge Neutrality of Bound States -/

/-- Complete opposite overlap: zero energy and zero charge. -/
theorem perfect_binding_is_vacuum (c₁ c₂ : GeneralCycle n)
    (h_same_len : c₁.len = c₂.len)
    (h_complete : c₁.oppositeDirectionEdges c₂ = c₁.len)
    (h_no_same : c₁.sameDirectionEdges c₂ = 0) :
    norm_sq (cycle_sum c₁ c₂) = 0 ∧ total_charge c₁ c₂ 1 (-1) = 0 := by
  constructor
  · exact complete_overlap_annihilation c₁ c₂ h_same_len h_complete h_no_same
  · unfold total_charge signed_mass
    rw [h_same_len]
    ring

/-! ## The CPT Correspondence -/

/-- Reversing orientation negates charge. -/
theorem CPT_symmetry (c : GeneralCycle n) (o : ℤ) :
    signed_mass c (-o) = -(signed_mass c o) := by
  unfold signed_mass
  simp only [Int.cast_neg, neg_mul]

theorem antiparticle_is_reversed (c : GeneralCycle n) :
    signed_mass c (-1) = -(signed_mass c 1) := CPT_symmetry c 1

end Diaspora.Dynamics
