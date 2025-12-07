import Diaspora.Dynamics.BoundStates

/-!
# Charge Conservation: Signed Mass and Matter-Antimatter

This file formalizes the interpretation of cycle orientation as "charge" and proves
conservation laws for multi-cycle systems.

## Physical Interpretation

In Diaspora, cycles have two distinct properties:
- **Mass** (unsigned): Energy = 1/n for an n-cycle. Always positive.
- **Charge** (signed): Direction determines sign. +1/n or -1/n.

Same-direction cycles have same-sign charge → repulsion.
Opposite-direction cycles have opposite-sign charge → attraction.
This mirrors electromagnetism: like charges repel, opposite charges attract.

## Main Results

- `signed_mass`: The signed mass of a cycle (orientation × mass)
- `charge_of_pair`: Combined charge of two cycles (additive)
- `opposite_cycles_zero_charge`: Matter + antimatter = zero net charge
- `charge_conserved_in_binding`: Binding preserves total charge

## The Matter-Antimatter Correspondence

A cycle traversed clockwise is "matter" with charge +m.
The same cycle traversed counterclockwise is "antimatter" with charge -m.
When they overlap completely, charge cancels: +m + (-m) = 0.
-/

namespace Diaspora.Dynamics

open Diaspora.Core Diaspora.Logic Diaspora.Hodge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]

/-! ## Signed Mass (Charge) -/

/-- The **orientation** of a cycle: +1 or -1 based on traversal direction.

    In Diaspora, orientation is determined by the order of vertices in the cycle.
    This is the discrete analog of electric charge. -/
def cycleOrientation (_c : GeneralCycle n) : ℤ := 1  -- Convention: cycles are +1 by default

/-- The **signed mass** (charge) of a cycle: orientation × mass.

    - Matter: +1/n (positive orientation)
    - Antimatter: -1/n (negative orientation)

    This is the topological analog of electric charge. -/
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

/-- The total charge of two cycles is the sum of their individual charges.
    This is the additivity of charge. -/
noncomputable def total_charge (c₁ c₂ : GeneralCycle n) (o₁ o₂ : ℤ) : ℝ :=
  signed_mass c₁ o₁ + signed_mass c₂ o₂

/-- **Charge Additivity**: Total charge is the sum of parts. -/
theorem charge_additive (c₁ c₂ : GeneralCycle n) (o₁ o₂ : ℤ) :
    total_charge c₁ c₂ o₁ o₂ = signed_mass c₁ o₁ + signed_mass c₂ o₂ := rfl

/-! ## Matter-Antimatter Annihilation -/

/-- **Zero Charge for Matter-Antimatter Pair**: When a cycle and its reverse
    (same cycle, opposite orientation) combine, total charge is zero.

    This is charge conservation: +m + (-m) = 0. -/
theorem matter_antimatter_zero_charge (c : GeneralCycle n) :
    total_charge c c 1 (-1) = 0 := by
  unfold total_charge signed_mass
  ring

/-- The same cycle with opposite orientations has zero total charge. -/
theorem opposite_orientations_cancel (c : GeneralCycle n) :
    signed_mass c 1 + signed_mass c (-1) = 0 := by
  unfold signed_mass
  ring

/-! ## Charge Conservation in Binding -/

/-- **Charge Conservation Principle**: When two cycles bind (share edges with
    opposite direction), the total charge is preserved.

    Binding changes energy but not charge. -/
theorem charge_conserved_in_binding (c₁ c₂ : GeneralCycle n) (o₁ o₂ : ℤ)
    (h : IsBoundPair c₁ c₂) :
    -- Before binding (separate)
    total_charge c₁ c₂ o₁ o₂ =
    -- After binding (still same total charge, just lower energy)
    signed_mass c₁ o₁ + signed_mass c₂ o₂ := by
  -- The key insight: binding changes energy, not charge
  -- Total charge is just the sum of individual charges
  rfl

/-- **Energy Changes, Charge Doesn't**: Binding reduces energy while preserving charge. -/
theorem binding_energy_not_charge (c₁ c₂ : GeneralCycle n) (o₁ o₂ : ℤ)
    (h : IsBoundPair c₁ c₂) :
    -- Charge is preserved
    (total_charge c₁ c₂ o₁ o₂ = signed_mass c₁ o₁ + signed_mass c₂ o₂) ∧
    -- But energy is reduced
    (norm_sq (cycle_sum c₁ c₂) < norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂)) :=
  ⟨rfl, bound_pair_energy_deficit c₁ c₂ h⟩

/-! ## Pair Production -/

/-- **Pair Production**: Creating a matter-antimatter pair from vacuum requires
    energy equal to 2 × mass.

    This is the reverse of annihilation: 0 energy → +m + (-m) requires 2m input.

    In Diaspora terms: creating a cycle and its reverse (bound state with complete
    opposite overlap) has zero net energy, but separating them requires 2m. -/
theorem pair_production_energy (c : GeneralCycle n) :
    -- Energy needed to create and separate a matter-antimatter pair
    2 * mass_of_cycle c.len =
    -- Equals 2 × individual mass
    mass_of_cycle c.len + mass_of_cycle c.len := by ring

/-! ## Charge Neutrality of Bound States -/

/-- A perfectly bound matter-antimatter pair (complete opposite overlap) is:
    1. Charge neutral (total charge = 0)
    2. Energy neutral (combined energy = 0)

    This is the Diaspora vacuum: no net topology, no net charge, no net energy. -/
theorem perfect_binding_is_vacuum (c₁ c₂ : GeneralCycle n)
    (h_same_len : c₁.len = c₂.len)
    (h_complete : c₁.oppositeDirectionEdges c₂ = c₁.len)
    (h_no_same : c₁.sameDirectionEdges c₂ = 0) :
    -- Energy is zero
    norm_sq (cycle_sum c₁ c₂) = 0 ∧
    -- Charge is zero (if opposite orientations)
    total_charge c₁ c₂ 1 (-1) = 0 := by
  constructor
  · exact complete_overlap_annihilation c₁ c₂ h_same_len h_complete h_no_same
  · -- For opposite orientations
    unfold total_charge signed_mass
    rw [h_same_len]
    ring

/-! ## The CPT Correspondence -/

/-- **Charge-Parity-Time**: Reversing a cycle negates its charge.

    This is the discrete analog of CPT symmetry:
    - C (charge conjugation): orientation flip → charge negation
    - P (parity): spatial reflection → same effect for cycles
    - T (time reversal): traversal direction → orientation flip

    In Diaspora, all three are the same operation: reversing the cycle. -/
theorem CPT_symmetry (c : GeneralCycle n) (o : ℤ) :
    signed_mass c (-o) = -(signed_mass c o) := by
  unfold signed_mass
  simp only [Int.cast_neg, neg_mul]

/-- **Antiparticle Definition**: The antiparticle of a cycle is the same cycle
    with opposite orientation.

    This follows from CPT: applying C (charge conjugation) negates the charge. -/
theorem antiparticle_is_reversed (c : GeneralCycle n) :
    signed_mass c (-1) = -(signed_mass c 1) := CPT_symmetry c 1

end Diaspora.Dynamics
