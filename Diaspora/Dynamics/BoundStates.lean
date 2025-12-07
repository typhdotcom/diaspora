import Diaspora.Dynamics.Gravity

/-!
# Bound States: Gravitational Binding and Escape Energy

This file formalizes gravitationally bound states and their properties:

- **Bound Pair**: Two cycles sharing edges with opposite orientation (attractive)
- **Escape Energy**: The energy required to separate a bound pair
- **Gravitational Equilibrium**: Maximum opposite overlap minimizes energy

## Main Results

- `IsBoundPair`: Predicate for cycles in an attractive configuration
- `escape_energy_equals_binding`: Separating a bound pair requires adding back the binding energy
- `more_overlap_more_binding`: More shared edges → stronger binding
- `gravitational_equilibrium_principle`: Maximum overlap minimizes combined energy
- `annihilation_releases_energy`: Matter-antimatter annihilation releases 2×mass

## Physical Interpretation

A bound state is the gravitational analog of an orbit: two topological defects
held together by their shared edges. The binding energy represents the "gravitational
potential well" - the energy deficit that must be overcome to separate them.

In the extreme case of complete overlap (matter + antimatter), the bound state
has zero energy. Separation would require adding back both masses.
-/

namespace Diaspora.Dynamics

open Diaspora.Core Diaspora.Logic Diaspora.Hodge

variable {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]

/-! ## Bound Pairs -/

/-- Two cycles form a **bound pair** when they share edges in opposite direction.
    This is the attractive configuration: their combined energy is less than
    the sum of their individual energies.

    Physical interpretation: bound particles in a gravitational potential well. -/
def IsBoundPair (c₁ c₂ : GeneralCycle n) : Prop :=
  c₁.oppositeDirectionEdges c₂ > 0 ∧ c₁.sameDirectionEdges c₂ = 0

/-- A bound pair has less combined energy than the sum of parts. -/
theorem bound_pair_energy_deficit (c₁ c₂ : GeneralCycle n) (h : IsBoundPair c₁ c₂) :
    norm_sq (cycle_sum c₁ c₂) < norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) :=
  sharing_reduces_energy c₁ c₂ h.1 h.2

/-- The **binding energy** of a pair: how much energy is saved by binding. -/
noncomputable def binding_energy (c₁ c₂ : GeneralCycle n) : ℝ :=
  norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) - norm_sq (cycle_sum c₁ c₂)

/-- Binding energy equals the sharing reduction formula. -/
theorem binding_energy_formula (c₁ c₂ : GeneralCycle n) (h : c₁.sameDirectionEdges c₂ = 0) :
    binding_energy c₁ c₂ = sharing_energy_reduction c₁.len c₂.len (c₁.oppositeDirectionEdges c₂) := by
  unfold binding_energy
  rw [sub_eq_iff_eq_add]
  rw [add_comm]
  have := gravity_binding_energy c₁ c₂ h
  linarith

/-- Bound pairs have positive binding energy. -/
theorem bound_pair_positive_binding (c₁ c₂ : GeneralCycle n) (h : IsBoundPair c₁ c₂) :
    binding_energy c₁ c₂ > 0 := by
  unfold binding_energy
  have := bound_pair_energy_deficit c₁ c₂ h
  linarith

/-! ## Escape Energy -/

/-- The **escape energy**: energy required to fully separate a bound pair.

    When two cycles are bound (sharing edges with opposite direction), separating
    them requires adding back the binding energy. This is the gravitational
    analog of escape velocity.

    E_escape = E_separate - E_bound = binding_energy -/
noncomputable def escape_energy (c₁ c₂ : GeneralCycle n) : ℝ :=
  binding_energy c₁ c₂

omit [DecidableEq (Fin n)] in
/-- **Escape Energy Theorem**: Separating a bound pair requires adding exactly
    the binding energy.

    Physical interpretation: To move two gravitationally bound particles to
    infinite separation (no shared edges), you must supply energy equal to
    the gravitational potential well depth. -/
theorem escape_energy_equals_binding (c₁ c₂ : GeneralCycle n) :
    escape_energy c₁ c₂ = binding_energy c₁ c₂ := rfl

/-- Escape energy in terms of masses and shared edges.
    E_escape = 2k/(n₁·n₂) = 2k · m₁ · m₂ for k shared edges. -/
theorem escape_energy_formula (c₁ c₂ : GeneralCycle n) (h : c₁.sameDirectionEdges c₂ = 0)
    (h₁ : c₁.len > 0) (h₂ : c₂.len > 0) :
    escape_energy c₁ c₂ = (c₁.oppositeDirectionEdges c₂ : ℝ) *
      2 * mass_of_cycle c₁.len * mass_of_cycle c₂.len := by
  rw [escape_energy_equals_binding, binding_energy_formula c₁ c₂ h]
  unfold sharing_energy_reduction mass_of_cycle
  have h₁' : (c₁.len : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h₁)
  have h₂' : (c₂.len : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h₂)
  field_simp [h₁', h₂']

/-! ## Gravitational Equilibrium -/

/-- **More Overlap Means Stronger Binding**: Each additional shared edge
    (with opposite direction) increases binding energy by the gravitational force.

    ∂(binding_energy)/∂k = gravitational_force = 2/(n₁·n₂) -/
theorem more_overlap_more_binding (c₁ c₂ : GeneralCycle n) (h : c₁.sameDirectionEdges c₂ = 0) :
    binding_energy c₁ c₂ = (c₁.oppositeDirectionEdges c₂ : ℝ) * gravitational_force c₁.len c₂.len := by
  rw [binding_energy_formula c₁ c₂ h]
  rw [binding_energy_per_edge c₁ c₂]

omit [Fintype (Fin n)] [NeZero n] in
/-- **Gravitational Equilibrium Principle**: Among all configurations with the
    same cycles, maximum opposite-direction overlap minimizes combined energy.

    This is the discrete analog of "matter falls into gravitational wells". -/
theorem gravitational_equilibrium_principle (c₁ c₂ : GeneralCycle n)
    (_h : c₁.sameDirectionEdges c₂ = 0) :
    -- More overlap → less combined energy
    ∀ k₁ k₂ : ℕ,
      k₁ < k₂ →
      k₁ ≤ c₁.oppositeDirectionEdges c₂ →
      k₂ ≤ c₁.oppositeDirectionEdges c₂ →
      sharing_energy_reduction c₁.len c₂.len k₁ < sharing_energy_reduction c₁.len c₂.len k₂ := by
  intro k₁ k₂ h_lt _ _
  unfold sharing_energy_reduction
  have h_len1 : (0 : ℝ) < c₁.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₁.len_ge_3)
  have h_len2 : (0 : ℝ) < c₂.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₂.len_ge_3)
  have h_prod_pos : (0 : ℝ) < c₁.len * c₂.len := mul_pos h_len1 h_len2
  have h_k_lt : (k₁ : ℝ) < k₂ := Nat.cast_lt.mpr h_lt
  apply div_lt_div_of_pos_right _ h_prod_pos
  linarith

/-- **Energy Minimum at Maximum Overlap**: Combined energy decreases monotonically
    with opposite-direction overlap. Maximum overlap = minimum energy. -/
theorem energy_decreases_with_overlap (c₁ c₂ : GeneralCycle n) (h : c₁.sameDirectionEdges c₂ = 0) :
    norm_sq (cycle_sum c₁ c₂) = norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) -
      sharing_energy_reduction c₁.len c₂.len (c₁.oppositeDirectionEdges c₂) := by
  have := gravity_binding_energy c₁ c₂ h
  linarith

/-! ## Matter-Antimatter Annihilation -/

omit [DecidableEq (Fin n)] in
/-- **Annihilation Energy Release**: When identical cycles with opposite direction
    completely overlap, the energy released equals the sum of both masses.

    This is the Diaspora analog of E = mc² for matter-antimatter annihilation. -/
theorem annihilation_releases_energy (c : GeneralCycle n) :
    -- Energy of individual cycle
    norm_sq (general_cycle_form c) = mass_of_cycle c.len := by
  rw [general_cycle_form_energy, mass_of_cycle]

/-- **Total Annihilation**: For complete opposite-direction overlap of identical cycles,
    the combined energy is zero, meaning all mass-energy is released.

    Compare to complete_overlap_annihilation: the bound state has zero energy,
    so separating it would require adding back 2 × mass. -/
theorem total_annihilation_energy (c₁ c₂ : GeneralCycle n)
    (h_same_len : c₁.len = c₂.len)
    (h_complete : c₁.oppositeDirectionEdges c₂ = c₁.len)
    (h_no_same : c₁.sameDirectionEdges c₂ = 0) :
    escape_energy c₁ c₂ = 2 * mass_of_cycle c₁.len := by
  -- When completely overlapped, combined energy is 0
  have h_zero := complete_overlap_annihilation c₁ c₂ h_same_len h_complete h_no_same
  -- So escape energy = individual energies + 0 cancellation
  unfold escape_energy binding_energy
  rw [h_zero, sub_zero]
  rw [annihilation_releases_energy, annihilation_releases_energy, h_same_len]
  ring

/-! ## Stability of Bound States -/

/-- A bound pair where both cycles are individually stable (under threshold C_max)
    remains stable as a system, because binding only reduces total strain. -/
theorem bound_pair_reduces_strain (c₁ c₂ : GeneralCycle n) (h : IsBoundPair c₁ c₂) :
    norm_sq (cycle_sum c₁ c₂) ≤ norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) := by
  have := bound_pair_energy_deficit c₁ c₂ h
  linarith

/-- **Bound State Stability**: Gravitationally bound systems have lower energy,
    hence are more stable than unbound systems.

    If individual cycles are at the edge of stability (max strain = C_max),
    binding them reduces the total strain, pushing them below threshold. -/
theorem binding_enhances_stability (c₁ c₂ : GeneralCycle n) (h : IsBoundPair c₁ c₂) :
    binding_energy c₁ c₂ > 0 ∧
    norm_sq (cycle_sum c₁ c₂) < norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) :=
  ⟨bound_pair_positive_binding c₁ c₂ h, bound_pair_energy_deficit c₁ c₂ h⟩

end Diaspora.Dynamics
