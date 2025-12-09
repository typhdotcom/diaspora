import Diaspora.Dynamics.Gravity

/-!
# Bound States

Gravitationally bound pairs and escape energy.
-/

namespace Diaspora.Dynamics

open Diaspora.Core Diaspora.Logic Diaspora.Hodge

variable {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]

/-! ## Bound Pairs -/

/-- Cycles sharing edges in opposite direction (attractive configuration). -/
def IsBoundPair (c₁ c₂ : GeneralCycle n) : Prop :=
  c₁.oppositeDirectionEdges c₂ > 0 ∧ c₁.sameDirectionEdges c₂ = 0

/-- A bound pair has less combined energy than the sum of parts. -/
theorem bound_pair_energy_deficit (c₁ c₂ : GeneralCycle n) (h : IsBoundPair c₁ c₂) :
    norm_sq (cycle_sum c₁ c₂) < norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) :=
  sharing_reduces_energy c₁ c₂ h.1 h.2

/-- Energy saved by binding. -/
noncomputable def binding_energy (c₁ c₂ : GeneralCycle n) : ℝ :=
  norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) - norm_sq (cycle_sum c₁ c₂)

theorem binding_energy_formula (c₁ c₂ : GeneralCycle n) (h : c₁.sameDirectionEdges c₂ = 0) :
    binding_energy c₁ c₂ = sharing_energy_reduction c₁.len c₂.len (c₁.oppositeDirectionEdges c₂) := by
  unfold binding_energy
  rw [sub_eq_iff_eq_add]
  rw [add_comm]
  have := gravity_binding_energy c₁ c₂ h
  linarith

theorem bound_pair_positive_binding (c₁ c₂ : GeneralCycle n) (h : IsBoundPair c₁ c₂) :
    binding_energy c₁ c₂ > 0 := by
  unfold binding_energy
  have := bound_pair_energy_deficit c₁ c₂ h
  linarith

/-! ## Escape Energy -/

/-- Energy required to fully separate a bound pair. -/
noncomputable def escape_energy (c₁ c₂ : GeneralCycle n) : ℝ :=
  binding_energy c₁ c₂

omit [DecidableEq (Fin n)] in
theorem escape_energy_equals_binding (c₁ c₂ : GeneralCycle n) :
    escape_energy c₁ c₂ = binding_energy c₁ c₂ := rfl

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

theorem more_overlap_more_binding (c₁ c₂ : GeneralCycle n) (h : c₁.sameDirectionEdges c₂ = 0) :
    binding_energy c₁ c₂ = (c₁.oppositeDirectionEdges c₂ : ℝ) * gravitational_force c₁.len c₂.len := by
  rw [binding_energy_formula c₁ c₂ h]
  rw [binding_energy_per_edge c₁ c₂]

omit [Fintype (Fin n)] [NeZero n] in
/-- Maximum opposite-direction overlap minimizes combined energy. -/
theorem gravitational_equilibrium_principle (c₁ c₂ : GeneralCycle n)
    (_h : c₁.sameDirectionEdges c₂ = 0) :
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

theorem energy_decreases_with_overlap (c₁ c₂ : GeneralCycle n) (h : c₁.sameDirectionEdges c₂ = 0) :
    norm_sq (cycle_sum c₁ c₂) = norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) -
      sharing_energy_reduction c₁.len c₂.len (c₁.oppositeDirectionEdges c₂) := by
  have := gravity_binding_energy c₁ c₂ h
  linarith

/-! ## Matter-Antimatter Annihilation -/

omit [DecidableEq (Fin n)] in
theorem annihilation_releases_energy (c : GeneralCycle n) :
    norm_sq (general_cycle_form c) = mass_of_cycle c.len := by
  rw [general_cycle_form_energy, mass_of_cycle]

/-- Complete overlap annihilation: escape energy equals 2 × mass. -/
theorem total_annihilation_energy (c₁ c₂ : GeneralCycle n)
    (h_same_len : c₁.len = c₂.len)
    (h_complete : c₁.oppositeDirectionEdges c₂ = c₁.len)
    (h_no_same : c₁.sameDirectionEdges c₂ = 0) :
    escape_energy c₁ c₂ = 2 * mass_of_cycle c₁.len := by
  have h_zero := complete_overlap_annihilation c₁ c₂ h_same_len h_complete h_no_same
  unfold escape_energy binding_energy
  rw [h_zero, sub_zero]
  rw [annihilation_releases_energy, annihilation_releases_energy, h_same_len]
  ring

/-! ## Stability of Bound States -/

theorem bound_pair_reduces_strain (c₁ c₂ : GeneralCycle n) (h : IsBoundPair c₁ c₂) :
    norm_sq (cycle_sum c₁ c₂) ≤ norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) := by
  have := bound_pair_energy_deficit c₁ c₂ h
  linarith

theorem binding_enhances_stability (c₁ c₂ : GeneralCycle n) (h : IsBoundPair c₁ c₂) :
    binding_energy c₁ c₂ > 0 ∧
    norm_sq (cycle_sum c₁ c₂) < norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) :=
  ⟨bound_pair_positive_binding c₁ c₂ h, bound_pair_energy_deficit c₁ c₂ h⟩

end Diaspora.Dynamics
