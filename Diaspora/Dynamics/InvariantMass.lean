import Diaspora.Dynamics.Dispersion
import Diaspora.Dynamics.BoundStates

/-! # Invariant Mass -/

namespace Diaspora.Dynamics.InvariantMass

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.Dispersion

/-! ## Signed Momentum -/

/-- Momentum with sign determined by orientation. -/
noncomputable def signed_momentum (n : ℕ) (orientation : ℤ) : ℝ :=
  orientation * momentum n

/-- Matter (positive orientation) has positive momentum. -/
theorem matter_positive_momentum (n : ℕ) :
    signed_momentum n 1 = momentum n := by
  unfold signed_momentum
  simp

/-- Antimatter (negative orientation) has negative momentum. -/
theorem antimatter_negative_momentum (n : ℕ) :
    signed_momentum n (-1) = -momentum n := by
  unfold signed_momentum
  simp

/-- Opposite orientations have opposite momenta. -/
theorem opposite_orientation_opposite_momentum (n : ℕ) :
    signed_momentum n 1 + signed_momentum n (-1) = 0 := by
  unfold signed_momentum
  ring

/-! ## Invariant Mass Squared -/

/-- m² = E² - p² -/
noncomputable def invariant_mass_sq (E p : ℝ) : ℝ := E^2 - p^2

/-- √(m²) when m² ≥ 0. -/
noncomputable def invariant_mass (E p : ℝ) : ℝ := Real.sqrt (invariant_mass_sq E p)

/-! ## Single Cycles are Lightlike -/

/-- Single cycles have m² = 0 (lightlike). -/
theorem single_cycle_invariant_mass_sq (n : ℕ) (h : n ≥ 3) :
    invariant_mass_sq (mass_of_cycle n) (momentum n) = 0 := by
  unfold invariant_mass_sq
  rw [dispersion_relation n h]
  ring

/-- Single cycles have zero invariant mass. -/
theorem single_cycle_invariant_mass (n : ℕ) (h : n ≥ 3) :
    invariant_mass (mass_of_cycle n) (momentum n) = 0 := by
  unfold invariant_mass
  rw [single_cycle_invariant_mass_sq n h]
  simp

/-- E = |p| for single cycles. -/
theorem single_cycle_lightlike (n : ℕ) (h : n ≥ 3) :
    mass_of_cycle n = |momentum n| := by
  unfold momentum
  have h_pos : mass_of_cycle n > 0 := by
    unfold mass_of_cycle
    have hn : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    positivity
  rw [abs_of_pos h_pos]

/-! ## Two-Cycle Systems -/

/-- E₁ + E₂ - binding. -/
noncomputable def two_cycle_energy (n₁ n₂ : ℕ) (binding : ℝ) : ℝ :=
  mass_of_cycle n₁ + mass_of_cycle n₂ - binding

/-- o₁·p₁ + o₂·p₂ where o ∈ {+1, -1}. -/
noncomputable def two_cycle_momentum (n₁ n₂ : ℕ) (o₁ o₂ : ℤ) : ℝ :=
  signed_momentum n₁ o₁ + signed_momentum n₂ o₂

/-! ## Same-Direction Pairs (Lightlike) -/

/-- Same-direction pairs without binding have m² = 0. -/
theorem same_direction_no_binding_lightlike (n₁ n₂ : ℕ) :
    let E := two_cycle_energy n₁ n₂ 0
    let p := two_cycle_momentum n₁ n₂ 1 1
    invariant_mass_sq E p = 0 := by
  simp only
  unfold two_cycle_energy two_cycle_momentum signed_momentum
  simp only [sub_zero]
  unfold invariant_mass_sq momentum
  ring

/-- Same-direction pairs have zero invariant mass. -/
theorem same_direction_invariant_mass (n₁ n₂ : ℕ) :
    let E := two_cycle_energy n₁ n₂ 0
    let p := two_cycle_momentum n₁ n₂ 1 1
    invariant_mass E p = 0 := by
  simp only
  unfold invariant_mass two_cycle_energy two_cycle_momentum signed_momentum invariant_mass_sq momentum
  simp only [sub_zero]
  simp

/-! ## Opposite-Direction Pairs (Timelike) -/

/-- Opposite-direction equal cycles have m² > 0 (momenta cancel). -/
theorem opposite_direction_equal_timelike (n : ℕ) (_h : n ≥ 3) :
    let E := two_cycle_energy n n 0
    let p := two_cycle_momentum n n 1 (-1)
    invariant_mass_sq E p = (2 * mass_of_cycle n)^2 := by
  simp only
  unfold two_cycle_energy two_cycle_momentum signed_momentum
  simp only [sub_zero]
  unfold invariant_mass_sq
  ring

/-- The invariant mass of opposite-direction equal cycles is 2m. -/
theorem opposite_direction_equal_invariant_mass (n : ℕ) (h : n ≥ 3) :
    let E := two_cycle_energy n n 0
    let p := two_cycle_momentum n n 1 (-1)
    invariant_mass E p = 2 * mass_of_cycle n := by
  simp only
  unfold invariant_mass
  rw [opposite_direction_equal_timelike n h]
  have h_pos : 2 * mass_of_cycle n > 0 := by
    unfold mass_of_cycle
    have hn : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    positivity
  rw [Real.sqrt_sq (le_of_lt h_pos)]

/-- Momenta cancel for opposite-direction equal cycles. -/
theorem opposite_equal_momentum_cancels (n : ℕ) :
    two_cycle_momentum n n 1 (-1) = 0 := by
  unfold two_cycle_momentum signed_momentum
  ring

/-! ## Bound States: Interpolation from 2m to 0 -/

/-- Invariant mass of bound pair: 2m - binding. Since p = 0, mass = energy. -/
noncomputable def bound_pair_invariant_mass (n k : ℕ) : ℝ :=
  2 * mass_of_cycle n - sharing_energy_reduction n n k

/-- Bound pair mass = 2/n - 2k/n². -/
theorem bound_pair_mass_eq_energy (n k : ℕ) (_ : n ≥ 3) :
    bound_pair_invariant_mass n k = 2 * mass_of_cycle n - 2 * (k : ℝ) / (n : ℝ)^2 := by
  unfold bound_pair_invariant_mass sharing_energy_reduction
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hn]

/-- Unbound (k=0): mass = 2m. -/
theorem unbound_equal_invariant_mass (n : ℕ) (_ : n ≥ 3) :
    bound_pair_invariant_mass n 0 = 2 * mass_of_cycle n := by
  unfold bound_pair_invariant_mass sharing_energy_reduction
  simp

/-- Full annihilation (k=n): mass = 0. -/
theorem annihilation_invariant_mass (n : ℕ) (_ : n ≥ 3) :
    bound_pair_invariant_mass n n = 0 := by
  unfold bound_pair_invariant_mass sharing_energy_reduction mass_of_cycle
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hn]
  ring

/-- More binding → less mass. -/
theorem more_binding_less_mass (n : ℕ) (_ : n ≥ 3) (k₁ k₂ : ℕ) (hk : k₁ < k₂) (_ : k₂ ≤ n) :
    bound_pair_invariant_mass n k₂ < bound_pair_invariant_mass n k₁ := by
  unfold bound_pair_invariant_mass sharing_energy_reduction
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have h_prod_pos : (0 : ℝ) < (n : ℝ) * (n : ℝ) := mul_pos hn_pos hn_pos
  have h_cast : (k₁ : ℝ) < k₂ := Nat.cast_lt.mpr hk
  have h_div : 2 * (k₁ : ℝ) / ((n : ℝ) * n) < 2 * (k₂ : ℝ) / ((n : ℝ) * n) := by
    apply div_lt_div_of_pos_right _ h_prod_pos
    linarith
  linarith

/-! ## General Opposite-Direction Pairs -/

/-- m² = 4·m₁·m₂ for opposite-direction unequal cycles. -/
theorem opposite_direction_unequal_mass_sq (n₁ n₂ : ℕ) (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3) :
    let E := two_cycle_energy n₁ n₂ 0
    let p := two_cycle_momentum n₁ n₂ 1 (-1)
    invariant_mass_sq E p = 4 * mass_of_cycle n₁ * mass_of_cycle n₂ := by
  simp only
  unfold two_cycle_energy two_cycle_momentum signed_momentum invariant_mass_sq momentum
  simp only [sub_zero]
  unfold mass_of_cycle
  have hn₁ : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn₂ : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hn₁, hn₂]
  ring

/-- Opposite-direction pairs are always timelike (m² > 0). -/
theorem opposite_direction_timelike (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    let E := two_cycle_energy n₁ n₂ 0
    let p := two_cycle_momentum n₁ n₂ 1 (-1)
    invariant_mass_sq E p > 0 := by
  simp only
  rw [opposite_direction_unequal_mass_sq n₁ n₂ h₁ h₂]
  have h₁_pos : mass_of_cycle n₁ > 0 := by
    unfold mass_of_cycle; positivity
  have h₂_pos : mass_of_cycle n₂ > 0 := by
    unfold mass_of_cycle; positivity
  positivity

/-- m = 2√(m₁·m₂) for opposite-direction unequal cycles. -/
theorem opposite_direction_unequal_invariant_mass (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    let E := two_cycle_energy n₁ n₂ 0
    let p := two_cycle_momentum n₁ n₂ 1 (-1)
    invariant_mass E p = 2 * Real.sqrt (mass_of_cycle n₁ * mass_of_cycle n₂) := by
  simp only
  unfold invariant_mass
  rw [opposite_direction_unequal_mass_sq n₁ n₂ h₁ h₂]
  have h₁_pos : mass_of_cycle n₁ > 0 := by unfold mass_of_cycle; positivity
  have h₂_pos : mass_of_cycle n₂ > 0 := by unfold mass_of_cycle; positivity
  have h_prod_pos : mass_of_cycle n₁ * mass_of_cycle n₂ > 0 := mul_pos h₁_pos h₂_pos
  have h_4_prod : (4 : ℝ) * mass_of_cycle n₁ * mass_of_cycle n₂ =
      4 * (mass_of_cycle n₁ * mass_of_cycle n₂) := by ring
  rw [h_4_prod]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have h_sqrt_4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num]
    exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)
  rw [h_sqrt_4]

/-! ## The Invariant Mass Correspondence -/

/-- Summary: lightlike ↔ same direction, timelike ↔ opposite direction. -/
theorem the_invariant_mass_correspondence (n : ℕ) (h : n ≥ 3) :
    (invariant_mass_sq (mass_of_cycle n) (momentum n) = 0) ∧
    (invariant_mass_sq (two_cycle_energy n n 0) (two_cycle_momentum n n 1 1) = 0) ∧
    (invariant_mass_sq (two_cycle_energy n n 0) (two_cycle_momentum n n 1 (-1)) > 0) ∧
    (invariant_mass (two_cycle_energy n n 0) (two_cycle_momentum n n 1 (-1)) = 2 * mass_of_cycle n) ∧
    (bound_pair_invariant_mass n n = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact single_cycle_invariant_mass_sq n h
  · exact same_direction_no_binding_lightlike n n
  · have := opposite_direction_equal_timelike n h
    rw [this]
    have h_pos : mass_of_cycle n > 0 := by unfold mass_of_cycle; positivity
    positivity
  · exact opposite_direction_equal_invariant_mass n h
  · exact annihilation_invariant_mass n h

/-! ## Connection to Charge -/

/-- Same charge → lightlike, opposite charge → timelike. -/
theorem charge_determines_causality (n : ℕ) (h : n ≥ 3) :
    (invariant_mass_sq (two_cycle_energy n n 0) (two_cycle_momentum n n 1 1) = 0) ∧
    (invariant_mass_sq (two_cycle_energy n n 0) (two_cycle_momentum n n 1 (-1)) > 0) := by
  exact ⟨same_direction_no_binding_lightlike n n,
         (the_invariant_mass_correspondence n h).2.2.1⟩

end Diaspora.Dynamics.InvariantMass
