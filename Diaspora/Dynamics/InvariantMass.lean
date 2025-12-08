import Diaspora.Dynamics.Dispersion
import Diaspora.Dynamics.BoundStates

/-!
# Invariant Mass: From Lightlike Particles to Timelike Bound States

This file proves that while individual topological defects are lightlike (E = p),
bound states of counter-propagating cycles can have positive invariant mass.

## The Core Insight

In special relativity, the invariant mass squared is:
  m² = E² - p²

For a single cycle: E = p = 1/n, so m² = 0 (lightlike).

For two cycles:
- **Same direction**: p_total = p₁ + p₂, E_total = E₁ + E₂ → still lightlike
- **Opposite direction**: p_total = p₁ - p₂, E_total = E₁ + E₂ - B → can be timelike!

When equal-size cycles counter-propagate:
- Momenta cancel: p_total = 0
- Energies partially cancel via binding: E_total = 2/n - B
- Invariant mass: m = E_total > 0 (timelike!)

This explains how lightlike particles form massive bound states.

## Main Results

- `signed_momentum`: Momentum with sign based on orientation
- `single_cycle_lightlike`: Individual cycles have m² = 0
- `same_direction_lightlike`: Same-direction pairs remain lightlike
- `opposite_direction_timelike`: Counter-propagating pairs are timelike
- `annihilation_returns_to_null`: Complete annihilation gives m = 0

## Physical Interpretation

The transition from lightlike to timelike mirrors standard physics:
two photons moving in the same direction are lightlike (invariant mass 0),
but two photons moving in opposite directions form a timelike system
with positive invariant mass.

In Diaspora, the orientation of a cycle plays the role of propagation direction.
Opposite orientations mean "counter-propagating," and the gravitational binding
that results creates a genuinely massive composite object.
-/

namespace Diaspora.Dynamics.InvariantMass

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.Dispersion

/-! ## Signed Momentum -/

/-- The **signed momentum** of a cycle depends on its orientation.

    Cycles have intrinsic momentum p = 1/n, but the SIGN depends on
    which direction the cycle is traversed:
    - Positive orientation: p = +1/n
    - Negative orientation: p = -1/n

    This is the relativistic analog: a particle and antiparticle
    have opposite 3-momentum if counter-propagating. -/
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

/-- The **invariant mass squared** of a system: m² = E² - p².

    In special relativity, this is Lorentz invariant.
    - m² > 0: timelike (massive)
    - m² = 0: lightlike (massless/null)
    - m² < 0: spacelike (tachyonic, forbidden) -/
noncomputable def invariant_mass_sq (E p : ℝ) : ℝ := E^2 - p^2

/-- The invariant mass (only defined when m² ≥ 0). -/
noncomputable def invariant_mass (E p : ℝ) : ℝ := Real.sqrt (invariant_mass_sq E p)

/-! ## Single Cycles are Lightlike -/

/-- A single cycle has invariant mass squared = 0.

    This is the content of `dispersion_relation`: E = p for all cycles.
    In relativity terms, cycles are null/lightlike. -/
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

/-- **Lightlike Condition**: E = |p| for single cycles. -/
theorem single_cycle_lightlike (n : ℕ) (h : n ≥ 3) :
    mass_of_cycle n = |momentum n| := by
  unfold momentum
  have h_pos : mass_of_cycle n > 0 := by
    unfold mass_of_cycle
    have hn : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    positivity
  rw [abs_of_pos h_pos]

/-! ## Two-Cycle Systems -/

/-- Total energy of a two-cycle system.

    E_total = E₁ + E₂ - binding_energy

    Where binding_energy = 0 for disjoint or same-direction cycles,
    and binding_energy > 0 for opposite-direction sharing. -/
noncomputable def two_cycle_energy (n₁ n₂ : ℕ) (binding : ℝ) : ℝ :=
  mass_of_cycle n₁ + mass_of_cycle n₂ - binding

/-- Total momentum of a two-cycle system.

    p_total = o₁ × p₁ + o₂ × p₂

    Where o₁, o₂ ∈ {+1, -1} are the orientations.
    - Same orientation: p_total = p₁ + p₂
    - Opposite orientation: p_total = p₁ - p₂ -/
noncomputable def two_cycle_momentum (n₁ n₂ : ℕ) (o₁ o₂ : ℤ) : ℝ :=
  signed_momentum n₁ o₁ + signed_momentum n₂ o₂

/-! ## Same-Direction Pairs (Lightlike) -/

/-- **Same-direction pairs remain lightlike** (without binding).

    When two cycles have the same orientation and don't bind:
    - E_total = E₁ + E₂ = p₁ + p₂
    - p_total = p₁ + p₂
    - m² = E² - p² = 0

    Physical interpretation: Parallel photons have zero invariant mass. -/
theorem same_direction_no_binding_lightlike (n₁ n₂ : ℕ) :
    let E := two_cycle_energy n₁ n₂ 0
    let p := two_cycle_momentum n₁ n₂ 1 1
    invariant_mass_sq E p = 0 := by
  simp only
  unfold two_cycle_energy two_cycle_momentum signed_momentum
  simp only [sub_zero]
  unfold invariant_mass_sq momentum
  -- E = m₁ + m₂ = p₁ + p₂ = p
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

/-- **Opposite-direction equal cycles have positive invariant mass** (without binding).

    When two equal cycles have opposite orientations (but don't overlap):
    - E_total = 2/n (energies add)
    - p_total = 0 (momenta cancel!)
    - m² = E² > 0 (timelike!)

    Physical interpretation: Counter-propagating photons form a massive system. -/
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

/-- **Momenta Cancel for Opposite-Direction Equal Cycles** -/
theorem opposite_equal_momentum_cancels (n : ℕ) :
    two_cycle_momentum n n 1 (-1) = 0 := by
  unfold two_cycle_momentum signed_momentum
  ring

/-! ## Bound States: Interpolation from 2m to 0 -/

/-- The invariant mass of a bound pair of equal cycles.

    With k shared edges and cycle length n:
    - Binding energy B = 2k/n²
    - E_total = 2/n - 2k/n²
    - p_total = 0 (momenta cancel)
    - m_invariant = E_total

    As k increases from 0 to n:
    - k = 0: m = 2/n = 2m (unbound)
    - k = n: m = 0 (annihilated) -/
noncomputable def bound_pair_invariant_mass (n k : ℕ) : ℝ :=
  2 * mass_of_cycle n - sharing_energy_reduction n n k

/-- The bound pair invariant mass equals the effective energy (since p = 0). -/
theorem bound_pair_mass_eq_energy (n k : ℕ) (_ : n ≥ 3) :
    bound_pair_invariant_mass n k = 2 * mass_of_cycle n - 2 * (k : ℝ) / (n : ℝ)^2 := by
  unfold bound_pair_invariant_mass sharing_energy_reduction
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hn]

/-- **Unbound equal cycles**: invariant mass = 2m. -/
theorem unbound_equal_invariant_mass (n : ℕ) (_ : n ≥ 3) :
    bound_pair_invariant_mass n 0 = 2 * mass_of_cycle n := by
  unfold bound_pair_invariant_mass sharing_energy_reduction
  simp

/-- **Complete annihilation**: invariant mass = 0. -/
theorem annihilation_invariant_mass (n : ℕ) (_ : n ≥ 3) :
    bound_pair_invariant_mass n n = 0 := by
  unfold bound_pair_invariant_mass sharing_energy_reduction mass_of_cycle
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hn]
  ring

/-- **Monotonicity**: More binding → less invariant mass. -/
theorem more_binding_less_mass (n : ℕ) (_ : n ≥ 3) (k₁ k₂ : ℕ) (hk : k₁ < k₂) (_ : k₂ ≤ n) :
    bound_pair_invariant_mass n k₂ < bound_pair_invariant_mass n k₁ := by
  unfold bound_pair_invariant_mass sharing_energy_reduction
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have h_prod_pos : (0 : ℝ) < (n : ℝ) * (n : ℝ) := mul_pos hn_pos hn_pos
  have h_cast : (k₁ : ℝ) < k₂ := Nat.cast_lt.mpr hk
  -- k₂ > k₁ implies 2k₂/(n²) > 2k₁/(n²)
  have h_div : 2 * (k₁ : ℝ) / ((n : ℝ) * n) < 2 * (k₂ : ℝ) / ((n : ℝ) * n) := by
    apply div_lt_div_of_pos_right _ h_prod_pos
    linarith
  linarith

/-! ## General Opposite-Direction Pairs -/

/-- Invariant mass squared for general opposite-direction unequal cycles.

    For cycles of length n₁ and n₂ with opposite orientations:
    - E_total = 1/n₁ + 1/n₂
    - p_total = 1/n₁ - 1/n₂
    - m² = E² - p² = 4/(n₁·n₂)

    This is always positive for finite n₁, n₂. -/
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

/-- **Opposite-direction pairs are always timelike** (m² > 0). -/
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

/-- The invariant mass of opposite-direction unequal cycles. -/
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

/-- **The Invariant Mass Correspondence** (Summary Theorem)

    This theorem unifies the lightlike-to-timelike transition:

    1. Single cycles are lightlike: m² = 0
    2. Same-direction pairs are lightlike: m² = 0
    3. Opposite-direction pairs are timelike: m² = 4·m₁·m₂ > 0
    4. Equal opposite-direction: m = 2m (total mass)
    5. Complete annihilation: m = 0 (back to lightlike/vacuum)

    Physical interpretation: Topology determines not just energy and momentum,
    but also the causal character of a system. Single defects are null rays
    traveling at c. Bound states of counter-propagating defects are massive
    objects that can be at rest. The matter-antimatter annihilation returns
    the system to the null/vacuum state. -/
theorem the_invariant_mass_correspondence (n : ℕ) (h : n ≥ 3) :
    -- 1. Single cycle is lightlike
    (invariant_mass_sq (mass_of_cycle n) (momentum n) = 0) ∧
    -- 2. Same-direction pair is lightlike
    (invariant_mass_sq (two_cycle_energy n n 0) (two_cycle_momentum n n 1 1) = 0) ∧
    -- 3. Opposite-direction pair is timelike
    (invariant_mass_sq (two_cycle_energy n n 0) (two_cycle_momentum n n 1 (-1)) > 0) ∧
    -- 4. Equal opposite-direction mass = 2m
    (invariant_mass (two_cycle_energy n n 0) (two_cycle_momentum n n 1 (-1)) = 2 * mass_of_cycle n) ∧
    -- 5. Complete annihilation gives m = 0
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

/-- **Charge determines causal character**.

    Matter-matter (same charge): lightlike system
    Matter-antimatter (opposite charge): timelike system

    This connects charge conservation to relativistic invariants:
    opposite charges can annihilate (m → 0), same charges cannot. -/
theorem charge_determines_causality (n : ℕ) (h : n ≥ 3) :
    -- Same charge (same direction) → lightlike
    (invariant_mass_sq (two_cycle_energy n n 0) (two_cycle_momentum n n 1 1) = 0) ∧
    -- Opposite charge (opposite direction) → timelike
    (invariant_mass_sq (two_cycle_energy n n 0) (two_cycle_momentum n n 1 (-1)) > 0) := by
  exact ⟨same_direction_no_binding_lightlike n n,
         (the_invariant_mass_correspondence n h).2.2.1⟩

end Diaspora.Dynamics.InvariantMass
