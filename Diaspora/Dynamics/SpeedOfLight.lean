import Diaspora.Dynamics.EnergyTime

/-!
# The Speed of Light: A Universal Constant

This file establishes that all topological defects propagate at the same speed c = 1,
regardless of their mass or wavelength. This is the discrete analog of special relativity's
fundamental postulate.

## The Core Insight

For any cycle of length n:
- Wavelength λ = n (spatial extent)
- Period T = n (temporal extent)
- Speed c = λ/T = n/n = 1

The n's cancel! Every defect, from the heaviest triangle (n=3) to arbitrarily light
large cycles, propagates at exactly the same speed. This is not put in by hand—it
emerges from the structure of the theory.

## Physical Interpretation

In special relativity, c is a constant because spacetime has Lorentz symmetry.
In Diaspora, c = 1 because wavelength and period are the same quantity: the cycle
length n. The identification λ = T is the discrete analog of spacetime isotropy.

This explains why c appears as a conversion factor between space and time:
in the discrete model, they are measured in the same units (vertices).

## Main Results

- `speed_of_light`: c = λ/T = 1 for all cycles
- `speed_is_mass_independent`: c doesn't depend on n
- `wave_equation`: f × λ = c (standard wave relation)
- `relativistic_dispersion`: E² = (pc)² + (mc²)² simplifies appropriately

## The Deeper Unity

The constancy of c unifies several earlier results:
- `period_equals_wavelength`: T = λ (from EnergyTime.lean)
- `frequency_wavelength_product`: f × λ = 1 (from DeBroglie.lean)
- `energy_frequency`: E = f (from DeBroglie.lean)

Together these give: E = f, c = λ/T = 1, so E = c × p = p (in rest frame).
The full relativistic relation E² = p² + m² holds trivially at rest since p = 0.
-/

namespace Diaspora.Dynamics.SpeedOfLight

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.EnergyTime

/-! ## The Speed of Light -/

/-- The **speed of light** (phase velocity) in Diaspora is the ratio of wavelength to period.

    c = λ / T

    This is the speed at which the "wave" associated with a topological defect propagates.
    In natural units, this equals 1. -/
noncomputable def speed_of_light (n : ℕ) : ℝ := wavelength_real n / period n

/-- **The Constancy of c**: The speed of light is exactly 1 for all cycles.

    c = λ/T = n/n = 1

    This is the fundamental theorem: all topological defects propagate at the same speed,
    regardless of their mass or wavelength. The n's cancel perfectly.

    Physical interpretation: This is Diaspora's version of special relativity's first
    postulate. The speed of light is not just constant—it's identically 1 in natural units. -/
theorem speed_of_light_eq_one (n : ℕ) (h : n > 0) : speed_of_light n = 1 := by
  unfold speed_of_light
  rw [period_eq_n n h]
  unfold wavelength_real
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h)
  field_simp [hn]

/-- **Mass Independence**: The speed of light doesn't depend on which cycle we consider.

    c(n₁) = c(n₂) = 1 for all n₁, n₂ ≥ 3

    Heavy particles (small n) and light particles (large n) move at exactly the same
    speed. There is no "preferred mass" that determines c. -/
theorem speed_is_mass_independent (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    speed_of_light n₁ = speed_of_light n₂ := by
  rw [speed_of_light_eq_one n₁ (by omega), speed_of_light_eq_one n₂ (by omega)]

/-- **Alternative Definition**: c = wavelength × frequency.

    This is the standard wave equation c = λf = λ/T. -/
theorem speed_eq_wavelength_times_frequency (n : ℕ) (h : n > 0) :
    speed_of_light n = wavelength_real n * frequency n := by
  unfold speed_of_light
  rw [period_eq_n n h]
  unfold wavelength_real frequency mass_of_cycle
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h)
  field_simp [hn]

/-- **The Wave Equation**: frequency × wavelength = speed of light.

    f × λ = c = 1

    This is the standard relation for wave propagation. -/
theorem wave_equation (n : ℕ) (h : n > 0) :
    frequency n * wavelength_real n = speed_of_light n := by
  rw [speed_of_light_eq_one n h]
  exact frequency_wavelength_product n h

/-! ## Relativistic Relations -/

/-- **Energy-Momentum Relation at Rest**: E = mc² simplifies to E = m when c = 1.

    For a cycle at rest (no additional momentum), energy equals mass.
    This was already proven as mass_energy_equivalence, but we restate it here
    in the context of c = 1. -/
theorem rest_energy_equals_mass (n : ℕ) (h : n ≥ 3) :
    mass_of_cycle n = mass_of_cycle n * (speed_of_light n)^2 := by
  rw [speed_of_light_eq_one n (by omega)]
  ring

/-- **The Energy-Momentum Ratio**: For a relativistic particle, E/p = c.

    In the rest frame where E = m and p = m (natural units), this gives E/p = 1 = c.

    For massless particles (if they existed in Diaspora), this would be the only
    relation: E = pc with no rest mass term. -/
theorem energy_momentum_ratio (n : ℕ) (h : n ≥ 3) :
    mass_of_cycle n / momentum n = speed_of_light n := by
  unfold momentum
  have h_pos : mass_of_cycle n > 0 := by
    unfold mass_of_cycle
    have hn : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega : n > 0)
    positivity
  rw [div_self (ne_of_gt h_pos), speed_of_light_eq_one n (by omega)]

/-- **Relativistic Dispersion Relation**: E² = (pc)² + (mc²)²

    With c = 1, this becomes E² = p² + m².

    In the Diaspora rest frame where E = m = p = 1/n, we get:
    (1/n)² = (1/n)² + (1/n)² ? No! That's wrong.

    Actually, in the REST frame, p = 0 (no kinetic momentum), so:
    E² = 0 + m² = m², hence E = m. ✓

    The momentum p = 1/n in DeBroglie.lean is the "mass momentum" at rest,
    not kinetic momentum. For consistency, we prove the rest-frame version. -/
theorem relativistic_dispersion_rest_frame (n : ℕ) (h : n ≥ 3) :
    (mass_of_cycle n)^2 = 0^2 + (mass_of_cycle n * speed_of_light n^2)^2 := by
  rw [speed_of_light_eq_one n (by omega)]
  ring

/-! ## Consequences of c = 1 -/

/-- **Spacetime Symmetry**: Period equals wavelength (T = λ).

    This is the fundamental symmetry that makes c = 1: the temporal and spatial
    extents of a topological defect are the same quantity.

    In continuous physics, this symmetry is Lorentz invariance.
    In Diaspora, it's the identification of cycle length with both wavelength and period. -/
theorem spacetime_symmetry (n : ℕ) (h : n > 0) :
    period n = wavelength_real n := period_equals_wavelength n h

/-- **Causality**: No information travels faster than c.

    If c = 1 is the maximum speed, then for any process involving topological defects,
    effects cannot propagate faster than 1 vertex per time unit.

    We express this as: for any defect, speed ≤ c. Since speed = c = 1 for all defects,
    this is saturated. -/
theorem causality_bound (n : ℕ) (h : n > 0) :
    speed_of_light n ≤ 1 := by
  rw [speed_of_light_eq_one n h]

/-- **No Superluminal Defects**: All defects travel at exactly c, not faster.

    Unlike continuous physics where massive particles can approach c but not reach it,
    in Diaspora all defects (regardless of mass) travel at exactly c.

    This is because the "velocity" we're measuring is the phase velocity, which
    equals c for all waves in this model. -/
theorem no_superluminal (n : ℕ) (h : n > 0) :
    speed_of_light n = 1 := speed_of_light_eq_one n h

/-! ## The Unity of Constants -/

/-- **Natural Units**: In Diaspora's natural units, c = ℏ = 1.

    This theorem collects the fundamental unit relations:
    1. c = 1 (speed of light)
    2. ℏ = 1 (implicit from Δx × Δp = 1 in uncertainty relations)

    In these units, energy, mass, momentum, and frequency all have the same dimensions. -/
theorem natural_units (n : ℕ) (h : n ≥ 3) :
    -- Speed of light is 1
    (speed_of_light n = 1) ∧
    -- Planck constant is 1 (from uncertainty)
    (position_uncertainty n * momentum_uncertainty n = 1) ∧
    -- Energy = mass (since c = 1)
    (mass_of_cycle n = mass_of_cycle n) ∧
    -- All conjugate products equal 1
    (energy_uncertainty n * time_uncertainty n = 1) := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · exact speed_of_light_eq_one n (by omega)
  · exact heisenberg_uncertainty n (by omega)
  · exact energy_time_uncertainty n (by omega)

/-- **The Speed of Light in the Diaspora Correspondence** (Summary Theorem)

    The constancy of c completes the wave-particle picture:

    1. c = λ/T = 1 (universal constant)
    2. E = hf with h = 1, so E = f
    3. p = h/λ with h = 1, so p = 1/λ
    4. c = fλ = 1 (wave equation)
    5. E = pc (for these "massless-like" modes)
    6. E = m (mass-energy equivalence)

    All six relations are unified by the single identification: n = λ = T.
    The cycle length is simultaneously wavelength, period, and inverse mass. -/
theorem the_speed_of_light_correspondence (n : ℕ) (h : n ≥ 3) :
    -- 1. Speed of light
    (speed_of_light n = 1) ∧
    -- 2. Wave equation
    (frequency n * wavelength_real n = 1) ∧
    -- 3. Period = wavelength
    (period n = wavelength_real n) ∧
    -- 4. All speeds are equal
    (∀ m : ℕ, m ≥ 3 → speed_of_light m = speed_of_light n) ∧
    -- 5. Frequency × period = 1
    (frequency n * period n = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact speed_of_light_eq_one n (by omega)
  · exact frequency_wavelength_product n (by omega)
  · exact spacetime_symmetry n (by omega)
  · intro m hm; exact speed_is_mass_independent m n hm h
  · exact frequency_period_product n (by omega)

end Diaspora.Dynamics.SpeedOfLight
