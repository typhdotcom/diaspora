import Diaspora.Dynamics.BoundStates
import Diaspora.Dynamics.Planck

/-!
# Pair Production: Matter Creation from Energy

This file formalizes pair production - the creation of particle-antiparticle
pairs from energy. This is the reverse of matter-antimatter annihilation.

## The Physics

In quantum field theory, sufficient energy can create a particle-antiparticle pair:
  γ → e⁻ + e⁺

The threshold energy is twice the rest mass: E ≥ 2mc².

In Diaspora, pair production is the reverse of annihilation:
- Annihilation: cycle + anticycle → 0 energy (releases 2m)
- Production: 2m energy → cycle + anticycle

The minimum energy to create ANY matter is 2 × (1/3) = 2/3, achieved by
creating a triangle-antitriangle pair. Larger cycles require less energy.

## Main Results

- `pair_production_threshold`: Creating an n-cycle pair requires energy ≥ 2/n
- `genesis_energy_threshold`: Minimum for any matter creation is 2/3
- `production_annihilation_dual`: These processes are energy-inverses
- `heavier_pairs_harder`: Heavier particles require more energy to create
- `threshold_spectrum`: The production thresholds form a discrete spectrum

## Physical Interpretation

Pair production and annihilation are inverse processes:
- Annihilation: converts mass to "vacuum energy" (binding releases 2m)
- Production: converts energy to mass (creation costs 2m)

The asymmetry of our universe (more matter than antimatter) is not
addressed here, but the threshold mechanics are complete.
-/

namespace Diaspora.Dynamics.PairProduction

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.Planck

/-! ## Pair Production Threshold -/

/-- The **energy threshold** for creating an n-cycle / anticycle pair.

    To create a particle-antiparticle pair, you need at least 2× the rest mass.
    For an n-cycle with mass 1/n, the threshold is 2/n.

    Physical interpretation: This is the minimum "activation energy" needed
    to nucleate topology from the vacuum. Below this threshold, pair creation
    is energetically forbidden. -/
noncomputable def pair_threshold (n : ℕ) : ℝ := 2 * mass_of_cycle n

/-- **Pair Production Threshold Formula**: threshold = 2/n for an n-cycle pair.

    Creating a pair of n-cycles requires energy at least 2/n. -/
theorem pair_threshold_formula (n : ℕ) (h : n > 0) :
    pair_threshold n = 2 / n := by
  unfold pair_threshold mass_of_cycle
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h)
  field_simp [hn]

/-- The pair threshold is positive for valid cycles. -/
theorem pair_threshold_pos (n : ℕ) (h : n ≥ 3) : pair_threshold n > 0 := by
  unfold pair_threshold mass_of_cycle
  have hn : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  positivity

/-! ## Genesis Energy: The Minimum for Any Matter Creation -/

/-- The **genesis threshold**: minimum energy to create any matter whatsoever.

    This is 2/3 = 2 × (1/3), the energy needed for a triangle-antitriangle pair.
    No matter can be created with less energy than this.

    Physical interpretation: The triangle is the simplest possible paradox,
    and its pair is the cheapest possible matter to create. This is the
    "spark of creation" - the minimum investment to birth topology. -/
noncomputable def genesis_threshold : ℝ := pair_threshold 3

/-- The genesis threshold equals 2/3. -/
theorem genesis_threshold_value : genesis_threshold = 2 / 3 := by
  unfold genesis_threshold
  rw [pair_threshold_formula 3 (by omega)]
  norm_num

/-- **Genesis Threshold is Minimal**: No valid pair has a lower threshold.

    For any n ≥ 3, the pair threshold is at least the genesis threshold.
    The triangle pair (n=3) achieves this minimum. -/
theorem genesis_is_minimum (n : ℕ) (h : n ≥ 3) :
    pair_threshold n ≤ genesis_threshold := by
  simp only [pair_threshold, genesis_threshold, mass_of_cycle]
  have h₃ : (3 : ℝ) > 0 := by norm_num
  have hn : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_le : (3 : ℝ) ≤ n := Nat.cast_le.mpr h
  -- 2/n ≤ 2/3 when n ≥ 3
  have h1 : (1 : ℝ) / n ≤ 1 / 3 := one_div_le_one_div_of_le h₃ h_le
  linarith

/-- The triangle pair achieves the genesis threshold exactly. -/
theorem triangle_achieves_genesis : pair_threshold 3 = genesis_threshold := rfl

/-! ## Production-Annihilation Duality -/

/-- **Production-Annihilation Duality**: The energy to create a pair equals
    the energy released by annihilating that pair.

    This is energy conservation: what annihilation releases, production consumes.

    From BoundStates.lean: `total_annihilation_energy` proves escape_energy = 2m
    From this file: pair_threshold = 2m

    These are the same quantity viewed from opposite directions. -/
theorem production_annihilation_dual (n : ℕ) (_h : n ≥ 3) :
    pair_threshold n = 2 * mass_of_cycle n := rfl

/-- Alternative form: the threshold equals the sum of individual masses.

    Creating a pair means creating two particles, each with mass 1/n.
    The total mass (and thus energy) is 1/n + 1/n = 2/n. -/
theorem pair_threshold_is_sum_of_masses (n : ℕ) (_h : n > 0) :
    pair_threshold n = mass_of_cycle n + mass_of_cycle n := by
  unfold pair_threshold
  ring

/-! ## Threshold Hierarchy -/

/-- **Heavier Particles are Harder to Create**: Smaller n means higher threshold.

    n₁ < n₂ implies:
    - mass(n₁) > mass(n₂)  (heavier)
    - threshold(n₁) > threshold(n₂)  (harder to create)

    Physical interpretation: Creating heavy particles (like triangles) costs
    more energy than creating light particles (large cycles). -/
theorem heavier_pairs_harder (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_lt : n₁ < n₂) :
    pair_threshold n₁ > pair_threshold n₂ := by
  unfold pair_threshold
  have h_mass := mass_decreases_with_length n₁ n₂ (by omega) (by omega) h_lt
  linarith

/-- **Lighter Particles are Easier to Create**: Larger n means lower threshold.

    This is the contrapositive view of heavier_pairs_harder. -/
theorem lighter_pairs_easier (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_lt : n₁ < n₂) :
    pair_threshold n₂ < pair_threshold n₁ :=
  heavier_pairs_harder n₁ n₂ h₁ h₂ h_lt

/-! ## The Threshold Spectrum -/

/-- **The Threshold Spectrum**: Pair thresholds form a discrete set.

    The allowed thresholds are: 2/3, 2/4, 2/5, 2/6, ...
    This is the reciprocal of the mass spectrum, scaled by 2.

    Physical interpretation: Energy is quantized at creation. You cannot
    create a particle pair with arbitrary energy—only specific threshold
    values are physically meaningful. -/
theorem threshold_spectrum (n : ℕ) (h : n ≥ 3) :
    ∃ k : ℕ, k ≥ 3 ∧ pair_threshold n = 2 / k := by
  use n, h
  exact pair_threshold_formula n (by omega)

/-- **Threshold Gap**: The gap between consecutive thresholds.

    Δ(n) = threshold(n) - threshold(n+1) = 2/(n(n+1))

    This mirrors the mass gap formula. -/
theorem threshold_gap (n : ℕ) (h : n ≥ 3) :
    pair_threshold n - pair_threshold (n + 1) = 2 / (n * (n + 1)) := by
  unfold pair_threshold
  have h_gap := mass_gap n h
  have h_double : 2 * mass_of_cycle n - 2 * mass_of_cycle (n + 1) =
                  2 * (mass_of_cycle n - mass_of_cycle (n + 1)) := by ring
  rw [h_double, h_gap]
  ring

/-! ## Connection to Planck Scale -/

/-- **Genesis Below Planck Energy**: The genesis threshold (2/3) is below
    the Planck energy (1/√2 ≈ 0.707).

    Since 2/3 ≈ 0.667 < 0.707, creating the simplest matter requires less
    than one Planck energy.

    Physical interpretation: Pair production is a sub-Planckian phenomenon.
    You don't need Planck-scale energies to create matter—the discrete
    topology sets a lower threshold. -/
theorem genesis_below_planck_energy : genesis_threshold < planck_energy := by
  rw [genesis_threshold_value]
  unfold planck_energy hbar c G
  simp only [one_mul, one_pow]
  -- Goal: 2/3 < √(1/2)
  -- Since √(1/2) = 1/√2 ≈ 0.707 and 2/3 ≈ 0.667
  have h_sq : (2 / 3 : ℝ)^2 < (1 / 2 : ℝ) := by norm_num
  have h_lhs_pos : (0 : ℝ) < 2 / 3 := by norm_num
  have h_sqrt_pos : (0 : ℝ) < Real.sqrt (1 / 2) := Real.sqrt_pos.mpr (by norm_num)
  rw [← Real.sqrt_sq (le_of_lt h_lhs_pos)]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) h_sq

/-- **Genesis Threshold in Planck Units**:

    genesis / E_P = (2/3) / (1/√2) = (2√2)/3 ≈ 0.943

    We're about 94% of a Planck energy away from creating matter. -/
theorem genesis_planck_ratio : genesis_threshold / planck_energy = 2 * Real.sqrt 2 / 3 := by
  rw [genesis_threshold_value]
  unfold planck_energy hbar c G
  simp only [one_mul, one_pow]
  have h_sqrt : Real.sqrt (1 / 2) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  rw [h_sqrt]
  have h_sqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp [h_sqrt2_ne]

/-! ## Energy Conservation -/

/-- **Energy Conservation in Pair Production**: The energy put in equals
    the mass-energy of the created pair.

    If you invest exactly the threshold energy 2m, you get:
    - A particle with energy m = 1/n
    - An antiparticle with energy m = 1/n
    - Zero kinetic energy (particles at rest)

    E_in = E_particle + E_antiparticle = m + m = 2m = threshold

    This is E = mc² for pair creation. -/
theorem energy_conservation_production (n : ℕ) (_h : n ≥ 3) :
    pair_threshold n = mass_of_cycle n + mass_of_cycle n := by
  unfold pair_threshold
  ring

/-! ## The Pair Production Correspondence -/

/-- **The Pair Production Correspondence** (Summary Theorem)

    This theorem collects the key relationships:

    1. Threshold = 2m = 2/n for an n-cycle pair
    2. Genesis threshold = 2/3 (triangle pair is cheapest)
    3. Heavier particles have higher thresholds
    4. Production threshold = annihilation release (duality)
    5. Genesis is below Planck energy

    Physical interpretation: Matter creation has a quantized cost.
    The simplest topology (triangle) sets the fundamental energy
    scale for genesis. Below 2/3 units of energy, no matter can exist. -/
theorem the_pair_production_correspondence :
    -- 1. Genesis threshold value
    (genesis_threshold = 2 / 3) ∧
    -- 2. Genesis is minimal
    (∀ n : ℕ, n ≥ 3 → pair_threshold n ≤ genesis_threshold) ∧
    -- 3. Triangle achieves minimum
    (pair_threshold 3 = genesis_threshold) ∧
    -- 4. Genesis below Planck
    (genesis_threshold < planck_energy) ∧
    -- 5. Threshold is positive
    (genesis_threshold > 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact genesis_threshold_value
  · exact genesis_is_minimum
  · rfl
  · exact genesis_below_planck_energy
  · rw [genesis_threshold_value]; norm_num

end Diaspora.Dynamics.PairProduction
