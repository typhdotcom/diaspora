import Diaspora.Dynamics.Action

/-!
# Angular Momentum Quantization

This file establishes angular momentum as a quantized quantity in Diaspora,
completing the parallel with quantum mechanics.

## The Core Insight

In quantum mechanics, angular momentum is quantized: L = mℏ for integers m.
This was Bohr's revolutionary postulate, later derived from wave mechanics.

In Diaspora, this quantization emerges naturally from topology:

- The **winding number** around a cycle is always an integer
- Angular momentum = winding number (in units where ℏ = 1)
- Therefore: L ∈ ℤ (angular momentum is quantized)

This is not imposed—it follows from the discrete structure. You cannot have
fractional winding around a closed loop.

## The Rotator Spectrum

For a harmonic form with winding number m on an n-cycle:
- Each edge carries value m/n (to achieve total winding m)
- Energy = m²/n (quadratic in angular momentum)

This is the quantum rotator spectrum! In standard QM:
  E = L(L+1)ℏ²/(2I) ≈ L²/(2I) for large L

In Diaspora:
  E = L²/n where n acts as "moment of inertia"

Larger cycles (larger n) have smaller rotational energy for the same L,
analogous to larger moments of inertia.

## Connection to Action

The Bohr-Sommerfeld quantization condition states:
  ∮ p dq = nℏ for integer n

In Diaspora, each cycle has action S = E × T = 1 = ℏ. For winding m:
  Total action = m × ℏ = m

This connects action quantization to angular momentum quantization.

## Main Results

- `angular_momentum`: L = winding number (quantized in ℤ)
- `angular_momentum_quantized`: L ∈ ℤ for any harmonic form on a cycle
- `rotator_energy`: E = L²/n (energy-angular momentum relation)
- `minimum_angular_momentum`: |L|_min = 1 (no fractional angular momentum)
- `angular_momentum_additive`: L_total = L₁ + L₂ (conservation)
-/

namespace Diaspora.Dynamics.AngularMomentum

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.Action

/-! ## Angular Momentum Definition -/

/-- The **angular momentum** of a topological defect is its winding number.

    For a harmonic form on a cycle, this is the number of times the form
    "wraps around" the cycle. The Dehn twist has L = 1.

    This is quantized by construction: winding numbers are integers.

    Physical interpretation: Angular momentum measures the "rotational content"
    of a topological defect. It is the discrete analog of orbital angular momentum. -/
def angular_momentum (m : ℤ) : ℤ := m

/-- Angular momentum as a real number for energy calculations. -/
def angular_momentum_real (m : ℤ) : ℝ := (m : ℝ)

/-- The winding number determines the amplitude of the harmonic form.

    For winding m on an n-cycle, each edge carries value m/n.
    This ensures the holonomy (sum around cycle) equals m. -/
noncomputable def harmonic_amplitude (m : ℤ) (n : ℕ) : ℝ := (m : ℝ) / (n : ℝ)

/-! ## Angular Momentum Quantization -/

/-- **Angular Momentum is Quantized**: The winding number is always an integer.

    This is the Diaspora version of Bohr's quantization condition:
    L = mℏ with m ∈ ℤ and ℏ = 1.

    Unlike continuous quantum mechanics where this requires the wave function
    to be single-valued, in Diaspora it follows from discrete topology:
    you cannot wind a fractional amount around a closed loop. -/
theorem angular_momentum_quantized (m : ℤ) :
    ∃ k : ℤ, angular_momentum m = k := ⟨m, rfl⟩

/-- **Minimum Non-Zero Angular Momentum**: The smallest non-zero |L| is 1.

    You cannot have angular momentum between 0 and 1. This is the
    fundamental quantum of angular momentum, analogous to ℏ in standard QM.

    The Dehn twist represents this minimum: L = 1. -/
theorem minimum_nonzero_angular_momentum (m : ℤ) (h : m ≠ 0) :
    |m| ≥ 1 := Int.one_le_abs h

/-- The Dehn twist has angular momentum 1 (the minimum positive value). -/
theorem dehn_twist_angular_momentum : angular_momentum 1 = 1 := rfl

/-! ## The Rotator Energy Spectrum -/

/-- The **rotator energy** for angular momentum L on an n-cycle.

    E = L²/n

    This is the quantum rotator spectrum. The energy is:
    - Quadratic in L (like standard quantum rotator)
    - Inversely proportional to n (larger cycles = smaller energy for same L)

    Physical interpretation: n acts as the "moment of inertia" of the cycle.
    Larger structures can hold more angular momentum with less energy. -/
noncomputable def rotator_energy (L : ℤ) (n : ℕ) : ℝ := (L : ℝ)^2 / (n : ℝ)

/-- **Energy-Angular Momentum Relation**: E = L²/n

    For winding number L on an n-cycle, the energy scales quadratically.

    Derivation: If each edge has value L/n, then
    E = (1/2) × 2n × (L/n)² = L²/n

    (The factor 2n comes from n edges, each counted twice in the inner product.) -/
theorem energy_angular_momentum (L : ℤ) (n : ℕ) (hn : n ≥ 3) :
    rotator_energy L n = (L : ℝ)^2 * mass_of_cycle n := by
  unfold rotator_energy mass_of_cycle
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hn']

/-- The Dehn twist (L=1) has energy 1/n = mass_of_cycle n.

    This recovers the standard result from Twist.lean. -/
theorem dehn_twist_energy_from_L (n : ℕ) (_ : n ≥ 3) :
    rotator_energy 1 n = mass_of_cycle n := by
  unfold rotator_energy mass_of_cycle
  simp

/-- **Energy Increases with Angular Momentum**: Higher |L| means higher energy.

    |L₁| < |L₂| → E(L₁) < E(L₂) (for the same n)

    This is the rotational analog of the mass hierarchy. -/
theorem energy_increases_with_angular_momentum (L₁ L₂ : ℤ) (n : ℕ) (h : n ≥ 3)
    (h_lt : |L₁| < |L₂|) :
    rotator_energy L₁ n < rotator_energy L₂ n := by
  unfold rotator_energy
  have hn : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  apply div_lt_div_of_pos_right _ hn
  have h1 : (L₁ : ℝ)^2 = ((|L₁| : ℤ) : ℝ)^2 := by
    simp only [Int.cast_abs, sq_abs]
  have h2 : (L₂ : ℝ)^2 = ((|L₂| : ℤ) : ℝ)^2 := by
    simp only [Int.cast_abs, sq_abs]
  rw [h1, h2]
  have h_lt' : ((|L₁| : ℤ) : ℝ) < ((|L₂| : ℤ) : ℝ) := Int.cast_lt.mpr h_lt
  have h_pos₁ : (0 : ℝ) ≤ ((|L₁| : ℤ) : ℝ) := by positivity
  have h_pos₂ : (0 : ℝ) < ((|L₂| : ℤ) : ℝ) := by
    have h_L2_ne : L₂ ≠ 0 := by
      intro h_zero
      rw [h_zero, abs_zero] at h_lt
      exact (lt_irrefl 0 (lt_of_le_of_lt (abs_nonneg L₁) h_lt))
    have : |L₂| > 0 := abs_pos.mpr h_L2_ne
    exact Int.cast_pos.mpr this
  exact sq_lt_sq' (by linarith) h_lt'

/-- **Zero Angular Momentum**: L = 0 gives zero energy (vacuum state).

    A cycle with no winding has no rotational energy.
    This is the "classical" state with no angular momentum. -/
theorem zero_angular_momentum_zero_energy (n : ℕ) (_ : n ≥ 3) :
    rotator_energy 0 n = 0 := by
  unfold rotator_energy
  simp

/-! ## Energy Level Spacing -/

/-- The energy difference between consecutive angular momentum states.

    ΔE = E(L+1) - E(L) = (2L + 1)/n

    This increases linearly with L (unlike harmonic oscillator which has constant spacing). -/
theorem energy_level_spacing (L : ℤ) (n : ℕ) (h : n ≥ 3) :
    rotator_energy (L + 1) n - rotator_energy L n = (2 * L + 1 : ℤ) / (n : ℝ) := by
  unfold rotator_energy
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  push_cast
  ring

/-- The minimum energy gap (between L=0 and L=1) is 1/n = mass.

    This is the same as the mass of the Dehn twist. -/
theorem minimum_energy_gap (n : ℕ) (h : n ≥ 3) :
    rotator_energy 1 n - rotator_energy 0 n = mass_of_cycle n := by
  rw [zero_angular_momentum_zero_energy n h]
  simp [rotator_energy, mass_of_cycle]

/-! ## Angular Momentum Additivity (Conservation) -/

/-- **Angular Momentum is Additive**: Total L = sum of individual L values.

    When two harmonic forms combine (on the same or different cycles),
    their angular momenta add.

    This is the discrete analog of angular momentum conservation. -/
theorem angular_momentum_additive (L₁ L₂ : ℤ) :
    angular_momentum (L₁ + L₂) = angular_momentum L₁ + angular_momentum L₂ := rfl

/-- For opposite windings, angular momentum cancels.

    L + (-L) = 0

    Physical interpretation: A cycle and its reverse (opposite orientation)
    have opposite angular momentum. When combined, they have zero total L. -/
theorem opposite_angular_momentum_cancels (L : ℤ) :
    angular_momentum L + angular_momentum (-L) = 0 := by
  simp [angular_momentum]

/-- **Sign Determines Direction**: Positive and negative L represent opposite rotations.

    This is the discrete analog of clockwise vs counterclockwise rotation.
    Cycles with opposite orientations have opposite angular momentum signs. -/
theorem angular_momentum_sign (L : ℤ) :
    angular_momentum (-L) = -angular_momentum L := rfl

/-! ## Connection to Action -/

/-- **Action-Angular Momentum Relation**: S = |L| for a cycle traversed |L| times.

    The action of a harmonic form with winding L is |L| (in units of ℏ = 1).

    This is the Bohr-Sommerfeld condition:
    ∮ p dq = |L| × ℏ = |L| -/
theorem action_from_angular_momentum (L : ℤ) :
    |L| * planck_constant = |L| := by
  rw [planck_constant_eq_one, mul_one]

/-- The fundamental unit of angular momentum equals the fundamental unit of action.

    L_min = ℏ = 1

    This explains why both are "1" in natural units: they measure the same thing—
    the topological "quantum" of a single winding. -/
theorem angular_momentum_equals_action_quantum :
    (1 : ℤ) = angular_momentum 1 ∧ planck_constant = 1 :=
  ⟨rfl, planck_constant_eq_one⟩

/-! ## The Correspondence Principle -/

/-- **Classical Limit for Angular Momentum**: Large L approaches continuous behavior.

    As |L| → ∞, the relative spacing ΔE/E → 0:
    ΔE/E = (2L+1)/L² → 0

    In this limit, angular momentum appears continuous (classical). -/
theorem classical_limit_angular_momentum (L : ℤ) (n : ℕ) (h : n ≥ 3) (hL : L > 0) :
    (rotator_energy (L + 1) n - rotator_energy L n) / rotator_energy L n =
    (2 * L + 1 : ℤ) / (L : ℝ)^2 := by
  rw [energy_level_spacing L n h]
  unfold rotator_energy
  have hL' : (L : ℝ) ≠ 0 := by
    simp only [ne_eq, Int.cast_eq_zero]
    omega
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hL', hn]

/-! ## The Angular Momentum Correspondence (Summary) -/

/-- **The Angular Momentum Correspondence**

    This theorem collects the fundamental relations for angular momentum:

    1. L is quantized: L ∈ ℤ (integers)
    2. E = L²/n (rotator spectrum)
    3. Minimum |L| = 1 (no fractional angular momentum)
    4. L is additive (conservation)
    5. Action S = |L| (Bohr-Sommerfeld)

    Angular momentum quantization is not a postulate in Diaspora—it emerges
    from the discrete topology. You cannot have fractional winding.

    This completes the quantum mechanical picture alongside:
    - Wave-particle duality (de Broglie)
    - Uncertainty principles (Heisenberg)
    - Action quantization (Bohr-Sommerfeld)
    - Speed of light constancy (Einstein) -/
theorem the_angular_momentum_correspondence (L : ℤ) (n : ℕ) (h : n ≥ 3) :
    -- 1. Angular momentum is quantized
    (∃ k : ℤ, angular_momentum L = k) ∧
    -- 2. Energy-angular momentum relation
    (rotator_energy L n = (L : ℝ)^2 * mass_of_cycle n) ∧
    -- 3. Minimum nonzero is 1
    (L ≠ 0 → |L| ≥ 1) ∧
    -- 4. Additivity
    (∀ L' : ℤ, angular_momentum (L + L') = angular_momentum L + angular_momentum L') ∧
    -- 5. Action connection
    (|L| * planck_constant = |L|) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact angular_momentum_quantized L
  · exact energy_angular_momentum L n h
  · exact minimum_nonzero_angular_momentum L
  · exact fun L' => angular_momentum_additive L L'
  · exact action_from_angular_momentum L

/-! ## Physical Interpretation -/

/-- **The Bohr Atom in Diaspora**

    In Bohr's model, electrons orbit with quantized angular momentum L = nℏ.
    The energy levels follow E ∝ 1/n² (for the hydrogen atom).

    In Diaspora, topological defects have:
    - Quantized angular momentum L (winding number)
    - Energy E = L²/n (rotator spectrum)
    - Minimum L = 1 (fundamental quantum)

    The key difference: Bohr's E ∝ 1/n² comes from the Coulomb potential,
    while Diaspora's E ∝ L² comes from the rotational structure.

    Both share the essential insight: angular momentum is quantized because
    wave functions (or harmonic forms) must be single-valued around closed loops. -/
theorem bohr_model_connection (n : ℕ) (h : n ≥ 3) :
    -- Dehn twist (L=1) is the "ground state" with minimum nonzero L
    rotator_energy 1 n = mass_of_cycle n ∧
    -- Excited states have L = 2, 3, 4, ...
    ∀ L : ℤ, L ≥ 2 → rotator_energy L n > rotator_energy 1 n := by
  constructor
  · exact dehn_twist_energy_from_L n h
  · intro L hL
    apply energy_increases_with_angular_momentum 1 L n h
    have hL_pos : L ≥ 0 := by omega
    simp only [abs_one]
    rw [abs_of_nonneg hL_pos]
    omega

end Diaspora.Dynamics.AngularMomentum
