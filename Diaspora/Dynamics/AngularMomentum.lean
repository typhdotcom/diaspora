import Diaspora.Dynamics.Action

/-!
# Angular Momentum Quantization

Angular momentum = winding number (integer). Energy E = L²/n (rotator spectrum).
Quantization follows from discrete topology: fractional winding is impossible.
-/

namespace Diaspora.Dynamics.AngularMomentum

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.Action

/-! ## Angular Momentum Definition -/

/-- Angular momentum = winding number -/
def angular_momentum (m : ℤ) : ℤ := m

def angular_momentum_real (m : ℤ) : ℝ := (m : ℝ)

/-- For winding m on an n-cycle, each edge carries value m/n -/
noncomputable def harmonic_amplitude (m : ℤ) (n : ℕ) : ℝ := (m : ℝ) / (n : ℝ)

/-! ## Angular Momentum Quantization -/

theorem angular_momentum_quantized (m : ℤ) :
    ∃ k : ℤ, angular_momentum m = k := ⟨m, rfl⟩

theorem minimum_nonzero_angular_momentum (m : ℤ) (h : m ≠ 0) :
    |m| ≥ 1 := Int.one_le_abs h

theorem dehn_twist_angular_momentum : angular_momentum 1 = 1 := rfl

/-! ## The Rotator Energy Spectrum -/

/-- E = L²/n -/
noncomputable def rotator_energy (L : ℤ) (n : ℕ) : ℝ := (L : ℝ)^2 / (n : ℝ)

theorem energy_angular_momentum (L : ℤ) (n : ℕ) (hn : n ≥ 3) :
    rotator_energy L n = (L : ℝ)^2 * mass_of_cycle n := by
  unfold rotator_energy mass_of_cycle
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hn']

theorem dehn_twist_energy_from_L (n : ℕ) (_ : n ≥ 3) :
    rotator_energy 1 n = mass_of_cycle n := by
  unfold rotator_energy mass_of_cycle
  simp

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

theorem zero_angular_momentum_zero_energy (n : ℕ) (_ : n ≥ 3) :
    rotator_energy 0 n = 0 := by
  unfold rotator_energy
  simp

/-! ## Energy Level Spacing -/

/-- ΔE = E(L+1) - E(L) = (2L + 1)/n -/
theorem energy_level_spacing (L : ℤ) (n : ℕ) (h : n ≥ 3) :
    rotator_energy (L + 1) n - rotator_energy L n = (2 * L + 1 : ℤ) / (n : ℝ) := by
  unfold rotator_energy
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  push_cast
  ring

theorem minimum_energy_gap (n : ℕ) (h : n ≥ 3) :
    rotator_energy 1 n - rotator_energy 0 n = mass_of_cycle n := by
  rw [zero_angular_momentum_zero_energy n h]
  simp [rotator_energy, mass_of_cycle]

/-! ## Angular Momentum Additivity (Conservation) -/

theorem angular_momentum_additive (L₁ L₂ : ℤ) :
    angular_momentum (L₁ + L₂) = angular_momentum L₁ + angular_momentum L₂ := rfl

theorem opposite_angular_momentum_cancels (L : ℤ) :
    angular_momentum L + angular_momentum (-L) = 0 := by
  simp [angular_momentum]

theorem angular_momentum_sign (L : ℤ) :
    angular_momentum (-L) = -angular_momentum L := rfl

/-! ## Connection to Action -/

/-- S = |L| × ℏ = |L| (Bohr-Sommerfeld) -/
theorem action_from_angular_momentum (L : ℤ) :
    |L| * planck_constant = |L| := by
  rw [planck_constant_eq_one, mul_one]

theorem angular_momentum_equals_action_quantum :
    (1 : ℤ) = angular_momentum 1 ∧ planck_constant = 1 :=
  ⟨rfl, planck_constant_eq_one⟩

/-! ## The Correspondence Principle -/

/-- As |L| → ∞, ΔE/E = (2L+1)/L² → 0 (classical limit) -/
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

/-- Summary: L ∈ ℤ, E = L²/n, |L|_min = 1, L additive, S = |L| -/
theorem the_angular_momentum_correspondence (L : ℤ) (n : ℕ) (h : n ≥ 3) :
    (∃ k : ℤ, angular_momentum L = k) ∧
    rotator_energy L n = (L : ℝ)^2 * mass_of_cycle n ∧
    (L ≠ 0 → |L| ≥ 1) ∧
    (∀ L' : ℤ, angular_momentum (L + L') = angular_momentum L + angular_momentum L') ∧
    |L| * planck_constant = |L| := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact angular_momentum_quantized L
  · exact energy_angular_momentum L n h
  · exact minimum_nonzero_angular_momentum L
  · exact fun L' => angular_momentum_additive L L'
  · exact action_from_angular_momentum L

theorem bohr_model_connection (n : ℕ) (h : n ≥ 3) :
    rotator_energy 1 n = mass_of_cycle n ∧
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
