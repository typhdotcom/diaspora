import Diaspora.Dynamics.Velocity
import Diaspora.Dynamics.Dispersion

/-!
# Lorentz Transformations: Covariance of Topological Kinematics

This file proves that Diaspora's relativistic kinematics is Lorentz covariant:
energy and momentum transform correctly under boosts, preserving all invariants.

## The Core Result

Under a Lorentz boost with velocity v:
- E' = γ(E - vp)
- p' = γ(p - vE)

This transformation:
1. Preserves the invariant mass: E'² - p'² = E² - p²
2. Preserves lightlike condition: E = p ⟹ E' = p'
3. Gives the relativistic Doppler effect for cycles

## The Doppler Effect

For lightlike particles (E = p), the boost simplifies to:
- E' = γ(1 - v)E = E·D(v)

where D(v) = √((1-v)/(1+v)) is the Doppler factor.

For a cycle with frequency f = 1/n and wavelength λ = n:
- f' = f·D(v) (redshifted if v > 0, blueshifted if v < 0)
- λ' = λ/D(v) (stretched if v > 0, compressed if v < 0)

## Physical Interpretation

Different inertial observers see the same topological defect with different
energies and momenta. A cycle that appears "heavy" (small n, large E) to one
observer appears "lighter" (larger effective n, smaller E) to a receding observer.

But all observers agree on:
1. The lightlike nature: E = p
2. The quantized spectrum: E ∈ {1/3, 1/4, 1/5, ...} up to Doppler shift
3. The zero invariant mass: E² - p² = 0

This is the relativistic version of Diaspora's "topology is motion" principle:
you cannot stop a cycle, but you can change your frame to make it appear
redshifted or blueshifted.
-/

namespace Diaspora.Dynamics.LorentzTransform

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.Dispersion
open Diaspora.Dynamics.Velocity
open Diaspora.Dynamics.InvariantMass

/-! ## The Lorentz Boost -/

/-- The Lorentz factor γ = 1/√(1 - v²). -/
noncomputable def γ (v : ℝ) : ℝ := 1 / Real.sqrt (1 - v^2)

/-- The boosted energy: E' = γ(E - vp). -/
noncomputable def boost_energy (E p v : ℝ) : ℝ := γ v * (E - v * p)

/-- The boosted momentum: p' = γ(p - vE). -/
noncomputable def boost_momentum (E p v : ℝ) : ℝ := γ v * (p - v * E)

/-! ## Basic Lorentz Factor Properties -/

/-- γ is defined for |v| < 1. -/
theorem γ_defined (v : ℝ) (hv : |v| < 1) : 1 - v^2 > 0 := by
  have h : v^2 < 1 := by
    have h1 : |v|^2 < 1^2 := sq_lt_sq' (by linarith [abs_nonneg v]) hv
    simp only [one_pow, sq_abs] at h1
    exact h1
  linarith

/-- γ ≥ 1 for all valid velocities. -/
theorem γ_ge_one (v : ℝ) (hv : |v| < 1) : γ v ≥ 1 := by
  unfold γ
  have h_pos := γ_defined v hv
  have h_sqrt_pos : Real.sqrt (1 - v^2) > 0 := Real.sqrt_pos.mpr h_pos
  have h_sqrt_le_one : Real.sqrt (1 - v^2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    have h_sq_nonneg : v^2 ≥ 0 := sq_nonneg v
    linarith
  rw [ge_iff_le, one_le_div h_sqrt_pos]
  exact h_sqrt_le_one

/-- γ = 1 when v = 0 (no boost). -/
theorem γ_at_zero : γ 0 = 1 := by
  unfold γ
  simp

/-- The relativistic identity: γ² = 1/(1 - v²). -/
theorem γ_squared (v : ℝ) (hv : |v| < 1) : (γ v)^2 = 1 / (1 - v^2) := by
  unfold γ
  have h_pos := γ_defined v hv
  rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt h_pos)]

/-! ## Invariance of m² -/

/-- **The Invariance Theorem**: Lorentz boosts preserve E² - p².

    This is THE fundamental result of special relativity:
    m² = E² - p² is a Lorentz scalar (invariant under boosts).

    The proof is pure algebra: expanding E'² - p'² gives E² - p². -/
theorem invariant_mass_preserved (E p v : ℝ) (hv : |v| < 1) :
    (boost_energy E p v)^2 - (boost_momentum E p v)^2 = E^2 - p^2 := by
  unfold boost_energy boost_momentum
  have h_pos := γ_defined v hv
  have h_gamma_sq := γ_squared v hv
  -- E'² - p'² = γ²[(E - vp)² - (p - vE)²]
  --           = γ²[(E² - 2vEp + v²p²) - (p² - 2vEp + v²E²)]
  --           = γ²[E² + v²p² - p² - v²E²]
  --           = γ²[E²(1 - v²) - p²(1 - v²)]
  --           = γ²(1 - v²)(E² - p²)
  --           = (E² - p²)  since γ² = 1/(1-v²)
  calc (γ v * (E - v * p))^2 - (γ v * (p - v * E))^2
      = (γ v)^2 * ((E - v * p)^2 - (p - v * E)^2) := by ring
    _ = (γ v)^2 * (E^2 - 2*v*E*p + v^2*p^2 - (p^2 - 2*v*E*p + v^2*E^2)) := by ring
    _ = (γ v)^2 * (E^2 + v^2*p^2 - p^2 - v^2*E^2) := by ring
    _ = (γ v)^2 * (E^2*(1 - v^2) - p^2*(1 - v^2)) := by ring
    _ = (γ v)^2 * (1 - v^2) * (E^2 - p^2) := by ring
    _ = 1 / (1 - v^2) * (1 - v^2) * (E^2 - p^2) := by rw [h_gamma_sq]
    _ = E^2 - p^2 := by field_simp

/-! ## Lightlike Condition Preserved -/

/-- **Lightlike Preserved**: If E = p, then E' = p' under any boost.

    This is crucial: a lightlike particle (E = p) remains lightlike
    after a Lorentz transformation. The light cone is invariant. -/
theorem lightlike_preserved (E p v : ℝ) (h_light : E = p) :
    boost_energy E p v = boost_momentum E p v := by
  unfold boost_energy boost_momentum
  rw [h_light]

/-- Single cycles remain lightlike under boosts. -/
theorem cycle_lightlike_after_boost (n : ℕ) (h : n ≥ 3) (v : ℝ) (_hv : |v| < 1) :
    boost_energy (mass_of_cycle n) (momentum n) v =
    boost_momentum (mass_of_cycle n) (momentum n) v := by
  exact lightlike_preserved (mass_of_cycle n) (momentum n) v (dispersion_relation n h)

/-! ## The Doppler Factor -/

/-- The **Doppler factor** D(v) = √((1-v)/(1+v)).

    For motion away (v > 0): D < 1 (redshift)
    For motion toward (v < 0): D > 1 (blueshift)
    At rest (v = 0): D = 1 (no shift) -/
noncomputable def doppler_factor (v : ℝ) : ℝ := Real.sqrt ((1 - v) / (1 + v))

/-- D(0) = 1: no Doppler shift at rest. -/
theorem doppler_at_zero : doppler_factor 0 = 1 := by
  unfold doppler_factor
  simp

/-- D(v) > 0 for |v| < 1. -/
theorem doppler_positive (v : ℝ) (hv : |v| < 1) : doppler_factor v > 0 := by
  unfold doppler_factor
  rw [abs_lt] at hv
  have h1 : 1 - v > 0 := by linarith
  have h2 : 1 + v > 0 := by linarith
  have h_ratio_pos : (1 - v) / (1 + v) > 0 := div_pos h1 h2
  exact Real.sqrt_pos.mpr h_ratio_pos

/-- D(v) × D(-v) = 1: reciprocal relationship. -/
theorem doppler_reciprocal (v : ℝ) (hv : |v| < 1) :
    doppler_factor v * doppler_factor (-v) = 1 := by
  unfold doppler_factor
  have h1 : 1 - v > 0 := by rw [abs_lt] at hv; linarith
  have h2 : 1 + v > 0 := by rw [abs_lt] at hv; linarith
  have h1' : 1 - (-v) > 0 := by linarith
  have h2' : 1 + (-v) > 0 := by linarith
  rw [← Real.sqrt_mul (le_of_lt (div_pos h1 h2))]
  have h_prod : (1 - v) / (1 + v) * ((1 - -v) / (1 + -v)) = 1 := by
    simp only [sub_neg_eq_add]
    field_simp
    ring
  rw [h_prod, Real.sqrt_one]

/-! ## Doppler Effect for Lightlike Particles -/

/-- **The Doppler Theorem for Lightlike Particles**:
    For E = p, the boost gives E' = E × γ(1 - v) = E × D(v).

    This is the relativistic Doppler effect. -/
theorem lightlike_doppler (E : ℝ) (v : ℝ) :
    boost_energy E E v = E * γ v * (1 - v) := by
  unfold boost_energy
  ring

/-- The Doppler factor relation: γ(1 - v) = √((1-v)/(1+v)) = D(v) when |v| < 1. -/
theorem γ_one_minus_v_eq_doppler (v : ℝ) (hv : |v| < 1) :
    γ v * (1 - v) = doppler_factor v := by
  unfold γ doppler_factor
  rw [abs_lt] at hv
  have h1 : 1 - v > 0 := by linarith
  have h2 : 1 + v > 0 := by linarith
  have h_1mv2 : 1 - v^2 = (1 - v) * (1 + v) := by ring
  rw [h_1mv2]
  have h_sqrt_prod : Real.sqrt ((1 - v) * (1 + v)) = Real.sqrt (1 - v) * Real.sqrt (1 + v) :=
    Real.sqrt_mul (le_of_lt h1) (1 + v)
  rw [h_sqrt_prod]
  have h_sqrt1_ne : Real.sqrt (1 - v) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h1)
  have h_sqrt2_ne : Real.sqrt (1 + v) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h2)
  rw [Real.sqrt_div (le_of_lt h1)]
  field_simp [h_sqrt1_ne, h_sqrt2_ne]
  rw [Real.sq_sqrt (le_of_lt h1)]

/-- **Doppler-shifted energy** for a cycle: E' = E × D(v). -/
theorem cycle_doppler_energy (n : ℕ) (h : n ≥ 3) (v : ℝ) (hv : |v| < 1) :
    boost_energy (mass_of_cycle n) (momentum n) v =
    mass_of_cycle n * doppler_factor v := by
  have h_disp := dispersion_relation n h
  rw [h_disp]
  rw [lightlike_doppler (momentum n) v]
  rw [mul_assoc, γ_one_minus_v_eq_doppler v hv]

/-! ## Frequency and Wavelength Transform -/

/-- **Doppler-shifted frequency**: f' = f × D(v).

    For a receding source (v > 0), D < 1, so f' < f (redshift).
    For an approaching source (v < 0), D > 1, so f' > f (blueshift). -/
noncomputable def doppler_frequency (f v : ℝ) : ℝ := f * doppler_factor v

/-- **Doppler-shifted wavelength**: λ' = λ / D(v).

    Since f × λ = c = 1, if f' = f × D, then λ' = λ / D. -/
noncomputable def doppler_wavelength (wl v : ℝ) : ℝ := wl / doppler_factor v

/-- Frequency-wavelength duality preserved: f' × λ' = f × λ = c = 1. -/
theorem doppler_preserves_wave_equation (f wl v : ℝ) (hv : |v| < 1) (h_wave : f * wl = 1) :
    doppler_frequency f v * doppler_wavelength wl v = 1 := by
  unfold doppler_frequency doppler_wavelength
  have h_D_pos := doppler_positive v hv
  have h_D_ne : doppler_factor v ≠ 0 := ne_of_gt h_D_pos
  field_simp [h_D_ne]
  exact h_wave

/-- Cycle frequency transforms: f' = (1/n) × D(v). -/
theorem cycle_frequency_doppler (n : ℕ) (_h : n ≥ 3) (v : ℝ) (_hv : |v| < 1) :
    doppler_frequency (frequency n) v = frequency n * doppler_factor v := rfl

/-- Cycle wavelength transforms: λ' = n / D(v). -/
theorem cycle_wavelength_doppler (n : ℕ) (_h : n ≥ 3) (v : ℝ) (_hv : |v| < 1) :
    doppler_wavelength (wavelength_real n) v = wavelength_real n / doppler_factor v := rfl

/-! ## Redshift and Blueshift -/

/-- **Redshift**: For v > 0 (receding), D(v) < 1, so f' < f and λ' > λ. -/
theorem redshift (v : ℝ) (hv : 0 < v) (hv' : v < 1) : doppler_factor v < 1 := by
  unfold doppler_factor
  have h1 : 1 - v > 0 := by linarith
  have h2 : 1 + v > 0 := by linarith
  have h_ratio_lt_one : (1 - v) / (1 + v) < 1 := by
    rw [div_lt_one h2]
    linarith
  have h_ratio_pos : (1 - v) / (1 + v) > 0 := div_pos h1 h2
  calc Real.sqrt ((1 - v) / (1 + v))
      < Real.sqrt 1 := by
        apply Real.sqrt_lt_sqrt (le_of_lt h_ratio_pos)
        exact h_ratio_lt_one
    _ = 1 := Real.sqrt_one

/-- **Blueshift**: For v < 0 (approaching), D(v) > 1, so f' > f and λ' < λ. -/
theorem blueshift (v : ℝ) (hv : v < 0) (hv' : -1 < v) : doppler_factor v > 1 := by
  unfold doppler_factor
  have h1 : 1 - v > 0 := by linarith
  have h2 : 1 + v > 0 := by linarith
  have h_ratio_gt_one : (1 - v) / (1 + v) > 1 := by
    rw [gt_iff_lt, one_lt_div h2]
    linarith
  have h_ratio_pos : (1 - v) / (1 + v) > 0 := div_pos h1 h2
  calc Real.sqrt ((1 - v) / (1 + v))
      > Real.sqrt 1 := by
        apply Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)
        exact h_ratio_gt_one
    _ = 1 := Real.sqrt_one

/-! ## Velocity Composition -/

/-- **Relativistic Velocity Composition**: Adding velocities u and v. -/
noncomputable def velocity_composition (u v : ℝ) : ℝ := (u + v) / (1 + u * v)

/-- Composition with zero gives the original velocity. -/
theorem velocity_composition_zero_right (u : ℝ) : velocity_composition u 0 = u := by
  unfold velocity_composition
  simp

/-- Composition is symmetric: u ⊕ v = v ⊕ u. -/
theorem velocity_composition_comm (u v : ℝ) :
    velocity_composition u v = velocity_composition v u := by
  unfold velocity_composition
  ring

/-- The composition of subluminal velocities is subluminal. -/
theorem velocity_composition_subluminal (u v : ℝ)
    (hu : |u| < 1) (hv : |v| < 1) : |velocity_composition u v| < 1 := by
  unfold velocity_composition
  rw [abs_lt] at hu hv ⊢
  have hu1 : -1 < u := hu.1
  have hu2 : u < 1 := hu.2
  have hv1 : -1 < v := hv.1
  have hv2 : v < 1 := hv.2
  have h_denom_pos : 1 + u * v > 0 := by nlinarith
  have h_denom_ne : 1 + u * v ≠ 0 := ne_of_gt h_denom_pos
  constructor
  · -- -1 < (u + v) / (1 + u*v)
    have h_num : -(1 + u * v) < u + v := by nlinarith
    calc -1 = -(1 + u * v) / (1 + u * v) := by field_simp
      _ < (u + v) / (1 + u * v) := by
          apply div_lt_div_of_pos_right h_num h_denom_pos
  · rw [div_lt_one h_denom_pos]
    nlinarith

/-! ## The Lorentz Covariance Correspondence -/

/-- **The Lorentz Covariance Correspondence** (Summary Theorem)

    This theorem collects the key results about Lorentz transformations:

    1. Invariant mass preserved: E'² - p'² = E² - p²
    2. Lightlike preserved: E = p ⟹ E' = p'
    3. Doppler effect: E' = E × D(v) for lightlike particles
    4. Subluminal composition: |u| < 1 ∧ |v| < 1 ⟹ |u ⊕ v| < 1

    Physical interpretation: Diaspora's kinematics is fully Lorentz covariant.
    Different observers see different energies and momenta, but they all agree
    on the invariant mass and the lightlike nature of single cycles.

    The Doppler effect explains how topology "looks different" from different
    frames: a heavy cycle (small n) to one observer appears lighter (larger
    effective wavelength) to a receding observer. But the topology itself—
    the winding number, the harmonic content—is frame-independent. -/
theorem the_lorentz_covariance_correspondence (v : ℝ) (hv : |v| < 1) :
    -- 1. γ at rest is 1
    (γ 0 = 1) ∧
    -- 2. γ ≥ 1 for all velocities
    (γ v ≥ 1) ∧
    -- 3. Invariant mass preserved (example with E = p = 1)
    (boost_energy 1 1 v)^2 - (boost_momentum 1 1 v)^2 = 0 ∧
    -- 4. Lightlike preserved
    (boost_energy 1 1 v = boost_momentum 1 1 v) ∧
    -- 5. Doppler at rest is 1
    (doppler_factor 0 = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact γ_at_zero
  · exact γ_ge_one v hv
  · have h := invariant_mass_preserved 1 1 v hv
    simp at h ⊢
    exact h
  · exact lightlike_preserved 1 1 v rfl
  · exact doppler_at_zero

end Diaspora.Dynamics.LorentzTransform
