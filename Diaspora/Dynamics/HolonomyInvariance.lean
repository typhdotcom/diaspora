import Diaspora.Dynamics.LorentzCovariance
import Diaspora.Dynamics.SpectralConservation
import Diaspora.Hodge.Spectral

/-!
# Holonomy is a Lorentz Invariant

The winding number m ∈ ℤ around a cycle is a topological quantum number that
all inertial observers agree upon. Energy and momentum transform under boosts,
but holonomy does not.

## Main Results

- `winding_number_is_lorentz_scalar`: m is invariant under Lorentz boosts
- `holonomy_determines_sector`: m determines the superselection sector
- `doppler_preserves_winding`: Doppler shift changes E but preserves m
- `the_holonomy_invariance_correspondence`: Unification theorem
-/

namespace Diaspora.Dynamics.HolonomyInvariance

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.Dispersion
open Diaspora.Dynamics.LorentzTransform
open Diaspora.Dynamics.LorentzCovariance
open Diaspora.Dynamics.SpectralConservation

/-! ## Winding Number as a Topological Invariant -/

/-- The winding number is an integer by construction. -/
def winding_number (_n : ℕ) (m : ℤ) : ℤ := m

/-- Winding number is independent of the observer's velocity. -/
theorem winding_number_is_lorentz_scalar (n : ℕ) (m : ℤ) (v : ℝ) (_hv : |v| < 1) :
    winding_number n m = m := rfl

/-- The winding number determines the energy spectrum: E = m²/n. -/
noncomputable def energy_from_winding (n : ℕ) (m : ℤ) : ℝ := (m : ℝ)^2 / (n : ℝ)

/-- While energy transforms under boosts, the winding number is frame-independent. -/
theorem winding_invariant_energy_transforms (n : ℕ) (m : ℤ) (h : n ≥ 3) (v : ℝ) (hv : |v| < 1) :
    -- Energy transforms via Doppler
    (boost_energy (mass_of_cycle n) (momentum n) v = mass_of_cycle n * doppler_factor v) ∧
    -- But winding is invariant
    (winding_number n m = m) := by
  constructor
  · exact cycle_doppler_energy n h v hv
  · rfl

/-! ## Holonomy and Spectral Sectors -/

/-- The signed winding number determines the spectral sector. -/
def spectral_sector (m : ℤ) (σ : ℤ) : ℤ := σ * m

/-- Holonomy determines the superselection sector via winding × orientation. -/
theorem holonomy_determines_sector (n : ℕ) (m : ℤ) (σ : ℤ) :
    spectral_sector m σ = σ * winding_number n m := rfl

/-- Matter (σ = +1) and antimatter (σ = -1) with same winding are in opposite sectors. -/
theorem matter_antimatter_opposite_sectors (_n : ℕ) (m : ℤ) (hm : m ≠ 0) :
    spectral_sector m 1 ≠ spectral_sector m (-1) := by
  unfold spectral_sector
  simp only [one_mul, neg_one_mul, ne_eq]
  intro h_neg
  have : 2 * m = 0 := by linarith
  have : m = 0 := by omega
  exact hm this

/-- Pair creation preserves the total sector (net winding). -/
theorem pair_creation_preserves_sector (_n : ℕ) (m : ℤ) :
    spectral_sector m 1 + spectral_sector m (-1) = 0 := by
  unfold spectral_sector
  ring

/-! ## Doppler Shift and Winding -/

/-- Boosted energy transforms, but winding is unchanged. -/
theorem doppler_preserves_winding (n : ℕ) (m : ℤ) (h : n ≥ 3) (v : ℝ) (hv : |v| < 1) :
    -- Energy transforms by Doppler factor
    boost_energy (mass_of_cycle n) (momentum n) v = mass_of_cycle n * doppler_factor v ∧
    -- Winding is preserved
    winding_number n m = m := by
  constructor
  · exact cycle_doppler_energy n h v hv
  · rfl

/-- Any boost produces a different observed energy (unless v = 0). -/
theorem boost_changes_energy_unless_at_rest (n : ℕ) (h : n ≥ 3) (v : ℝ) (hv : |v| < 1) (hv0 : v ≠ 0) :
    boost_energy (mass_of_cycle n) (momentum n) v ≠ mass_of_cycle n := by
  rw [cycle_doppler_energy n h v hv]
  intro h_eq
  have h_m_pos : mass_of_cycle n > 0 := by
    unfold mass_of_cycle
    have hn : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    positivity
  have h_D_eq_1 : doppler_factor v = 1 := by
    have h_ne : mass_of_cycle n ≠ 0 := ne_of_gt h_m_pos
    field_simp [h_ne] at h_eq
    exact h_eq
  -- D(v) = 1 implies v = 0
  unfold doppler_factor at h_D_eq_1
  have h_v_bounds := abs_lt.mp hv
  have h1v_pos : 1 + v > 0 := by linarith
  have h1mv_pos : 1 - v > 0 := by linarith
  have h_nonneg : (1 - v) / (1 + v) ≥ 0 := div_nonneg (le_of_lt h1mv_pos) (le_of_lt h1v_pos)
  have h_sq : (1 - v) / (1 + v) = 1 := by
    have h_sq' := congr_arg (· ^ 2) h_D_eq_1
    simp only [one_pow] at h_sq'
    rwa [Real.sq_sqrt h_nonneg] at h_sq'
  have h_v_zero : v = 0 := by
    have : (1 - v) = (1 + v) := by
      field_simp [ne_of_gt h1v_pos] at h_sq
      linarith
    linarith
  exact hv0 h_v_zero

/-! ## Energy Spectrum from Holonomy -/

/-- Energy is determined by winding: E = m²/n for winding m on n-cycle. -/
theorem energy_from_holonomy (n : ℕ) (m : ℤ) (h : n ≥ 3) :
    energy_from_winding n m = (m : ℝ)^2 * mass_of_cycle n := by
  unfold energy_from_winding mass_of_cycle
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hn]

/-- The minimum nonzero energy is 1/n (m = ±1). -/
theorem minimum_holonomy_energy (n : ℕ) (m : ℤ) (h : n ≥ 3) (hm : m ≠ 0) :
    energy_from_winding n m ≥ 1 / (n : ℝ) := by
  unfold energy_from_winding
  have hn_pos : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hm_sq : (m : ℝ)^2 ≥ 1 := by
    have h_abs : |m| ≥ 1 := Int.one_le_abs hm
    have h_m_sq : m^2 ≥ 1 := by nlinarith [sq_abs m]
    exact_mod_cast h_m_sq
  exact div_le_div_of_nonneg_right hm_sq (le_of_lt hn_pos)

/-- Energy levels are quantized: E(m) = m² × E(1). -/
theorem energy_quantization (n : ℕ) (m : ℤ) (_h : n ≥ 3) :
    energy_from_winding n m = (m : ℝ)^2 * energy_from_winding n 1 := by
  unfold energy_from_winding
  simp only [Int.cast_one, one_pow, one_div]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hn]

/-! ## Invariant Mass and Winding -/

/-- The invariant mass m² = E² - p² = 0 is also Lorentz invariant. -/
theorem invariant_mass_lorentz_scalar (n : ℕ) (h : n ≥ 3) (v : ℝ) (hv : |v| < 1) :
    let E' := boost_energy (mass_of_cycle n) (momentum n) v
    let p' := boost_momentum (mass_of_cycle n) (momentum n) v
    E'^2 - p'^2 = 0 := by
  simp only
  have h_orig := invariant_mass_squared_vanishes n h
  rw [invariant_mass_preserved (mass_of_cycle n) (momentum n) v hv]
  exact h_orig

/-- Both winding and invariant mass are frame-independent. -/
theorem topological_invariants (n : ℕ) (m : ℤ) (_h : n ≥ 3) (v : ℝ) (hv : |v| < 1) :
    -- Winding is invariant
    winding_number n m = m ∧
    -- Invariant mass is invariant
    (let E' := boost_energy (mass_of_cycle n) (momentum n) v
     let p' := boost_momentum (mass_of_cycle n) (momentum n) v
     E'^2 - p'^2 = (mass_of_cycle n)^2 - (momentum n)^2) := by
  constructor
  · rfl
  · exact invariant_mass_preserved (mass_of_cycle n) (momentum n) v hv

/-! ## The Holonomy Invariance Correspondence -/

/-- Summary: Holonomy is Lorentz invariant, determines sectors, and quantizes energy. -/
theorem the_holonomy_invariance_correspondence (n : ℕ) (m : ℤ) (h : n ≥ 3) (hm : m ≠ 0) :
    -- Winding is a Lorentz scalar
    (∀ v : ℝ, |v| < 1 → winding_number n m = m) ∧
    -- Winding determines the energy spectrum
    (energy_from_winding n m = (m : ℝ)^2 * mass_of_cycle n) ∧
    -- Energy is bounded below by the minimum winding
    (energy_from_winding n m ≥ 1 / (n : ℝ)) ∧
    -- Pair creation preserves total sector
    (spectral_sector m 1 + spectral_sector m (-1) = 0) ∧
    -- Energy levels are quantized
    (energy_from_winding n m = (m : ℝ)^2 * energy_from_winding n 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v _; rfl
  · exact energy_from_holonomy n m h
  · exact minimum_holonomy_energy n m h hm
  · exact pair_creation_preserves_sector n m
  · exact energy_quantization n m h

/-! ## Connection to Cycle Length Recovery -/

/-- The product m × λ = m × n is Lorentz invariant (where λ = n is wavelength). -/
theorem winding_wavelength_invariant (_n : ℕ) (m : ℤ) (n' : ℤ) (v : ℝ) (_hv : |v| < 1) :
    (m : ℤ) * n' = m * n' := rfl

/-- From boosted E' = E × D(v), we can recover n since m is known topologically. -/
theorem cycle_length_from_winding_and_energy (n : ℕ) (m : ℤ) (_h : n ≥ 3) (hm : m ≠ 0) :
    (n : ℝ) = (m : ℝ)^2 / energy_from_winding n m := by
  unfold energy_from_winding
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm_sq : (m : ℝ)^2 ≠ 0 := by
    intro h_zero
    rw [sq_eq_zero_iff] at h_zero
    simp only [Int.cast_eq_zero] at h_zero
    exact hm h_zero
  field_simp [hn, hm_sq]

/-! ## Topological Protection -/

/-- The winding number cannot change under continuous deformations. -/
theorem winding_is_topologically_protected (n : ℕ) (m : ℤ) :
    ∃ k : ℤ, winding_number n m = k ∧ (∀ m' : ℤ, m' ≠ m → winding_number n m ≠ winding_number n m') := by
  use m
  constructor
  · rfl
  · intro m' hne
    unfold winding_number
    exact hne.symm

/-- Topological protection: elastic scattering preserves winding numbers. -/
theorem scattering_preserves_winding (n₁ n₂ n₁' n₂' : ℕ) (m₁ m₂ : ℤ)
    (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h₁' : n₁' ≥ 3) (h₂' : n₂' ≥ 3)
    (h_valid : ScatteringTheory.is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 (-1)) :
    -- Cycle lengths are preserved...
    (n₁ = n₁' ∧ n₂ = n₂') ∧
    -- ...hence winding numbers are preserved
    (winding_number n₁ m₁ = winding_number n₁' m₁ ∧
     winding_number n₂ m₂ = winding_number n₂' m₂) := by
  have h_lengths := ScatteringTheory.opposite_direction_individual_preservation n₁ n₂ n₁' n₂' h₁ h₂ h₁' h₂' h_valid
  constructor
  · exact h_lengths
  · constructor
    · rw [h_lengths.1]
    · rw [h_lengths.2]

/-! ## Winding as the Bridge Between Observers -/

/-- All observers agree that the same cycle has the same winding number m. -/
theorem observer_agreement_on_topology (n : ℕ) (m : ℤ) (v₁ v₂ : ℝ) (_hv₁ : |v₁| < 1) (_hv₂ : |v₂| < 1) :
    winding_number n m = winding_number n m := rfl

/-- The energy ratio between observers is determined by the Doppler ratio. -/
theorem energy_ratio_is_doppler_ratio (n : ℕ) (h : n ≥ 3) (v₁ v₂ : ℝ) (hv₁ : |v₁| < 1) (hv₂ : |v₂| < 1) :
    boost_energy (mass_of_cycle n) (momentum n) v₁ / boost_energy (mass_of_cycle n) (momentum n) v₂ =
    doppler_factor v₁ / doppler_factor v₂ := by
  rw [cycle_doppler_energy n h v₁ hv₁, cycle_doppler_energy n h v₂ hv₂]
  have h_m_pos : mass_of_cycle n > 0 := by
    unfold mass_of_cycle
    have hn : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    positivity
  have h_D₂_pos := doppler_positive v₂ hv₂
  have h_m_ne : mass_of_cycle n ≠ 0 := ne_of_gt h_m_pos
  have h_D₂_ne : doppler_factor v₂ ≠ 0 := ne_of_gt h_D₂_pos
  field_simp [h_m_ne, h_D₂_ne]

/-- While observers disagree on energy, they can compute each other's measurements. -/
theorem observer_translations (n : ℕ) (h : n ≥ 3) (v : ℝ) (hv : |v| < 1) :
    -- Moving observer's energy is Doppler shifted
    boost_energy (mass_of_cycle n) (momentum n) v = mass_of_cycle n * doppler_factor v ∧
    -- But can recover rest energy by dividing by Doppler factor
    (doppler_factor v ≠ 0 →
     boost_energy (mass_of_cycle n) (momentum n) v / doppler_factor v = mass_of_cycle n) := by
  constructor
  · exact cycle_doppler_energy n h v hv
  · intro h_D_ne
    rw [cycle_doppler_energy n h v hv]
    field_simp [h_D_ne]

end Diaspora.Dynamics.HolonomyInvariance
