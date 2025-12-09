import Diaspora.Dynamics.ScatteringTheory
import Diaspora.Dynamics.SameDirectionNonInteraction
import Diaspora.Dynamics.LorentzTransform

/-!
# Lorentz Covariance of Scattering

Scattering validity and cycle length preservation are frame-independent.
-/

namespace Diaspora.Dynamics.LorentzCovariance

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.Dispersion
open Diaspora.Dynamics.InvariantMass
open Diaspora.Dynamics.ScatteringTheory
open Diaspora.Dynamics.SameDirectionNonInteraction
open Diaspora.Dynamics.LorentzTransform

/-! ## Covariance of Conservation Laws -/

/-- Energy conservation is Lorentz covariant. -/
theorem energy_conservation_covariant
    (E₁ E₂ E₁' E₂' p₁ p₂ p₁' p₂' : ℝ) (v : ℝ)
    (hE : E₁ + E₂ = E₁' + E₂')
    (hp : p₁ + p₂ = p₁' + p₂') :
    boost_energy E₁ p₁ v + boost_energy E₂ p₂ v =
    boost_energy E₁' p₁' v + boost_energy E₂' p₂' v := by
  unfold boost_energy
  calc γ v * (E₁ - v * p₁) + γ v * (E₂ - v * p₂)
      = γ v * ((E₁ + E₂) - v * (p₁ + p₂)) := by ring
    _ = γ v * ((E₁' + E₂') - v * (p₁' + p₂')) := by rw [hE, hp]
    _ = γ v * (E₁' - v * p₁') + γ v * (E₂' - v * p₂') := by ring

/-- Momentum conservation is Lorentz covariant. -/
theorem momentum_conservation_covariant
    (E₁ E₂ E₁' E₂' p₁ p₂ p₁' p₂' : ℝ) (v : ℝ)
    (hE : E₁ + E₂ = E₁' + E₂')
    (hp : p₁ + p₂ = p₁' + p₂') :
    boost_momentum E₁ p₁ v + boost_momentum E₂ p₂ v =
    boost_momentum E₁' p₁' v + boost_momentum E₂' p₂' v := by
  unfold boost_momentum
  calc γ v * (p₁ - v * E₁) + γ v * (p₂ - v * E₂)
      = γ v * ((p₁ + p₂) - v * (E₁ + E₂)) := by ring
    _ = γ v * ((p₁' + p₂') - v * (E₁' + E₂')) := by rw [hE, hp]
    _ = γ v * (p₁' - v * E₁') + γ v * (p₂' - v * E₂') := by ring

/-! ## Scattering Validity is Frame-Independent -/

/-- Scattering validity transforms covariantly. -/
theorem scattering_validity_covariant
    (E₁ E₂ E₁' E₂' p₁ p₂ p₁' p₂' : ℝ) (v : ℝ)
    (hE : E₁ + E₂ = E₁' + E₂')
    (hp : p₁ + p₂ = p₁' + p₂') :
    (boost_energy E₁ p₁ v + boost_energy E₂ p₂ v =
     boost_energy E₁' p₁' v + boost_energy E₂' p₂' v) ∧
    (boost_momentum E₁ p₁ v + boost_momentum E₂ p₂ v =
     boost_momentum E₁' p₁' v + boost_momentum E₂' p₂' v) := by
  exact ⟨energy_conservation_covariant E₁ E₂ E₁' E₂' p₁ p₂ p₁' p₂' v hE hp,
         momentum_conservation_covariant E₁ E₂ E₁' E₂' p₁ p₂ p₁' p₂' v hE hp⟩

/-! ## Cycle Length is a Lorentz Scalar -/

/-- Cycle length is a topological invariant (Lorentz scalar). -/
theorem cycle_length_is_lorentz_scalar (n : ℕ) (h : n ≥ 3) (v : ℝ) (hv : |v| < 1) :
    boost_energy (mass_of_cycle n) (momentum n) v =
    mass_of_cycle n * doppler_factor v := by
  exact cycle_doppler_energy n h v hv

/-- Cycle length is recoverable from boosted energy via Doppler factor. -/
theorem cycle_length_recoverable (n : ℕ) (h : n ≥ 3) (v : ℝ) (hv : |v| < 1) :
    let E' := boost_energy (mass_of_cycle n) (momentum n) v
    let D := doppler_factor v
    E' / D = mass_of_cycle n := by
  simp only
  rw [cycle_doppler_energy n h v hv]
  have hD_pos := doppler_positive v hv
  have hD_ne : doppler_factor v ≠ 0 := ne_of_gt hD_pos
  field_simp [hD_ne]

/-! ## Lightlike Condition is Lorentz Invariant -/

/-- Lightlike systems remain lightlike under boosts. -/
theorem lightlike_invariant (E p v : ℝ) (h : E = p) :
    boost_energy E p v = boost_momentum E p v :=
  lightlike_preserved E p v h

/-- Same-direction pairs are lightlike in all frames. -/
theorem same_direction_lightlike_all_frames (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (v : ℝ) (hv : |v| < 1) :
    let E := same_direction_total_energy n₁ n₂
    let p := same_direction_total_momentum n₁ n₂
    let E' := boost_energy E p v
    let p' := boost_momentum E p v
    E'^2 - p'^2 = 0 := by
  simp only
  have h_lightlike := same_direction_lightlike_dispersion n₁ n₂ h₁ h₂
  have h_preserved := invariant_mass_preserved
        (same_direction_total_energy n₁ n₂)
        (same_direction_total_momentum n₁ n₂) v hv
  rw [h_preserved]
  exact same_direction_system_lightlike n₁ n₂ h₁ h₂

/-! ## No CM Frame is Lorentz Invariant -/

/-- "No CM frame" is a Lorentz-invariant statement. -/
theorem no_cm_frame_invariant (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (v : ℝ) (hv : |v| < 1) :
    let E := same_direction_total_energy n₁ n₂
    let p := same_direction_total_momentum n₁ n₂
    (boost_energy E p v)^2 - (boost_momentum E p v)^2 = 0 ∧
    (∀ u : ℝ, |u| < 1 →
      let E' := boost_energy E p v
      let p' := boost_momentum E p v
      let E'' := boost_energy E' p' u
      let p'' := boost_momentum E' p' u
      E''^2 - p''^2 = 0) := by
  constructor
  · exact same_direction_lightlike_all_frames n₁ n₂ h₁ h₂ v hv
  · intro u hu
    simp only
    have h_first := invariant_mass_preserved
          (same_direction_total_energy n₁ n₂)
          (same_direction_total_momentum n₁ n₂) v hv
    have h_second := invariant_mass_preserved
          (boost_energy (same_direction_total_energy n₁ n₂)
                        (same_direction_total_momentum n₁ n₂) v)
          (boost_momentum (same_direction_total_energy n₁ n₂)
                          (same_direction_total_momentum n₁ n₂) v) u hu
    rw [h_second, h_first]
    exact same_direction_system_lightlike n₁ n₂ h₁ h₂

/-! ## Scattering Conclusions are Frame-Independent -/

/-- Scattering preservation is frame-independent. -/
theorem scattering_preservation_frame_independent (n₁ n₂ n₁' n₂' : ℕ)
    (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h₁' : n₁' ≥ 3) (h₂' : n₂' ≥ 3)
    (h_valid : is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 (-1)) :
    (n₁ = n₁' ∧ n₂ = n₂') ∧
    (∀ v : ℝ, |v| < 1 →
      let E₁ := mass_of_cycle n₁
      let E₂ := mass_of_cycle n₂
      let E₁' := mass_of_cycle n₁'
      let E₂' := mass_of_cycle n₂'
      let p₁ := momentum n₁
      let p₂ := -(momentum n₂)  -- opposite direction
      let p₁' := momentum n₁'
      let p₂' := -(momentum n₂')
      boost_energy E₁ p₁ v + boost_energy E₂ p₂ v =
      boost_energy E₁' p₁' v + boost_energy E₂' p₂' v) := by
  constructor
  · exact opposite_direction_individual_preservation n₁ n₂ n₁' n₂' h₁ h₂ h₁' h₂' h_valid
  · intro v _hv
    have h_E := h_valid.1
    have h_p := h_valid.2
    unfold energy_conserved cycle_energy at h_E
    unfold momentum_conserved signed_cycle_momentum cycle_momentum_magnitude at h_p
    simp only [Int.cast_one, one_mul, Int.cast_neg, neg_mul] at h_p
    have h_covariant := energy_conservation_covariant
          (mass_of_cycle n₁) (mass_of_cycle n₂)
          (mass_of_cycle n₁') (mass_of_cycle n₂')
          (momentum n₁) (-(momentum n₂))
          (momentum n₁') (-(momentum n₂')) v
    apply h_covariant
    · exact h_E
    · exact h_p

/-! ## The Lorentz Covariance of Scattering Correspondence -/

/-- Unified Lorentz covariance: Doppler, recoverability, lightlike preservation. -/
theorem the_lorentz_covariance_of_scattering_correspondence (n : ℕ) (h : n ≥ 3) (v : ℝ) (hv : |v| < 1) :
    (boost_energy (mass_of_cycle n) (momentum n) v = mass_of_cycle n * doppler_factor v) ∧
    (boost_energy (mass_of_cycle n) (momentum n) v / doppler_factor v = mass_of_cycle n) ∧
    (boost_energy (mass_of_cycle n) (momentum n) v =
     boost_momentum (mass_of_cycle n) (momentum n) v) ∧
    ((boost_energy (same_direction_total_energy n n) (same_direction_total_momentum n n) v)^2 -
     (boost_momentum (same_direction_total_energy n n) (same_direction_total_momentum n n) v)^2 = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact cycle_doppler_energy n h v hv
  · exact cycle_length_recoverable n h v hv
  · exact cycle_lightlike_after_boost n h v hv
  · exact same_direction_lightlike_all_frames n n h h v hv

/-! ## The Center-of-Mass Frame for Timelike Systems -/

/-- CM boost velocity for opposite-direction pairs: v_CM = (n₂ - n₁)/(n₁ + n₂). -/
noncomputable def opposite_direction_cm_velocity (n₁ n₂ : ℕ) : ℝ :=
  ((n₂ : ℝ) - n₁) / (n₁ + n₂)

/-- The CM velocity for opposite-direction pairs is subluminal. -/
theorem opposite_direction_cm_subluminal (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    |opposite_direction_cm_velocity n₁ n₂| < 1 := by
  unfold opposite_direction_cm_velocity
  have hn₁_pos : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂_pos : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_sum_pos : (n₁ : ℝ) + n₂ > 0 := by linarith
  rw [abs_div, abs_of_pos h_sum_pos]
  rw [div_lt_one h_sum_pos]
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-- CM frame exists for opposite-direction pairs (timelike, m² > 0). -/
theorem opposite_direction_cm_frame_exists (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    let v := opposite_direction_cm_velocity n₁ n₂
    let E := two_cycle_energy n₁ n₂ 0
    let p := two_cycle_momentum n₁ n₂ 1 (-1)
    |v| < 1 ∧ boost_momentum E p v = 0 := by
  constructor
  · exact opposite_direction_cm_subluminal n₁ n₂ h₁ h₂
  · unfold boost_momentum opposite_direction_cm_velocity
    unfold two_cycle_energy two_cycle_momentum signed_momentum momentum mass_of_cycle
    simp only [sub_zero, Int.cast_one, Int.cast_neg, one_mul, neg_mul, one_div]
    have hn₁ : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hn₂ : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hn₁_pos : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    have hn₂_pos : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    have h_sum_ne : (n₁ : ℝ) + n₂ ≠ 0 := by linarith
    have h_key : (n₁ : ℝ)⁻¹ + -(n₂ : ℝ)⁻¹ - ((n₂ : ℝ) - n₁) / (n₁ + n₂) * ((n₁ : ℝ)⁻¹ + (n₂ : ℝ)⁻¹) = 0 := by
      field_simp [hn₁, hn₂, h_sum_ne]
      ring
    rw [mul_comm (γ _), mul_eq_zero]
    left
    exact h_key

/-- In the CM frame, the total momentum is zero. -/
theorem cm_frame_momentum_zero (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    boost_momentum (two_cycle_energy n₁ n₂ 0)
                   (two_cycle_momentum n₁ n₂ 1 (-1))
                   (opposite_direction_cm_velocity n₁ n₂) = 0 :=
  (opposite_direction_cm_frame_exists n₁ n₂ h₁ h₂).2

/-- Dichotomy: same-direction (lightlike) has no CM frame; opposite-direction (timelike) does. -/
theorem cm_frame_dichotomy (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    (¬∃ v : ℝ, |v| < 1 ∧
      boost_momentum (same_direction_total_energy n₁ n₂)
                     (same_direction_total_momentum n₁ n₂) v = 0) ∧
    (∃ v : ℝ, |v| < 1 ∧
      boost_momentum (two_cycle_energy n₁ n₂ 0)
                     (two_cycle_momentum n₁ n₂ 1 (-1)) v = 0) := by
  constructor
  · exact no_center_of_mass_frame n₁ n₂ h₁ h₂
  · exact ⟨opposite_direction_cm_velocity n₁ n₂,
          opposite_direction_cm_frame_exists n₁ n₂ h₁ h₂⟩

end Diaspora.Dynamics.LorentzCovariance
