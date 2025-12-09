import Diaspora.Dynamics.ScatteringTheory
import Diaspora.Dynamics.SameDirectionNonInteraction
import Diaspora.Dynamics.LorentzTransform

/-!
# Lorentz Covariance of Scattering: Frame-Independence of Topological Dynamics

This file proves that the kinematic rigidity of scattering is frame-independent:
all inertial observers agree on which scattering events are valid and on the outcome.

## The Core Question

The scattering theory (ScatteringTheory.lean) proves in some implicit "rest frame":
- Opposite-direction scattering preserves individual cycle lengths
- Same-direction scattering is impossible (no CM frame)

But does a boosted observer agree? They see:
- Different energies (Doppler shifted)
- Different momenta
- Do they reach the same conclusions?

## The Answer: Yes

The key insight is that Lorentz transformations act on kinematics (E, p), not topology (n).

1. **Conservation laws are covariant**: A boost maps conservation equations to conservation
   equations. If (E₁ + E₂ = E₁' + E₂', p₁ + p₂ = p₁' + p₂') holds, so does the boosted version.

2. **Cycle lengths are topological invariants**: The integer n (winding number) is not a
   kinematic quantity—it's the topology of the cycle. All observers see the same n.

3. **Lightlike condition is invariant**: m² = E² - p² = 0 is preserved by boosts.
   Same-direction systems remain lightlike in all frames.

## Main Results

- `energy_conservation_covariant`: Energy conservation transforms covariantly
- `momentum_conservation_covariant`: Momentum conservation transforms covariantly
- `scattering_validity_frame_independent`: Valid scattering in one frame ⟹ valid in all
- `cycle_length_is_lorentz_scalar`: n is the same for all observers
- `no_cm_frame_is_lorentz_invariant`: If no CM frame in S, no CM frame in S'
- `scattering_conclusion_frame_independent`: n₁ = n₁' holds for all observers

## Physical Interpretation

Different observers see different "snapshots" of the same physics:
- A receding observer sees all cycles redshifted (lower energy)
- An approaching observer sees all cycles blueshifted (higher energy)
- But all observers agree on cycle lengths, scattering validity, and outcomes

This is the relativistic principle for Diaspora: the laws of topological physics
are the same in all inertial frames.
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

/-- **Energy conservation is Lorentz covariant**.

    If E_initial = E_final in frame S, then E'_initial = E'_final in frame S'.

    This is because the Lorentz transformation is linear:
    E' = γ(E - vp), so if E₁ + E₂ = E₁' + E₂' and p₁ + p₂ = p₁' + p₂',
    then γ[(E₁ - vp₁) + (E₂ - vp₂)] = γ[(E₁' - vp₁') + (E₂' - vp₂')]. -/
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

/-- **Momentum conservation is Lorentz covariant**.

    If p_initial = p_final in frame S, then p'_initial = p'_final in frame S'.

    Same logic as energy: p' = γ(p - vE), so linearity preserves conservation. -/
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

/-- **Scattering validity transforms covariantly**.

    If a scattering event satisfies conservation in frame S,
    it satisfies conservation in any boosted frame S'.

    This is the content of the two covariance theorems above:
    (E-conserved ∧ p-conserved) in S ⟹ (E'-conserved ∧ p'-conserved) in S'. -/
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

/-- **Cycle length is NOT a kinematic quantity**.

    The integer n (the number of vertices in a cycle) is a topological invariant.
    It doesn't transform under Lorentz boosts—all observers see the same n.

    What DOES transform is the energy E = 1/n and momentum p = 1/n.
    A Doppler shift changes the observed E and p, but 1/E = 1/p = n always. -/
theorem cycle_length_is_lorentz_scalar (n : ℕ) (h : n ≥ 3) (v : ℝ) (hv : |v| < 1) :
    -- The boosted energy E' satisfies 1/E' ≠ n in general (Doppler shifted)
    -- But the TOPOLOGY (the integer n) is the same for all observers
    -- We express this as: if you know E and the Doppler factor, you can recover n
    boost_energy (mass_of_cycle n) (momentum n) v =
    mass_of_cycle n * doppler_factor v := by
  exact cycle_doppler_energy n h v hv

/-- **Recovering cycle length from boosted energy**.

    Given the boosted energy E' and the Doppler factor D(v), you can compute:
    E = E'/D(v) and then n = 1/E.

    All observers, despite seeing different energies, can agree on n. -/
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

/-- **Lightlike systems remain lightlike under boosts**.

    If E = p (lightlike) in frame S, then E' = p' in frame S'.
    This is already proven in LorentzTransform.lean as `lightlike_preserved`. -/
theorem lightlike_invariant (E p v : ℝ) (h : E = p) :
    boost_energy E p v = boost_momentum E p v :=
  lightlike_preserved E p v h

/-- **Same-direction pairs are lightlike in all frames**.

    A same-direction pair has m² = 0 in one frame.
    Since m² is Lorentz invariant, m² = 0 in ALL frames.
    Therefore, the system is lightlike for all observers. -/
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

/-- **"No CM frame" is a Lorentz-invariant statement**.

    If a system has m² = 0, then:
    1. Its "CM velocity" is c in every frame
    2. No boost can bring it to rest

    This is because m² = 0 is Lorentz invariant.

    Physical interpretation: All observers agree that same-direction
    lightlike systems cannot be brought to rest. -/
theorem no_cm_frame_invariant (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (v : ℝ) (hv : |v| < 1) :
    -- In the boosted frame, the system is still lightlike
    let E := same_direction_total_energy n₁ n₂
    let p := same_direction_total_momentum n₁ n₂
    (boost_energy E p v)^2 - (boost_momentum E p v)^2 = 0 ∧
    -- Therefore there's still no CM frame for the boosted observer
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
    -- Composing boosts: first by v, then by u
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

/-- **The scattering conclusion is frame-independent**.

    The theorem "opposite-direction scattering preserves cycle lengths" (n₁ = n₁')
    is a statement about TOPOLOGY, not about KINEMATICS.

    Since cycle lengths are Lorentz scalars (they don't transform),
    all observers agree that valid scattering preserves cycle lengths.

    This theorem makes this explicit: if scattering is valid in one frame,
    the preservation of cycle lengths holds in that frame, and since
    cycle lengths are frame-independent, the conclusion is universal. -/
theorem scattering_preservation_frame_independent (n₁ n₂ n₁' n₂' : ℕ)
    (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h₁' : n₁' ≥ 3) (h₂' : n₂' ≥ 3)
    (h_valid : is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 (-1)) :
    -- The conclusion n₁ = n₁' ∧ n₂ = n₂' is a topological statement
    -- that holds regardless of which frame we work in
    (n₁ = n₁' ∧ n₂ = n₂') ∧
    -- And for any boost, the boosted conservation laws also hold
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
    -- Extract conservation laws from h_valid
    have h_E := h_valid.1
    have h_p := h_valid.2
    unfold energy_conserved cycle_energy at h_E
    unfold momentum_conserved signed_cycle_momentum cycle_momentum_magnitude at h_p
    simp only [Int.cast_one, one_mul, Int.cast_neg, neg_mul] at h_p
    -- Apply covariance
    have h_covariant := energy_conservation_covariant
          (mass_of_cycle n₁) (mass_of_cycle n₂)
          (mass_of_cycle n₁') (mass_of_cycle n₂')
          (momentum n₁) (-(momentum n₂))
          (momentum n₁') (-(momentum n₂')) v
    apply h_covariant
    · exact h_E
    · exact h_p

/-! ## The Lorentz Covariance of Scattering Correspondence -/

/-- **The Lorentz Covariance of Scattering Correspondence** (Grand Unification)

    This theorem unifies all frame-independence results:

    1. **Conservation laws are covariant**: Energy and momentum conservation
       transform correctly under Lorentz boosts.

    2. **Cycle lengths are Lorentz scalars**: The topology n is the same
       for all observers; only E = 1/n and p = 1/n get Doppler shifted.

    3. **Lightlike condition is invariant**: Same-direction pairs have m² = 0
       in all frames.

    4. **"No CM frame" is frame-independent**: All observers agree that
       same-direction pairs cannot be brought to rest.

    5. **Scattering rigidity is universal**: The conclusion "n₁ = n₁'"
       from opposite-direction scattering holds for all observers.

    Physical interpretation: Diaspora's scattering physics respects the
    principle of relativity. Different observers see different energies
    and momenta, but they all agree on:
    - Which scattering events are valid
    - The topological outcome (preserved cycle lengths)
    - The impossibility of same-direction scattering
    - The structure of the mass spectrum -/
theorem the_lorentz_covariance_of_scattering_correspondence (n : ℕ) (h : n ≥ 3) (v : ℝ) (hv : |v| < 1) :
    -- 1. Boosted energy can be expressed via Doppler
    (boost_energy (mass_of_cycle n) (momentum n) v = mass_of_cycle n * doppler_factor v) ∧
    -- 2. Cycle length is recoverable from boosted energy
    (boost_energy (mass_of_cycle n) (momentum n) v / doppler_factor v = mass_of_cycle n) ∧
    -- 3. Single cycles remain lightlike
    (boost_energy (mass_of_cycle n) (momentum n) v =
     boost_momentum (mass_of_cycle n) (momentum n) v) ∧
    -- 4. Same-direction pairs are lightlike in all frames
    ((boost_energy (same_direction_total_energy n n) (same_direction_total_momentum n n) v)^2 -
     (boost_momentum (same_direction_total_energy n n) (same_direction_total_momentum n n) v)^2 = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact cycle_doppler_energy n h v hv
  · exact cycle_length_recoverable n h v hv
  · exact cycle_lightlike_after_boost n h v hv
  · exact same_direction_lightlike_all_frames n n h h v hv

/-! ## The Center-of-Mass Frame for Timelike Systems -/

/-- **The CM boost velocity for opposite-direction pairs**.

    For two cycles with opposite orientations, the CM frame is reached
    by boosting with velocity v_CM = p/E.

    For cycles n₁ and n₂:
    - E = 1/n₁ + 1/n₂
    - p = 1/n₁ - 1/n₂ (opposite directions subtract)
    - v_CM = (n₂ - n₁)/(n₁ + n₂)

    This is subluminal (|v_CM| < 1) for any finite n₁, n₂ ≥ 3. -/
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

/-- **The Center-of-Mass Frame Exists for Opposite-Direction Pairs**.

    Unlike same-direction pairs (which have no CM frame), opposite-direction
    pairs CAN be boosted to a frame where the total momentum is zero.

    This is the fundamental difference between:
    - Lightlike systems (m² = 0): no rest frame, v_CM = c
    - Timelike systems (m² > 0): rest frame exists, v_CM < c

    The CM velocity v = p/E = (1/n₁ - 1/n₂)/(1/n₁ + 1/n₂) = (n₂ - n₁)/(n₁ + n₂)
    is always subluminal, so the boost is well-defined. -/
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
    -- Goal: γ * (p - v * E) = 0 where p = 1/n₁ - 1/n₂, E = 1/n₁ + 1/n₂, v = (n₂ - n₁)/(n₁ + n₂)
    -- p - v * E = (1/n₁ - 1/n₂) - ((n₂ - n₁)/(n₁ + n₂)) * (1/n₁ + 1/n₂)
    -- The inner part: ((n₂ - n₁)/(n₁ + n₂)) * (1/n₁ + 1/n₂) = ((n₂ - n₁)/(n₁ + n₂)) * (n₁ + n₂)/(n₁ * n₂)
    --               = (n₂ - n₁) / (n₁ * n₂) = 1/n₁ - 1/n₂
    -- So p - v * E = (1/n₁ - 1/n₂) - (1/n₁ - 1/n₂) = 0
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

/-- **The Dichotomy**: Same-direction has no CM frame, opposite-direction does.

    This is the fundamental kinematic difference that determines:
    - Whether scattering can occur (requires a CM frame)
    - Whether binding is possible (requires counter-propagation)
    - Whether the system can be "at rest"

    Mathematically:
    - Same-direction: m² = 0 (lightlike) ⟹ no CM frame
    - Opposite-direction: m² > 0 (timelike) ⟹ CM frame exists -/
theorem cm_frame_dichotomy (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    -- Same-direction: no CM frame exists
    (¬∃ v : ℝ, |v| < 1 ∧
      boost_momentum (same_direction_total_energy n₁ n₂)
                     (same_direction_total_momentum n₁ n₂) v = 0) ∧
    -- Opposite-direction: CM frame exists
    (∃ v : ℝ, |v| < 1 ∧
      boost_momentum (two_cycle_energy n₁ n₂ 0)
                     (two_cycle_momentum n₁ n₂ 1 (-1)) v = 0) := by
  constructor
  · exact no_center_of_mass_frame n₁ n₂ h₁ h₂
  · exact ⟨opposite_direction_cm_velocity n₁ n₂,
          opposite_direction_cm_frame_exists n₁ n₂ h₁ h₂⟩

end Diaspora.Dynamics.LorentzCovariance
