import Diaspora.Dynamics.Dispersion
import Diaspora.Dynamics.InvariantMass

/-!
# Scattering Theory: Rigidity of Topology Under Elastic Collisions

This file proves a striking rigidity theorem: elastic scattering of lightlike cycles
preserves individual cycle lengths. Unlike point particles, topological defects
cannot exchange energy arbitrarily—their sizes are kinematically locked.

## The Central Insight

For two lightlike particles (E = |p|) scattering:
- Energy conservation: E₁ + E₂ = E₁' + E₂'
- Momentum conservation: p₁ + p₂ = p₁' + p₂'

With E = |p|, these become highly constrained. For opposite-direction scattering:

  Adding: 2/n₁ = 2/n₁' → n₁ = n₁'
  Subtracting: 2/n₂ = 2/n₂' → n₂ = n₂'

Individual cycle lengths are preserved—no exchange is possible!

## Main Results

- `opposite_direction_individual_preservation`: Opposite-direction scattering
  preserves individual cycle lengths (no exchange!)
- `no_direction_flip`: Cannot convert opposite-direction to same-direction
- `charge_conservation_in_scattering`: Total signed momentum is conserved

## Physical Interpretation

This rigidity has profound implications:
1. Topology cannot be "traded" between cycles through collisions
2. The discrete spectrum of masses (1/3, 1/4, 1/5, ...) is stable
3. Only pair production/annihilation can change cycle lengths
4. Scattering is purely elastic—no inelastic channels exist!

This contrasts sharply with standard QFT where particles can exchange energy
and momentum freely (subject only to conservation laws). In Diaspora, the
lightlike constraint E = p creates additional rigidity.
-/

namespace Diaspora.Dynamics.ScatteringTheory

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.Dispersion
open Diaspora.Dynamics.InvariantMass

/-! ## Scattering Kinematics -/

/-- The energy of a cycle: E = 1/n. -/
noncomputable def cycle_energy (n : ℕ) : ℝ := mass_of_cycle n

/-- The momentum magnitude of a cycle: p = 1/n.
    Direction is determined by orientation (±1). -/
noncomputable def cycle_momentum_magnitude (n : ℕ) : ℝ := momentum n

/-- The signed momentum of a cycle with orientation σ ∈ {+1, -1}. -/
noncomputable def signed_cycle_momentum (n : ℕ) (σ : ℤ) : ℝ :=
  σ * cycle_momentum_magnitude n

/-! ## Conservation Laws -/

/-- **Energy Conservation**: Total energy is conserved in scattering. -/
def energy_conserved (n₁ n₂ n₁' n₂' : ℕ) : Prop :=
  cycle_energy n₁ + cycle_energy n₂ = cycle_energy n₁' + cycle_energy n₂'

/-- **Momentum Conservation**: Total momentum is conserved in scattering. -/
def momentum_conserved (n₁ n₂ n₁' n₂' : ℕ) (σ₁ σ₂ σ₁' σ₂' : ℤ) : Prop :=
  signed_cycle_momentum n₁ σ₁ + signed_cycle_momentum n₂ σ₂ =
  signed_cycle_momentum n₁' σ₁' + signed_cycle_momentum n₂' σ₂'

/-- A scattering event satisfies both conservation laws. -/
def is_valid_scattering (n₁ n₂ n₁' n₂' : ℕ) (σ₁ σ₂ σ₁' σ₂' : ℤ) : Prop :=
  energy_conserved n₁ n₂ n₁' n₂' ∧ momentum_conserved n₁ n₂ n₁' n₂' σ₁ σ₂ σ₁' σ₂'

/-! ## Opposite-Direction Scattering -/

/-- **The Opposite-Direction Rigidity Theorem**: When two cycles with opposite
    orientations scatter elastically (both staying in opposite directions),
    the individual cycle lengths are preserved.

    This is because:
    - Energy: 1/n₁ + 1/n₂ = 1/n₁' + 1/n₂'
    - Momentum: 1/n₁ - 1/n₂ = 1/n₁' - 1/n₂'

    Adding: 2/n₁ = 2/n₁' → n₁ = n₁'
    Subtracting: 2/n₂ = 2/n₂' → n₂ = n₂'

    Unlike same-direction scattering (where exchange is possible), opposite-direction
    scattering is completely rigid: no energy exchange can occur! -/
theorem opposite_direction_individual_preservation (n₁ n₂ n₁' n₂' : ℕ)
    (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h₁' : n₁' ≥ 3) (h₂' : n₂' ≥ 3)
    (h_valid : is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 (-1)) :
    n₁ = n₁' ∧ n₂ = n₂' := by
  have h_E := h_valid.1
  have h_p := h_valid.2
  unfold energy_conserved cycle_energy mass_of_cycle at h_E
  unfold momentum_conserved signed_cycle_momentum cycle_momentum_magnitude momentum mass_of_cycle at h_p
  simp only [Int.cast_one, one_mul, Int.cast_neg, neg_mul] at h_p
  -- h_E: 1/n₁ + 1/n₂ = 1/n₁' + 1/n₂'
  -- h_p: 1/n₁ - 1/n₂ = 1/n₁' - 1/n₂'
  have hn₁ : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂ : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₁' : (n₁' : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂' : (n₂' : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  -- Add equations: 2/n₁ = 2/n₁'
  have h_add : (1 : ℝ) / n₁ + 1 / n₂ + (1 / n₁ - 1 / n₂) = 1 / n₁' + 1 / n₂' + (1 / n₁' - 1 / n₂') := by
    linarith
  ring_nf at h_add
  have h_n₁_eq : (1 : ℝ) / n₁ = 1 / n₁' := by linarith
  -- Subtract equations: 2/n₂ = 2/n₂'
  have h_sub : (1 : ℝ) / n₁ + 1 / n₂ - (1 / n₁ - 1 / n₂) = 1 / n₁' + 1 / n₂' - (1 / n₁' - 1 / n₂') := by
    linarith
  simp only [add_sub_sub_cancel] at h_sub
  have h_n₂_eq : (1 : ℝ) / n₂ = 1 / n₂' := by linarith
  -- Convert back to natural numbers
  have h₁_real : (n₁ : ℝ) = n₁' := by
    rw [one_div, one_div] at h_n₁_eq
    exact inv_inj.mp h_n₁_eq
  have h₂_real : (n₂ : ℝ) = n₂' := by
    rw [one_div, one_div] at h_n₂_eq
    exact inv_inj.mp h_n₂_eq
  exact ⟨Nat.cast_injective h₁_real, Nat.cast_injective h₂_real⟩

/-! ## No Direction Flipping -/

/-- **No Direction-Flip Theorem**: Opposite-direction pairs cannot scatter into
    same-direction pairs.

    If initial state is (+,-) with p_i = 1/n₁ - 1/n₂,
    and final state is (+,+) with p_f = 1/n₁' + 1/n₂',

    momentum conservation requires: 1/n₁ - 1/n₂ = 1/n₁' + 1/n₂'

    But energy conservation requires: 1/n₁ + 1/n₂ = 1/n₁' + 1/n₂'

    These can only both hold if 1/n₂ = 0, which is impossible.

    Physical interpretation: Charge (orientation) is conserved. You cannot
    convert a matter-antimatter pair into two matter particles. -/
theorem no_direction_flip (n₁ n₂ n₁' n₂' : ℕ)
    (_h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (_h₁' : n₁' ≥ 3) (_h₂' : n₂' ≥ 3)
    (h_valid : is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 1) :
    False := by
  have h_E := h_valid.1
  have h_p := h_valid.2
  unfold energy_conserved cycle_energy mass_of_cycle at h_E
  unfold momentum_conserved signed_cycle_momentum cycle_momentum_magnitude momentum mass_of_cycle at h_p
  simp only [Int.cast_one, one_mul, Int.cast_neg, neg_mul] at h_p
  -- h_E: 1/n₁ + 1/n₂ = 1/n₁' + 1/n₂'
  -- h_p: 1/n₁ - 1/n₂ = 1/n₁' + 1/n₂'
  -- Subtracting: 2/n₂ = 0, contradiction
  have hn₂ : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_diff : (1 : ℝ) / n₁ + 1 / n₂ - (1 / n₁ - 1 / n₂) = 2 / n₂ := by ring
  have h_zero : (1 : ℝ) / n₁' + 1 / n₂' - (1 / n₁' + 1 / n₂') = 0 := by ring
  have h_eq : (1 : ℝ) / n₁ + 1 / n₂ - (1 / n₁ - 1 / n₂) =
              1 / n₁' + 1 / n₂' - (1 / n₁' + 1 / n₂') := by linarith
  rw [h_diff, h_zero] at h_eq
  have h_n₂_zero : (2 : ℝ) / n₂ = 0 := h_eq
  have h_pos : (2 : ℝ) / n₂ > 0 := by positivity
  linarith

/-- The symmetric case: same-direction cannot become opposite-direction. -/
theorem no_direction_flip_symmetric (n₁ n₂ n₁' n₂' : ℕ)
    (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3) (_h₁' : n₁' ≥ 3) (h₂' : n₂' ≥ 3)
    (h_valid : is_valid_scattering n₁ n₂ n₁' n₂' 1 1 1 (-1)) :
    False := by
  have h_E := h_valid.1
  have h_p := h_valid.2
  unfold energy_conserved cycle_energy mass_of_cycle at h_E
  unfold momentum_conserved signed_cycle_momentum cycle_momentum_magnitude momentum mass_of_cycle at h_p
  simp only [Int.cast_one, one_mul, Int.cast_neg, neg_mul] at h_p
  -- h_E: 1/n₁ + 1/n₂ = 1/n₁' + 1/n₂'
  -- h_p: 1/n₁ + 1/n₂ = 1/n₁' - 1/n₂'
  have hn₂' : (n₂' : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_diff : (1 : ℝ) / n₁' + 1 / n₂' - (1 / n₁' - 1 / n₂') = 2 / n₂' := by ring
  have h_eq : (1 : ℝ) / n₁ + 1 / n₂ - (1 / n₁ + 1 / n₂) = 0 := by ring
  have h_zero : (1 : ℝ) / n₁' + 1 / n₂' - (1 / n₁' - 1 / n₂') = 0 := by linarith
  rw [h_diff] at h_zero
  have h_pos : (2 : ℝ) / n₂' > 0 := by positivity
  linarith

/-! ## Charge Conservation -/

/-- Total charge (signed mass) before and after scattering. -/
noncomputable def total_charge (n₁ n₂ : ℕ) (σ₁ σ₂ : ℤ) : ℝ :=
  signed_cycle_momentum n₁ σ₁ + signed_cycle_momentum n₂ σ₂

/-- **Charge Conservation**: Total signed momentum is conserved in any valid scattering.
    This is just momentum conservation restated. -/
theorem charge_conservation_in_scattering (n₁ n₂ n₁' n₂' : ℕ) (σ₁ σ₂ σ₁' σ₂' : ℤ)
    (h_valid : is_valid_scattering n₁ n₂ n₁' n₂' σ₁ σ₂ σ₁' σ₂') :
    total_charge n₁ n₂ σ₁ σ₂ = total_charge n₁' n₂' σ₁' σ₂' := h_valid.2

/-! ## Summary Theorem -/

/-- **The Scattering Rigidity Correspondence** (Summary Theorem)

    This theorem collects the key results about elastic scattering:

    1. Opposite-direction scattering preserves individual cycle lengths
    2. No direction flipping is allowed (charge conservation)
    3. Total charge (signed momentum) is conserved

    Physical interpretation:
    - Topology is rigid under scattering: you cannot change cycle lengths
    - The discrete mass spectrum (1/3, 1/4, 1/5, ...) is kinematically protected
    - Only pair production/annihilation can create or destroy topology
    - Scattering in Diaspora is purely elastic with no inelastic channels -/
theorem the_scattering_rigidity_correspondence :
    -- 1. Opposite-direction preserves lengths
    (∀ n₁ n₂ n₁' n₂' : ℕ, n₁ ≥ 3 → n₂ ≥ 3 → n₁' ≥ 3 → n₂' ≥ 3 →
      is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 (-1) → n₁ = n₁' ∧ n₂ = n₂') ∧
    -- 2. No opposite → same direction
    (∀ n₁ n₂ n₁' n₂' : ℕ, n₁ ≥ 3 → n₂ ≥ 3 → n₁' ≥ 3 → n₂' ≥ 3 →
      is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 1 → False) ∧
    -- 3. No same → opposite direction
    (∀ n₁ n₂ n₁' n₂' : ℕ, n₁ ≥ 3 → n₂ ≥ 3 → n₁' ≥ 3 → n₂' ≥ 3 →
      is_valid_scattering n₁ n₂ n₁' n₂' 1 1 1 (-1) → False) := by
  refine ⟨?_, ?_, ?_⟩
  · exact opposite_direction_individual_preservation
  · exact no_direction_flip
  · exact no_direction_flip_symmetric

/-! ## Kinematic Rigidity -/

/-- **The Kinematic Rigidity Principle**: In elastic scattering, cycle lengths
    form a conserved quantity.

    For opposite-direction: individual n₁, n₂ conserved

    This means the mass spectrum is stable against scattering perturbations.
    Only topological processes (pair creation/annihilation) can change it. -/
theorem kinematic_rigidity_principle (n₁ n₂ n₁' n₂' : ℕ)
    (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h₁' : n₁' ≥ 3) (h₂' : n₂' ≥ 3)
    (h_opposite : is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 (-1)) :
    -- The cycle lengths are completely rigid
    mass_of_cycle n₁ = mass_of_cycle n₁' ∧ mass_of_cycle n₂ = mass_of_cycle n₂' := by
  have ⟨h₁_eq, h₂_eq⟩ := opposite_direction_individual_preservation n₁ n₂ n₁' n₂' h₁ h₂ h₁' h₂' h_opposite
  exact ⟨by rw [h₁_eq], by rw [h₂_eq]⟩

/-! ## Elastic Scattering is Trivial -/

/-- **Elastic Scattering is Identity**: For opposite-direction cycles, the only
    valid scattering is the identity (no change at all).

    This is a consequence of the individual preservation theorem: if n₁ = n₁'
    and n₂ = n₂', then the scattering didn't change anything observable.

    Physical interpretation: Opposite-direction cycles pass through each other
    without any exchange of energy, momentum, or identity. -/
theorem elastic_scattering_is_identity (n₁ n₂ n₁' n₂' : ℕ)
    (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h₁' : n₁' ≥ 3) (h₂' : n₂' ≥ 3)
    (h_opposite : is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 (-1)) :
    -- Initial state equals final state
    n₁ = n₁' ∧ n₂ = n₂' ∧
    cycle_energy n₁ = cycle_energy n₁' ∧
    cycle_energy n₂ = cycle_energy n₂' := by
  have ⟨h₁_eq, h₂_eq⟩ := opposite_direction_individual_preservation n₁ n₂ n₁' n₂' h₁ h₂ h₁' h₂' h_opposite
  exact ⟨h₁_eq, h₂_eq, by rw [h₁_eq], by rw [h₂_eq]⟩

/-! ## Connection to Pair Production -/

/-- **Scattering vs Production**: Scattering cannot change cycle lengths, but pair
    production can create new cycles. This is the fundamental distinction:

    - Scattering: conserves {n₁, n₂} → cannot create/destroy topology
    - Pair production: energy → n + n̄ → creates new topology

    The threshold for pair production (2/n) is the only way to change the
    topological content of a system. -/
theorem scattering_vs_production (n₁ n₂ n₁' n₂' : ℕ)
    (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h₁' : n₁' ≥ 3) (h₂' : n₂' ≥ 3) :
    -- If valid scattering with opposite directions, lengths preserved
    (is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 (-1) → n₁ = n₁' ∧ n₂ = n₂') ∧
    -- Direction flips are impossible
    (¬ is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 1) ∧
    (¬ is_valid_scattering n₁ n₂ n₁' n₂' 1 1 1 (-1)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact opposite_direction_individual_preservation n₁ n₂ n₁' n₂' h₁ h₂ h₁' h₂'
  · intro h_valid
    exact no_direction_flip n₁ n₂ n₁' n₂' h₁ h₂ h₁' h₂' h_valid
  · intro h_valid
    exact no_direction_flip_symmetric n₁ n₂ n₁' n₂' h₁ h₂ h₁' h₂' h_valid

end Diaspora.Dynamics.ScatteringTheory
