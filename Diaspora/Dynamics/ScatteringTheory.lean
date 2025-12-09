import Diaspora.Dynamics.Dispersion
import Diaspora.Dynamics.InvariantMass

/-!
# Scattering Theory: Rigidity of Topology Under Elastic Collisions

For lightlike cycles (E = |p|), energy and momentum conservation together imply
that opposite-direction scattering preserves individual cycle lengths.
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

/-- Opposite-direction elastic scattering preserves individual cycle lengths. -/
theorem opposite_direction_individual_preservation (n₁ n₂ n₁' n₂' : ℕ)
    (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h₁' : n₁' ≥ 3) (h₂' : n₂' ≥ 3)
    (h_valid : is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 (-1)) :
    n₁ = n₁' ∧ n₂ = n₂' := by
  have h_E := h_valid.1
  have h_p := h_valid.2
  unfold energy_conserved cycle_energy mass_of_cycle at h_E
  unfold momentum_conserved signed_cycle_momentum cycle_momentum_magnitude momentum mass_of_cycle at h_p
  simp only [Int.cast_one, one_mul, Int.cast_neg, neg_mul] at h_p
  have hn₁ : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂ : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₁' : (n₁' : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂' : (n₂' : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_add : (1 : ℝ) / n₁ + 1 / n₂ + (1 / n₁ - 1 / n₂) = 1 / n₁' + 1 / n₂' + (1 / n₁' - 1 / n₂') := by
    linarith
  ring_nf at h_add
  have h_n₁_eq : (1 : ℝ) / n₁ = 1 / n₁' := by linarith
  have h_sub : (1 : ℝ) / n₁ + 1 / n₂ - (1 / n₁ - 1 / n₂) = 1 / n₁' + 1 / n₂' - (1 / n₁' - 1 / n₂') := by
    linarith
  simp only [add_sub_sub_cancel] at h_sub
  have h_n₂_eq : (1 : ℝ) / n₂ = 1 / n₂' := by linarith
  have h₁_real : (n₁ : ℝ) = n₁' := by
    rw [one_div, one_div] at h_n₁_eq
    exact inv_inj.mp h_n₁_eq
  have h₂_real : (n₂ : ℝ) = n₂' := by
    rw [one_div, one_div] at h_n₂_eq
    exact inv_inj.mp h_n₂_eq
  exact ⟨Nat.cast_injective h₁_real, Nat.cast_injective h₂_real⟩

/-! ## No Direction Flipping -/

/-- Opposite-direction pairs cannot scatter into same-direction pairs. -/
theorem no_direction_flip (n₁ n₂ n₁' n₂' : ℕ)
    (_h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (_h₁' : n₁' ≥ 3) (_h₂' : n₂' ≥ 3)
    (h_valid : is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 1) :
    False := by
  have h_E := h_valid.1
  have h_p := h_valid.2
  unfold energy_conserved cycle_energy mass_of_cycle at h_E
  unfold momentum_conserved signed_cycle_momentum cycle_momentum_magnitude momentum mass_of_cycle at h_p
  simp only [Int.cast_one, one_mul, Int.cast_neg, neg_mul] at h_p
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

/-- Total signed momentum is conserved in any valid scattering. -/
theorem charge_conservation_in_scattering (n₁ n₂ n₁' n₂' : ℕ) (σ₁ σ₂ σ₁' σ₂' : ℤ)
    (h_valid : is_valid_scattering n₁ n₂ n₁' n₂' σ₁ σ₂ σ₁' σ₂') :
    total_charge n₁ n₂ σ₁ σ₂ = total_charge n₁' n₂' σ₁' σ₂' := h_valid.2

/-! ## Summary Theorem -/

/-- Collects the key scattering rigidity results. -/
theorem the_scattering_rigidity_correspondence :
    (∀ n₁ n₂ n₁' n₂' : ℕ, n₁ ≥ 3 → n₂ ≥ 3 → n₁' ≥ 3 → n₂' ≥ 3 →
      is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 (-1) → n₁ = n₁' ∧ n₂ = n₂') ∧
    (∀ n₁ n₂ n₁' n₂' : ℕ, n₁ ≥ 3 → n₂ ≥ 3 → n₁' ≥ 3 → n₂' ≥ 3 →
      is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 1 → False) ∧
    (∀ n₁ n₂ n₁' n₂' : ℕ, n₁ ≥ 3 → n₂ ≥ 3 → n₁' ≥ 3 → n₂' ≥ 3 →
      is_valid_scattering n₁ n₂ n₁' n₂' 1 1 1 (-1) → False) := by
  refine ⟨?_, ?_, ?_⟩
  · exact opposite_direction_individual_preservation
  · exact no_direction_flip
  · exact no_direction_flip_symmetric

/-! ## Kinematic Rigidity -/

/-- Elastic scattering preserves individual cycle masses. -/
theorem kinematic_rigidity_principle (n₁ n₂ n₁' n₂' : ℕ)
    (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h₁' : n₁' ≥ 3) (h₂' : n₂' ≥ 3)
    (h_opposite : is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 (-1)) :
    mass_of_cycle n₁ = mass_of_cycle n₁' ∧ mass_of_cycle n₂ = mass_of_cycle n₂' := by
  have ⟨h₁_eq, h₂_eq⟩ := opposite_direction_individual_preservation n₁ n₂ n₁' n₂' h₁ h₂ h₁' h₂' h_opposite
  exact ⟨by rw [h₁_eq], by rw [h₂_eq]⟩

/-! ## Elastic Scattering is Trivial -/

/-- Opposite-direction elastic scattering is the identity map. -/
theorem elastic_scattering_is_identity (n₁ n₂ n₁' n₂' : ℕ)
    (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h₁' : n₁' ≥ 3) (h₂' : n₂' ≥ 3)
    (h_opposite : is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 (-1)) :
    n₁ = n₁' ∧ n₂ = n₂' ∧
    cycle_energy n₁ = cycle_energy n₁' ∧
    cycle_energy n₂ = cycle_energy n₂' := by
  have ⟨h₁_eq, h₂_eq⟩ := opposite_direction_individual_preservation n₁ n₂ n₁' n₂' h₁ h₂ h₁' h₂' h_opposite
  exact ⟨h₁_eq, h₂_eq, by rw [h₁_eq], by rw [h₂_eq]⟩

/-! ## Connection to Pair Production -/

/-- Scattering preserves cycle lengths; direction flips are impossible. -/
theorem scattering_vs_production (n₁ n₂ n₁' n₂' : ℕ)
    (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h₁' : n₁' ≥ 3) (h₂' : n₂' ≥ 3) :
    (is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 (-1) → n₁ = n₁' ∧ n₂ = n₂') ∧
    (¬ is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 1) ∧
    (¬ is_valid_scattering n₁ n₂ n₁' n₂' 1 1 1 (-1)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact opposite_direction_individual_preservation n₁ n₂ n₁' n₂' h₁ h₂ h₁' h₂'
  · intro h_valid
    exact no_direction_flip n₁ n₂ n₁' n₂' h₁ h₂ h₁' h₂' h_valid
  · intro h_valid
    exact no_direction_flip_symmetric n₁ n₂ n₁' n₂' h₁ h₂ h₁' h₂' h_valid

end Diaspora.Dynamics.ScatteringTheory
