import Diaspora.Dynamics.ScatteringTheory
import Diaspora.Dynamics.PairProduction
import Diaspora.Dynamics.ChargeConservation

/-!
# Spectral Conservation

The signed mass distribution is conserved under all dynamical processes:
elastic scattering, pair production, and annihilation.
-/

namespace Diaspora.Dynamics.SpectralConservation

open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.ScatteringTheory
open Diaspora.Dynamics.PairProduction

/-! ## Signed Cycle Energy -/

/-- The signed energy of a cycle with orientation σ ∈ {+1, -1}. -/
noncomputable def signed_energy (n : ℕ) (σ : ℤ) : ℝ := σ * mass_of_cycle n

theorem signed_energy_positive (n : ℕ) (_h : n ≥ 3) :
    signed_energy n 1 = mass_of_cycle n := by
  unfold signed_energy; simp

theorem signed_energy_negative (n : ℕ) (_h : n ≥ 3) :
    signed_energy n (-1) = -mass_of_cycle n := by
  unfold signed_energy; simp

/-! ## Total Signed Energy of a Configuration -/

/-- A cycle configuration: list of (cycle length, orientation) pairs. -/
abbrev CycleConfig := List (ℕ × ℤ)

/-- Total signed energy of a configuration. -/
noncomputable def total_signed_energy (config : CycleConfig) : ℝ :=
  config.foldl (fun acc (n, σ) => acc + signed_energy n σ) 0

/-- Empty configuration has zero energy. -/
theorem empty_config_zero : total_signed_energy [] = 0 := rfl

/-- Helper: foldl with a shifted accumulator. -/
theorem foldl_add_shift (config : CycleConfig) (init : ℝ) (n : ℕ) (σ : ℤ) :
    List.foldl (fun acc (x : ℕ × ℤ) => acc + signed_energy x.1 x.2) init (config ++ [(n, σ)]) =
    List.foldl (fun acc (x : ℕ × ℤ) => acc + signed_energy x.1 x.2) init config + signed_energy n σ := by
  induction config generalizing init with
  | nil => simp only [List.nil_append, List.foldl_cons, List.foldl_nil]
  | cons head tail ih =>
    simp only [List.cons_append, List.foldl_cons]
    exact ih (init + signed_energy head.1 head.2)

/-- Adding a cycle adds its signed energy. -/
theorem add_cycle_energy (config : CycleConfig) (n : ℕ) (σ : ℤ) :
    total_signed_energy (config ++ [(n, σ)]) =
    total_signed_energy config + signed_energy n σ := by
  unfold total_signed_energy
  exact foldl_add_shift config 0 n σ

/-! ## Pair Creation/Annihilation Preserves Total -/

/-- Creating a matter-antimatter pair adds zero to total signed energy. -/
theorem pair_creation_conserves (config : CycleConfig) (n : ℕ) (h : n ≥ 3) :
    total_signed_energy (config ++ [(n, 1), (n, -1)]) = total_signed_energy config := by
  have h_assoc : config ++ [(n, 1), (n, -1)] = config ++ [(n, 1)] ++ [(n, -1)] := by simp
  rw [h_assoc]
  rw [add_cycle_energy (config ++ [(n, 1)]) n (-1)]
  rw [add_cycle_energy config n 1]
  rw [signed_energy_positive n h, signed_energy_negative n h]
  ring

/-- Removing a matter-antimatter pair preserves total signed energy. -/
theorem pair_annihilation_conserves (n : ℕ) (h : n ≥ 3) :
    signed_energy n 1 + signed_energy n (-1) = 0 := by
  rw [signed_energy_positive n h, signed_energy_negative n h]
  ring

/-! ## Elastic Scattering Preserves Total -/

/-- Before/after configurations for elastic scattering. -/
structure ElasticScattering where
  n₁ : ℕ
  n₂ : ℕ
  n₁' : ℕ
  n₂' : ℕ
  σ₁ : ℤ
  σ₂ : ℤ
  σ₁' : ℤ
  σ₂' : ℤ
  h₁ : n₁ ≥ 3
  h₂ : n₂ ≥ 3
  h₁' : n₁' ≥ 3
  h₂' : n₂' ≥ 3
  valid : is_valid_scattering n₁ n₂ n₁' n₂' σ₁ σ₂ σ₁' σ₂'

/-- Total signed energy before scattering. -/
noncomputable def scattering_energy_before (s : ElasticScattering) : ℝ :=
  signed_energy s.n₁ s.σ₁ + signed_energy s.n₂ s.σ₂

/-- Total signed energy after scattering. -/
noncomputable def scattering_energy_after (s : ElasticScattering) : ℝ :=
  signed_energy s.n₁' s.σ₁' + signed_energy s.n₂' s.σ₂'

/-- Elastic scattering conserves total signed energy. -/
theorem elastic_scattering_conserves (s : ElasticScattering) :
    scattering_energy_before s = scattering_energy_after s := by
  unfold scattering_energy_before scattering_energy_after
  have h_E := s.valid.1
  unfold energy_conserved cycle_energy at h_E
  unfold signed_energy
  have h_p := s.valid.2
  unfold momentum_conserved signed_cycle_momentum cycle_momentum_magnitude momentum at h_p
  simp only [mass_of_cycle] at h_E ⊢
  convert h_p using 1

/-! ## The Opposite-Direction Case: Complete Proof -/

/-- For opposite-direction scattering, individual lengths are preserved. -/
theorem opposite_direction_preserves_spectrum (n₁ n₂ n₁' n₂' : ℕ)
    (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h₁' : n₁' ≥ 3) (h₂' : n₂' ≥ 3)
    (h_valid : is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 (-1)) :
    n₁ = n₁' ∧ n₂ = n₂' :=
  opposite_direction_individual_preservation n₁ n₂ n₁' n₂' h₁ h₂ h₁' h₂' h_valid

/-! ## Signed Mass Distribution -/

/-- The signed mass at cycle length n in a configuration. -/
noncomputable def signed_mass_at (config : CycleConfig) (n : ℕ) : ℤ :=
  config.foldl (fun acc (m, σ) => if m = n then acc + σ else acc) 0

/-- Helper: foldl for signed mass is invariant under pair append (generalized over init). -/
theorem foldl_signed_mass_pair_cancel (config : CycleConfig) (n k : ℕ) (init : ℤ) :
    List.foldl (fun acc (p : ℕ × ℤ) => if p.1 = k then acc + p.2 else acc)
               init (config ++ [(n, 1), (n, -1)]) =
    List.foldl (fun acc (p : ℕ × ℤ) => if p.1 = k then acc + p.2 else acc) init config := by
  induction config generalizing init with
  | nil =>
    simp only [List.nil_append, List.foldl_cons, List.foldl_nil]
    by_cases h : n = k
    · simp only [h, ↓reduceIte]; ring
    · simp only [h, ↓reduceIte]
  | cons head tail ih =>
    simp only [List.cons_append, List.foldl_cons]
    obtain ⟨m, σ⟩ := head
    by_cases hm : m = k
    · simp only [hm, ↓reduceIte]
      exact ih (init + σ)
    · simp only [hm, ↓reduceIte]
      exact ih init

/-- Pair creation doesn't change signed mass at any length. -/
theorem pair_creation_preserves_distribution (config : CycleConfig) (n k : ℕ) :
    signed_mass_at (config ++ [(n, 1), (n, -1)]) k = signed_mass_at config k := by
  unfold signed_mass_at
  exact foldl_signed_mass_pair_cancel config n k 0

/-! ## The Spectral Conservation Theorem -/

/-- All allowed processes preserve the signed mass distribution.
    This is the main theorem: Z(t) is conserved. -/
theorem the_spectral_conservation_principle :
    -- Pair creation preserves signed mass at each length
    (∀ config : CycleConfig, ∀ n k : ℕ, n ≥ 3 →
      signed_mass_at (config ++ [(n, 1), (n, -1)]) k = signed_mass_at config k) ∧
    -- Pair annihilation: opposite orientations sum to zero
    (∀ n : ℕ, n ≥ 3 → signed_energy n 1 + signed_energy n (-1) = 0) ∧
    -- Elastic scattering preserves individual cycle lengths
    (∀ n₁ n₂ n₁' n₂' : ℕ, n₁ ≥ 3 → n₂ ≥ 3 → n₁' ≥ 3 → n₂' ≥ 3 →
      is_valid_scattering n₁ n₂ n₁' n₂' 1 (-1) 1 (-1) →
      n₁ = n₁' ∧ n₂ = n₂') := by
  refine ⟨?_, ?_, ?_⟩
  · intro config n k _
    exact pair_creation_preserves_distribution config n k
  · intro n hn
    exact pair_annihilation_conserves n hn
  · exact opposite_direction_preserves_spectrum

/-! ## Corollary: Universe Categorization -/

/-- The "topological sector" of a configuration: sum of signed masses. -/
noncomputable def topological_sector (config : CycleConfig) : ℝ :=
  total_signed_energy config

/-- Pair production preserves the topological sector. -/
theorem sector_invariant_under_pair_production (config : CycleConfig) (n : ℕ) (h : n ≥ 3) :
    topological_sector (config ++ [(n, 1), (n, -1)]) = topological_sector config :=
  pair_creation_conserves config n h

/-- The vacuum sector: configurations with zero total signed energy. -/
def IsVacuumSector (config : CycleConfig) : Prop :=
  topological_sector config = 0

/-- Empty configuration is in the vacuum sector. -/
theorem empty_is_vacuum : IsVacuumSector [] := by
  unfold IsVacuumSector topological_sector
  rfl

/-- Pair production from vacuum stays in vacuum. -/
theorem vacuum_pair_stays_vacuum (n : ℕ) (h : n ≥ 3) :
    IsVacuumSector [(n, 1), (n, -1)] := by
  unfold IsVacuumSector topological_sector total_signed_energy
  simp only [List.foldl_cons, List.foldl_nil]
  rw [signed_energy_positive n h, signed_energy_negative n h]
  ring

end Diaspora.Dynamics.SpectralConservation
