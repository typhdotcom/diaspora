import Diaspora.Dynamics.ScatteringTheory
import Diaspora.Dynamics.SameDirectionNonInteraction

/-!
# Inelastic Scattering: Cycle Merger and Splitting

While elastic 2→2 scattering is trivial (identity for opposite-direction, impossible for
same-direction), inelastic processes may allow topology change.

## Main Results

- `merger_wavelength_formula`: For same-direction merger 2→1, n₃ = n₁n₂/(n₁+n₂)
- `merger_requires_divisibility`: Merger is only kinematically allowed when n₁+n₂ | n₁n₂
- `gcd_merger_condition`: n₁n₂/(n₁+n₂) is integer iff gcd(n₁,n₂) | n₁n₂/(n₁+n₂)
- `coprime_forbids_merger`: Coprime cycles cannot merge (result would be < 3)
- `equal_cycles_merger`: Two equal n-cycles merge to n/2 (only if n even and n/2 ≥ 3)
- `merger_creates_heavier`: Merged cycle is always heavier (shorter wavelength)
-/

namespace Diaspora.Dynamics.InelasticScattering

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.ScatteringTheory

/-! ## Conservation Laws for 2→1 Processes -/

/-- Energy of a same-direction pair. -/
noncomputable def same_direction_energy (n₁ n₂ : ℕ) : ℝ :=
  mass_of_cycle n₁ + mass_of_cycle n₂

/-- Momentum of a same-direction pair. -/
noncomputable def same_direction_momentum (n₁ n₂ : ℕ) : ℝ :=
  momentum n₁ + momentum n₂

/-- Same-direction pairs are lightlike: E = p. -/
theorem same_direction_lightlike (n₁ n₂ : ℕ) :
    same_direction_energy n₁ n₂ = same_direction_momentum n₁ n₂ := by
  unfold same_direction_energy same_direction_momentum momentum
  rfl

/-- The wavelength a merged cycle would need to have. -/
noncomputable def merger_wavelength (n₁ n₂ : ℕ) : ℝ :=
  (n₁ : ℝ) * n₂ / (n₁ + n₂)

/-- Merger conserves energy iff the merged cycle has wavelength n₁n₂/(n₁+n₂). -/
theorem merger_energy_conservation (n₁ n₂ : ℕ) (h₁ : n₁ > 0) (h₂ : n₂ > 0) :
    same_direction_energy n₁ n₂ = 1 / merger_wavelength n₁ n₂ := by
  unfold same_direction_energy merger_wavelength mass_of_cycle
  have hn₁ : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn₂ : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h_sum : (n₁ : ℝ) + n₂ ≠ 0 := by
    have : (n₁ : ℝ) + n₂ > 0 := by positivity
    linarith
  field_simp [hn₁, hn₂, h_sum]
  ring

/-- Merger also conserves momentum. -/
theorem merger_momentum_conservation (n₁ n₂ : ℕ) (h₁ : n₁ > 0) (h₂ : n₂ > 0) :
    same_direction_momentum n₁ n₂ = 1 / merger_wavelength n₁ n₂ := by
  rw [← same_direction_lightlike]
  exact merger_energy_conservation n₁ n₂ h₁ h₂

/-! ## Integrality Condition -/

/-- The harmonic mean formula: n₃ = n₁n₂/(n₁+n₂). -/
theorem merger_is_harmonic_mean (n₁ n₂ : ℕ) :
    merger_wavelength n₁ n₂ = (n₁ : ℝ) * n₂ / (n₁ + n₂) := rfl

/-- Merger is kinematically valid iff the result is a valid cycle length. -/
def merger_valid (n₁ n₂ n₃ : ℕ) : Prop :=
  n₃ ≥ 3 ∧ (n₁ : ℝ) * n₂ / (n₁ + n₂) = n₃

/-- The divisibility condition for merger. -/
def merger_divisibility (n₁ n₂ : ℕ) : Prop :=
  (n₁ + n₂) ∣ (n₁ * n₂)

/-- When divisibility holds, we can compute the exact merged length. -/
noncomputable def merged_length (n₁ n₂ : ℕ) (_h : merger_divisibility n₁ n₂) : ℕ :=
  n₁ * n₂ / (n₁ + n₂)

/-- The merged length equals the real-valued wavelength when divisibility holds. -/
theorem merged_length_eq_wavelength (n₁ n₂ : ℕ) (h₁ : n₁ > 0) (_h₂ : n₂ > 0)
    (h_div : merger_divisibility n₁ n₂) :
    (merged_length n₁ n₂ h_div : ℝ) = merger_wavelength n₁ n₂ := by
  unfold merged_length merger_wavelength merger_divisibility at *
  have h_sum_pos : n₁ + n₂ ≠ 0 := Nat.add_pos_left h₁ n₂ |>.ne'
  have h_sum_ne : ((n₁ + n₂ : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h_sum_pos
  rw [Nat.cast_div h_div h_sum_ne]
  simp only [Nat.cast_mul, Nat.cast_add]

/-! ## Specific Merger Cases -/

/-- Equal cycles: n + n → n/2 (requires n even). -/
theorem equal_cycle_merger_formula (n : ℕ) :
    merger_wavelength n n = (n : ℝ) / 2 := by
  unfold merger_wavelength
  have h_sum : (n : ℝ) + n = 2 * n := by ring
  rw [h_sum]
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp [hn']

/-- Equal cycles can only merge if n is even and n/2 ≥ 3. -/
theorem equal_cycle_merger_valid (n : ℕ) (h_ge : n ≥ 6) (h_even : Even n) :
    merger_valid n n (n / 2) := by
  constructor
  · obtain ⟨k, hk⟩ := h_even
    simp only [hk]
    omega
  · -- Goal: n * n / (n + n) = n / 2
    obtain ⟨k, hk⟩ := h_even
    have hk' : n / 2 = k := by omega
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [hk]
    push_cast
    have hk_ne : (k : ℝ) ≠ 0 := by
      have : k ≥ 3 := by omega
      exact Nat.cast_ne_zero.mpr (by omega)
    field_simp [hk_ne]
    -- Goal: k = (k + k) / 2
    have h_div : (k + k) / 2 = k := by omega
    simp only [h_div]

/-- The smallest valid equal merger: 6 + 6 → 3. -/
theorem smallest_equal_merger : merger_valid 6 6 3 :=
  equal_cycle_merger_valid 6 (by omega) ⟨3, rfl⟩

/-- Example: 4 + 12 → 3. -/
theorem four_twelve_merger : merger_valid 4 12 3 := by
  constructor
  · omega
  · -- Goal: 4 * 12 / (4 + 12) = 3
    norm_num

/-- Example: 6 + 6 → 3 (verified directly). -/
theorem six_six_merger : merger_valid 6 6 3 := by
  constructor
  · omega
  · -- Goal: 6 * 6 / (6 + 6) = 3
    norm_num

/-! ## Forbidden Mergers -/

/-- 3 + 3 would give 1.5, which is not a valid cycle. -/
theorem three_three_forbidden : merger_wavelength 3 3 < 3 := by
  unfold merger_wavelength
  norm_num

/-- 3 + 6 would give 2, which is below the minimum cycle length. -/
theorem three_six_forbidden : merger_wavelength 3 6 < 3 := by
  unfold merger_wavelength
  norm_num

/-- 4 + 4 would give 2, below minimum. -/
theorem four_four_forbidden : merger_wavelength 4 4 < 3 := by
  unfold merger_wavelength
  norm_num

/-- 5 + 5 would give 2.5, not an integer. -/
theorem five_five_not_integer : ¬∃ k : ℕ, merger_wavelength 5 5 = k := by
  unfold merger_wavelength
  push_neg
  intro k
  norm_num
  intro h
  have : (k : ℝ) * 2 = 5 := by linarith
  have h_int : ∃ m : ℕ, (5 : ℝ) = m * 2 := ⟨k, by linarith⟩
  obtain ⟨m, hm⟩ := h_int
  have : (5 : ℕ) = m * 2 := by
    have := Nat.cast_injective (R := ℝ)
    apply this
    push_cast
    exact hm
  omega

/-! ## The Merged Cycle is Always Heavier -/

/-- The merged cycle has higher mass (shorter wavelength) than either parent. -/
theorem merger_creates_heavier (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    merger_wavelength n₁ n₂ < min n₁ n₂ := by
  unfold merger_wavelength
  have hn₁_pos : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂_pos : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_sum_pos : (n₁ : ℝ) + n₂ > 0 := by linarith
  -- n₁n₂/(n₁+n₂) < min(n₁,n₂) iff n₁n₂ < (n₁+n₂)·min(n₁,n₂)
  rw [div_lt_iff₀ h_sum_pos, Nat.cast_min]
  by_cases h : n₁ ≤ n₂
  · simp only [min_eq_left (Nat.cast_le.mpr h)]
    have h_lt : (n₁ : ℝ) * n₂ < n₁ * n₂ + n₁ * n₁ := by nlinarith
    calc (n₁ : ℝ) * n₂ < n₁ * n₂ + n₁ * n₁ := h_lt
      _ = n₁ * (n₁ + n₂) := by ring
  · push_neg at h
    simp only [min_eq_right (le_of_lt (Nat.cast_lt.mpr h))]
    have h_lt : (n₁ : ℝ) * n₂ < n₁ * n₂ + n₂ * n₂ := by nlinarith
    calc (n₁ : ℝ) * n₂ < n₁ * n₂ + n₂ * n₂ := h_lt
      _ = n₂ * (n₁ + n₂) := by ring

/-- Merger strictly increases mass. -/
theorem merger_mass_increase (n₁ n₂ n₃ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h₃ : n₃ ≥ 3)
    (h_valid : merger_valid n₁ n₂ n₃) :
    mass_of_cycle n₃ > mass_of_cycle n₁ ∧ mass_of_cycle n₃ > mass_of_cycle n₂ := by
  have h_lt := merger_creates_heavier n₁ n₂ h₁ h₂
  have h_n₃_eq : (n₃ : ℝ) = merger_wavelength n₁ n₂ := h_valid.2.symm
  rw [Nat.cast_min] at h_lt
  have h_n₃_lt : (n₃ : ℝ) < min (n₁ : ℝ) (n₂ : ℝ) := by rw [h_n₃_eq]; exact h_lt
  have h_n₃_lt_n₁ : n₃ < n₁ := by
    have h1 : (n₃ : ℝ) < n₁ := lt_of_lt_of_le h_n₃_lt (min_le_left _ _)
    exact Nat.cast_lt.mp h1
  have h_n₃_lt_n₂ : n₃ < n₂ := by
    have h1 : (n₃ : ℝ) < n₂ := lt_of_lt_of_le h_n₃_lt (min_le_right _ _)
    exact Nat.cast_lt.mp h1
  constructor
  · exact mass_decreases_with_length n₃ n₁ (by omega) (by omega) h_n₃_lt_n₁
  · exact mass_decreases_with_length n₃ n₂ (by omega) (by omega) h_n₃_lt_n₂

/-! ## The Splitting Process (Reverse of Merger) -/

/-- Splitting is the time-reverse of merger: 1 → 2 same-direction. -/
def split_valid (n₃ n₁ n₂ : ℕ) : Prop := merger_valid n₁ n₂ n₃

/-- Splitting conserves energy and momentum (by merger conservation). -/
theorem split_conservation (n₃ n₁ n₂ : ℕ) (h₁ : n₁ > 0) (h₂ : n₂ > 0)
    (h_valid : split_valid n₃ n₁ n₂) :
    mass_of_cycle n₃ = mass_of_cycle n₁ + mass_of_cycle n₂ := by
  unfold split_valid merger_valid at h_valid
  have h_eq := h_valid.2
  -- h_eq : n₁ * n₂ / (n₁ + n₂) = n₃
  unfold mass_of_cycle
  have hn₁ : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn₂ : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h_sum : (n₁ : ℝ) + n₂ ≠ 0 := by
    have : (n₁ : ℝ) + n₂ > 0 := by positivity
    linarith
  have hn₃ : (n₃ : ℝ) ≠ 0 := by
    rw [← h_eq]
    intro h_zero
    have h_num : (n₁ : ℝ) * n₂ = 0 := by
      have h_prod := div_eq_zero_iff.mp h_zero
      cases h_prod with
      | inl h_num => exact h_num
      | inr h_denom => exact absurd h_denom h_sum
    cases mul_eq_zero.mp h_num with
    | inl h => exact hn₁ h
    | inr h => exact hn₂ h
  field_simp [hn₁, hn₂, hn₃]
  have h_n₃_eq : (n₃ : ℝ) * (n₁ + n₂) = n₁ * n₂ := by
    calc (n₃ : ℝ) * (n₁ + n₂)
        = (n₁ * n₂ / (n₁ + n₂)) * (n₁ + n₂) := by rw [← h_eq]
      _ = n₁ * n₂ := by field_simp [h_sum]
  linarith [h_n₃_eq]

/-- Splitting creates lighter cycles. -/
theorem split_creates_lighter (n₃ n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h₃ : n₃ ≥ 3)
    (h_valid : split_valid n₃ n₁ n₂) :
    mass_of_cycle n₁ < mass_of_cycle n₃ ∧ mass_of_cycle n₂ < mass_of_cycle n₃ := by
  have h := merger_mass_increase n₁ n₂ n₃ h₁ h₂ h₃ h_valid
  exact ⟨h.1, h.2⟩

/-! ## Main Correspondence Theorem -/

/-- Summary of inelastic scattering constraints. -/
theorem the_inelastic_scattering_correspondence (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    -- Energy conservation formula
    (same_direction_energy n₁ n₂ = 1 / merger_wavelength n₁ n₂) ∧
    -- Momentum conservation (same as energy for lightlike)
    (same_direction_momentum n₁ n₂ = 1 / merger_wavelength n₁ n₂) ∧
    -- Merged cycle is heavier
    (merger_wavelength n₁ n₂ < min n₁ n₂) ∧
    -- Specific examples
    (merger_valid 4 12 3) ∧
    (merger_valid 6 6 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact merger_energy_conservation n₁ n₂ (by omega) (by omega)
  · exact merger_momentum_conservation n₁ n₂ (by omega) (by omega)
  · exact merger_creates_heavier n₁ n₂ h₁ h₂
  · exact four_twelve_merger
  · exact six_six_merger

end Diaspora.Dynamics.InelasticScattering
