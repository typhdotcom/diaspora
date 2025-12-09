import Diaspora.Dynamics.Gravity

/-!
# De Broglie Correspondence

Cycle length n serves as wavelength, giving m × λ = 1.

- `wavelength`: λ = n
- `deBroglie_product`: m × λ = 1
- `heisenberg_uncertainty`: Δx × Δp = 1
-/

namespace Diaspora.Dynamics.DeBroglie

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics

def wavelength (n : ℕ) : ℕ := n

noncomputable def wavelength_real (n : ℕ) : ℝ := (n : ℝ)

/-- m × λ = 1. -/
theorem deBroglie_product (n : ℕ) (h : n > 0) :
    mass_of_cycle n * wavelength_real n = 1 := by
  unfold mass_of_cycle wavelength_real
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h)
  field_simp [hn]

theorem wavelength_from_mass (n : ℕ) (h : n ≥ 3) :
    wavelength_real n = 1 / mass_of_cycle n := by
  unfold wavelength_real mass_of_cycle
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : n ≠ 0)
  field_simp [hn]

theorem mass_from_wavelength (n : ℕ) (h : n ≥ 3) :
    mass_of_cycle n = 1 / wavelength_real n := by
  unfold mass_of_cycle wavelength_real
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : n ≠ 0)
  field_simp [hn]

/-- Momentum p = m in natural units. -/
noncomputable def momentum (n : ℕ) : ℝ := mass_of_cycle n

theorem wavelength_momentum_relation (n : ℕ) (h : n ≥ 3) :
    wavelength_real n = 1 / momentum n := by
  unfold momentum
  exact wavelength_from_mass n h

/-- p × λ = 1. -/
theorem momentum_wavelength_product (n : ℕ) (h : n > 0) :
    momentum n * wavelength_real n = 1 := by
  unfold momentum
  exact deBroglie_product n h

/-- n₁ < n₂ implies m(n₁) > m(n₂) and λ(n₁) < λ(n₂). -/
theorem heavier_shorter_wavelength (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_lt : n₁ < n₂) :
    mass_of_cycle n₁ > mass_of_cycle n₂ ∧ wavelength_real n₁ < wavelength_real n₂ := by
  constructor
  · exact mass_decreases_with_length n₁ n₂ (by omega) (by omega) h_lt
  · unfold wavelength_real
    exact Nat.cast_lt.mpr h_lt

theorem minimum_wavelength : wavelength 3 = 3 := rfl

theorem max_mass_min_wavelength : mass_of_cycle (wavelength 3) = 1/3 := by
  unfold mass_of_cycle wavelength
  norm_num

/-- Compton wavelength λ_C = 1/m. -/
noncomputable def compton_wavelength (n : ℕ) : ℝ := 1 / mass_of_cycle n

theorem compton_equals_wavelength (n : ℕ) (h : n ≥ 3) :
    compton_wavelength n = wavelength_real n := by
  unfold compton_wavelength
  exact (wavelength_from_mass n h).symm

/-- Frequency f = m = 1/n. -/
noncomputable def frequency (n : ℕ) : ℝ := mass_of_cycle n

theorem energy_frequency (n : ℕ) : mass_of_cycle n = frequency n := rfl

/-- f × λ = 1. -/
theorem frequency_wavelength_product (n : ℕ) (h : n > 0) :
    frequency n * wavelength_real n = 1 := by
  unfold frequency
  exact deBroglie_product n h

theorem wave_particle_unity (n : ℕ) (h : n > 0) :
    mass_of_cycle n = 1 / wavelength_real n ∧
    momentum n = 1 / wavelength_real n ∧
    frequency n = 1 / wavelength_real n ∧
    mass_of_cycle n * wavelength_real n = 1 := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h)
  simp only [mass_of_cycle, wavelength_real, momentum, frequency]
  refine ⟨trivial, trivial, trivial, ?_⟩
  field_simp [hn]

theorem wavelength_quantized (n : ℕ) (h : n ≥ 3) : wavelength n ≥ 3 := h

theorem mass_spectrum_discrete (n : ℕ) (h : n ≥ 3) :
    ∃ k : ℕ, k ≥ 3 ∧ mass_of_cycle n = 1 / (k : ℝ) := by
  use n, h
  unfold mass_of_cycle
  rfl

/-- All six wave-particle relations unified. -/
theorem the_deBroglie_correspondence (n : ℕ) (h : n ≥ 3) :
    (mass_of_cycle n * wavelength_real n = 1) ∧
    (momentum n * wavelength_real n = 1) ∧
    (mass_of_cycle n = frequency n) ∧
    (frequency n * wavelength_real n = 1) ∧
    (mass_of_cycle n = momentum n) ∧
    (mass_of_cycle n = mass_of_cycle n) := by
  refine ⟨?_, ?_, rfl, ?_, rfl, rfl⟩
  · exact deBroglie_product n (by omega)
  · exact momentum_wavelength_product n (by omega)
  · exact frequency_wavelength_product n (by omega)

noncomputable def position_uncertainty (n : ℕ) : ℝ := wavelength_real n

noncomputable def momentum_uncertainty (n : ℕ) : ℝ := momentum n

/-- Δx × Δp = 1. -/
theorem heisenberg_uncertainty (n : ℕ) (h : n > 0) :
    position_uncertainty n * momentum_uncertainty n = 1 := by
  unfold position_uncertainty momentum_uncertainty
  rw [mul_comm]
  exact momentum_wavelength_product n h

/-- n₁ < n₂ implies Δx(n₁) < Δx(n₂) and Δp(n₁) > Δp(n₂). -/
theorem uncertainty_tradeoff (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_lt : n₁ < n₂) :
    position_uncertainty n₁ < position_uncertainty n₂ ∧
    momentum_uncertainty n₁ > momentum_uncertainty n₂ := by
  unfold position_uncertainty momentum_uncertainty momentum
  have h := heavier_shorter_wavelength n₁ n₂ h₁ h₂ h_lt
  exact ⟨h.2, h.1⟩

theorem minimum_uncertainty_state :
    position_uncertainty 3 * momentum_uncertainty 3 = 1 :=
  heisenberg_uncertainty 3 (by omega)

/-- m_eff = m₁ + m₂ - binding_energy. -/
noncomputable def effective_mass_bound (n₁ n₂ k : ℕ) : ℝ :=
  mass_of_cycle n₁ + mass_of_cycle n₂ - sharing_energy_reduction n₁ n₂ k

/-- λ_eff = 1/m_eff. -/
noncomputable def effective_wavelength_bound (n₁ n₂ k : ℕ) : ℝ :=
  1 / effective_mass_bound n₁ n₂ k

/-- Stronger binding → lower mass → longer wavelength. -/
theorem binding_increases_wavelength (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    ∀ k₁ k₂ : ℕ,
      k₁ < k₂ →
      (h_mass₁ : effective_mass_bound n₁ n₂ k₁ > 0) →
      (h_mass₂ : effective_mass_bound n₁ n₂ k₂ > 0) →
      effective_wavelength_bound n₁ n₂ k₁ < effective_wavelength_bound n₁ n₂ k₂ := by
  intro k₁ k₂ h_lt h_mass₁ h_mass₂
  unfold effective_wavelength_bound
  -- More binding → smaller effective mass → larger wavelength
  apply one_div_lt_one_div_of_lt h_mass₂
  unfold effective_mass_bound sharing_energy_reduction
  have h_n₁ : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_n₂ : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h_prod : (n₁ : ℝ) * n₂ > 0 := mul_pos h_n₁ h_n₂
  have h_k_lt : (k₁ : ℝ) < k₂ := Nat.cast_lt.mpr h_lt
  have h_reduction_lt : 2 * (k₁ : ℝ) / (n₁ * n₂) < 2 * (k₂ : ℝ) / (n₁ * n₂) := by
    apply div_lt_div_of_pos_right _ h_prod
    linarith
  linarith

/-- Complete annihilation: m_eff → 0 when binding = total mass. -/
theorem annihilation_infinite_wavelength (n : ℕ) (h : n ≥ 3) :
    effective_mass_bound n n n = 0 := by
  unfold effective_mass_bound sharing_energy_reduction mass_of_cycle
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn_pos : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  field_simp [hn]
  ring

end Diaspora.Dynamics.DeBroglie
