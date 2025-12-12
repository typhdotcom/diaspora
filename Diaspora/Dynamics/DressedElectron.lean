import Diaspora.Dynamics.InvariantMass
import Diaspora.Dynamics.Velocity

/-!
# The Dressed Electron

A single triangle is lightlike: E = p, m² = 0. Observed electrons "at rest"
must be dressed: triangle + opposite-orientation structure creates m² > 0.

## Main Results

- `bare_electron_lightlike`: Single triangles have m² = 0
- `dressed_electron_timelike`: Dressed electrons have m² > 0
- `observable_at_rest_implies_dressed`: Rest frame implies dressing
-/

namespace Diaspora.Dynamics.DressedElectron

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.Dispersion
open Diaspora.Dynamics.InvariantMass

/-! ## The Bare Electron -/

/-- The bare electron is a single triangle (n = 3). -/
structure BareElectron where
  orientation : ℤ
  h_orientation : orientation = 1 ∨ orientation = -1

/-- Energy of a bare electron: 1/3. -/
noncomputable def bareEnergy : ℝ := mass_of_cycle 3

/-- Momentum magnitude of a bare electron: 1/3. -/
noncomputable def bareMomentum : ℝ := momentum 3

/-- Bare electrons are lightlike: E² - p² = 0. -/
theorem bare_electron_lightlike :
    invariant_mass_sq bareEnergy bareMomentum = 0 := by
  unfold bareEnergy bareMomentum
  exact single_cycle_invariant_mass_sq 3 (by omega)

/-- Bare electrons have zero invariant mass. -/
theorem bare_electron_zero_mass :
    invariant_mass bareEnergy bareMomentum = 0 := by
  unfold bareEnergy bareMomentum
  exact single_cycle_invariant_mass 3 (by omega)

/-- Bare electrons have nonzero momentum (no rest frame). -/
theorem bare_electron_has_momentum :
    bareMomentum > 0 := by
  unfold bareMomentum
  exact no_rest_frame 3 (by omega)

/-- Bare electrons travel at c. -/
theorem bare_electron_velocity_is_c :
    phase_velocity 3 = 1 :=
  phase_velocity_is_c 3 (by omega)

/-- E = p for bare electrons. -/
theorem bare_electron_dispersion :
    bareEnergy = bareMomentum := by
  unfold bareEnergy bareMomentum
  exact dispersion_relation 3 (by omega)

/-! ## The Dressed Electron -/

/-- A dressed electron is a triangle paired with an opposite-orientation cycle.
    The pairing creates invariant mass and allows a rest frame. -/
structure Dressed where
  core_orientation : ℤ
  h_core : core_orientation = 1 ∨ core_orientation = -1
  dressing_n : ℕ
  h_valid : dressing_n ≥ 3

/-- Total energy of a dressed electron (unbound). -/
noncomputable def Dressed.totalEnergy (e : Dressed) : ℝ :=
  mass_of_cycle 3 + mass_of_cycle e.dressing_n

/-- Net momentum of a dressed electron (momenta subtract due to opposite orientation). -/
noncomputable def Dressed.netMomentum (e : Dressed) : ℝ :=
  |mass_of_cycle 3 - mass_of_cycle e.dressing_n|

/-- Invariant mass squared of dressed electron. -/
noncomputable def Dressed.massSq (e : Dressed) : ℝ :=
  e.totalEnergy^2 - e.netMomentum^2

/-- Dressed electrons are timelike: m² > 0.
    Key calculation: (a + b)² - (a - b)² = 4ab > 0 for positive a, b. -/
theorem dressed_electron_timelike (e : Dressed) :
    e.massSq > 0 := by
  unfold Dressed.massSq Dressed.totalEnergy Dressed.netMomentum
  unfold mass_of_cycle
  have hn_pos : e.dressing_n > 0 := Nat.lt_of_lt_of_le (by omega : 0 < 3) e.h_valid
  have h3 : (3 : ℝ) > 0 := by norm_num
  have hn : (e.dressing_n : ℝ) > 0 := Nat.cast_pos.mpr hn_pos
  -- (a + b)² - |a - b|² = 4ab for any a, b
  have h_key : ∀ a b : ℝ, (a + b)^2 - |a - b|^2 = 4 * a * b := by
    intros a b; rw [sq_abs]; ring
  simp only [Nat.cast_ofNat]
  rw [h_key (1/3) (1/e.dressing_n)]
  positivity

/-- Explicit formula: m² = 4/(3n) for triangle + n-cycle dressing. -/
theorem dressed_mass_sq_formula (e : Dressed) :
    e.massSq = 4 / (3 * e.dressing_n) := by
  unfold Dressed.massSq Dressed.totalEnergy Dressed.netMomentum mass_of_cycle
  have hn_pos : e.dressing_n > 0 := Nat.lt_of_lt_of_le (by omega : 0 < 3) e.h_valid
  have hn : (e.dressing_n : ℝ) > 0 := Nat.cast_pos.mpr hn_pos
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have hn' : (e.dressing_n : ℝ) ≠ 0 := ne_of_gt hn
  simp only [Nat.cast_ofNat]
  rw [sq_abs]
  field_simp [h3, hn']
  ring

/-- Invariant mass of a dressed electron. -/
noncomputable def Dressed.mass (e : Dressed) : ℝ :=
  Real.sqrt e.massSq

/-- Dressed electron invariant mass is positive. -/
theorem dressed_mass_positive (e : Dressed) :
    e.mass > 0 := by
  unfold Dressed.mass
  exact Real.sqrt_pos.mpr (dressed_electron_timelike e)

/-! ## Equal Dressing: The Symmetric Case -/

/-- A symmetrically dressed electron: triangle + anti-triangle. -/
def symmetricDressed : Dressed where
  core_orientation := 1
  h_core := Or.inl rfl
  dressing_n := 3
  h_valid := by omega

/-- Symmetric dressing gives m² = 4/9. -/
theorem symmetric_dressing_mass_sq :
    symmetricDressed.massSq = 4/9 := by
  rw [dressed_mass_sq_formula]
  unfold symmetricDressed
  simp only
  norm_num

/-- Symmetric dressed electron has zero net momentum (at rest). -/
theorem symmetric_dressing_at_rest :
    symmetricDressed.netMomentum = 0 := by
  unfold Dressed.netMomentum symmetricDressed mass_of_cycle
  simp

/-- Symmetric dressed electron invariant mass = 2/3. -/
theorem symmetric_dressing_mass :
    symmetricDressed.mass = 2/3 := by
  unfold Dressed.mass
  rw [symmetric_dressing_mass_sq]
  have h : Real.sqrt (4/9) = 2/3 := by
    rw [show (4 : ℝ)/9 = (2/3)^2 by norm_num]
    exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2/3)
  exact h

/-! ## The Central Theorem -/

/-- A system has a rest frame iff it is timelike (m² > 0). -/
def HasRestFrame (m_sq : ℝ) : Prop := m_sq > 0

/-- Bare electrons do not have a rest frame. -/
theorem bare_no_rest_frame :
    ¬HasRestFrame (invariant_mass_sq bareEnergy bareMomentum) := by
  unfold HasRestFrame
  rw [bare_electron_lightlike]
  exact lt_irrefl 0

/-- Dressed electrons have a rest frame. -/
theorem dressed_has_rest_frame (e : Dressed) :
    HasRestFrame e.massSq :=
  dressed_electron_timelike e

/-- An electron configuration is either bare or dressed. -/
inductive ElectronConfig where
  | bare : BareElectron → ElectronConfig
  | dressed : Dressed → ElectronConfig

/-- Get the invariant mass squared of an electron configuration. -/
noncomputable def ElectronConfig.massSq : ElectronConfig → ℝ
  | .bare _ => invariant_mass_sq bareEnergy bareMomentum
  | .dressed e => e.massSq

/-- An electron observable at rest must be dressed. -/
theorem observable_at_rest_implies_dressed (config : ElectronConfig) :
    HasRestFrame config.massSq → ∃ e : Dressed, config = .dressed e := by
  intro h_rest
  cases config with
  | bare _ =>
    exfalso
    exact bare_no_rest_frame h_rest
  | dressed e =>
    exact ⟨e, rfl⟩

/-- Contrapositive: A bare electron cannot be observed at rest. -/
theorem bare_cannot_be_at_rest (e : BareElectron) :
    ¬HasRestFrame (ElectronConfig.bare e).massSq := by
  unfold ElectronConfig.massSq
  exact bare_no_rest_frame

/-! ## The Dressing Spectrum -/

/-- The velocity of a dressed electron: v = |p|/E. -/
noncomputable def Dressed.velocity (e : Dressed) : ℝ :=
  e.netMomentum / e.totalEnergy

/-- Equal dressing (n = 3) gives v = 0. -/
theorem symmetric_velocity_zero :
    symmetricDressed.velocity = 0 := by
  unfold Dressed.velocity
  rw [symmetric_dressing_at_rest]
  simp

/-- Dressed electrons are subluminal: v < 1. -/
theorem dressed_subluminal (e : Dressed) :
    e.velocity < 1 := by
  unfold Dressed.velocity Dressed.netMomentum Dressed.totalEnergy mass_of_cycle
  have hn_pos : e.dressing_n > 0 := Nat.lt_of_lt_of_le (by omega : 0 < 3) e.h_valid
  have h3 : (3 : ℝ) > 0 := by norm_num
  have hn : (e.dressing_n : ℝ) > 0 := Nat.cast_pos.mpr hn_pos
  simp only [Nat.cast_ofNat]
  have h_E_pos : 1/3 + 1/(e.dressing_n : ℝ) > 0 := by positivity
  -- v = |1/3 - 1/n| / (1/3 + 1/n) < 1 since |a-b| < a+b for positive a,b
  have h_abs_lt : |1/3 - 1/(e.dressing_n : ℝ)| < 1/3 + 1/(e.dressing_n : ℝ) := by
    have h1 : 1/(3 : ℝ) > 0 := by positivity
    have h2 : 1/(e.dressing_n : ℝ) > 0 := by positivity
    cases le_or_gt (1/(3 : ℝ)) (1/(e.dressing_n : ℝ)) with
    | inl h =>
      rw [abs_of_nonpos (by linarith)]
      linarith
    | inr h =>
      rw [abs_of_pos (by linarith)]
      linarith
  calc |1 / 3 - 1 / ↑e.dressing_n| / (1 / 3 + 1 / ↑e.dressing_n)
      < (1/3 + 1/(e.dressing_n : ℝ)) / (1/3 + 1/(e.dressing_n : ℝ)) :=
        div_lt_div_of_pos_right h_abs_lt h_E_pos
    _ = 1 := div_self (ne_of_gt h_E_pos)

/-- Larger dressing → smaller invariant mass. -/
theorem larger_dressing_smaller_mass (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_lt : n₁ < n₂) :
    (⟨1, Or.inl rfl, n₂, h₂⟩ : Dressed).mass < (⟨1, Or.inl rfl, n₁, h₁⟩ : Dressed).mass := by
  unfold Dressed.mass
  apply Real.sqrt_lt_sqrt
  · exact le_of_lt (dressed_electron_timelike ⟨1, Or.inl rfl, n₂, h₂⟩)
  · rw [dressed_mass_sq_formula, dressed_mass_sq_formula]
    simp only
    have h1 : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    have h2 : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    have h_cast : (n₁ : ℝ) < n₂ := Nat.cast_lt.mpr h_lt
    have h3 : (3 : ℝ) > 0 := by norm_num
    -- 4/(3n₂) < 4/(3n₁) when n₁ < n₂
    apply div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 4)
    · exact mul_pos h3 h1
    · exact mul_lt_mul_of_pos_left h_cast h3

/-! ## The Dressed Electron Correspondence -/

/-- Summary of the dressed electron theory. -/
theorem the_dressed_electron_correspondence :
    -- Bare electrons are lightlike
    (invariant_mass_sq bareEnergy bareMomentum = 0) ∧
    -- Dressed electrons are timelike
    (∀ e : Dressed, e.massSq > 0) ∧
    -- Observable at rest implies dressed
    (∀ config : ElectronConfig, HasRestFrame config.massSq →
      ∃ e : Dressed, config = .dressed e) ∧
    -- Symmetric dressing (triangle + anti-triangle) is at rest with mass 2/3
    symmetricDressed.netMomentum = 0 ∧
    symmetricDressed.mass = 2/3 := by
  exact ⟨bare_electron_lightlike, dressed_electron_timelike,
         observable_at_rest_implies_dressed, symmetric_dressing_at_rest,
         symmetric_dressing_mass⟩

end Diaspora.Dynamics.DressedElectron
