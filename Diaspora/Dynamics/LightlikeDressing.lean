import Diaspora.Dynamics.InvariantMass
import Diaspora.Dynamics.Velocity

/-!
# Lightlike Dressing

Single cycles are lightlike (E = p, m² = 0). Opposite-orientation pairs
create timelike composites (m² > 0) that can have a rest frame.
-/

namespace Diaspora.Dynamics.LightlikeDressing

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.Dispersion
open Diaspora.Dynamics.InvariantMass

/-! ## Bare Triangle -/

/-- A bare triangle (n = 3) with orientation. -/
structure BareTriangle where
  orientation : ℤ
  h_orientation : orientation = 1 ∨ orientation = -1

/-- Energy of a bare triangle: 1/3. -/
noncomputable def bareEnergy : ℝ := mass_of_cycle 3

/-- Momentum of a bare triangle: 1/3. -/
noncomputable def bareMomentum : ℝ := momentum 3

/-- Bare triangles are lightlike: E² - p² = 0. -/
theorem bare_triangle_lightlike :
    invariant_mass_sq bareEnergy bareMomentum = 0 := by
  unfold bareEnergy bareMomentum
  exact single_cycle_invariant_mass_sq 3 (by omega)

/-- Bare triangles have zero invariant mass. -/
theorem bare_triangle_zero_mass :
    invariant_mass bareEnergy bareMomentum = 0 := by
  unfold bareEnergy bareMomentum
  exact single_cycle_invariant_mass 3 (by omega)

/-- Bare triangles have nonzero momentum. -/
theorem bare_triangle_has_momentum :
    bareMomentum > 0 := by
  unfold bareMomentum
  exact no_rest_frame 3 (by omega)

/-- Bare triangles travel at c. -/
theorem bare_triangle_velocity_is_c :
    phase_velocity 3 = 1 :=
  phase_velocity_is_c 3 (by omega)

/-- E = p for bare triangles. -/
theorem bare_triangle_dispersion :
    bareEnergy = bareMomentum := by
  unfold bareEnergy bareMomentum
  exact dispersion_relation 3 (by omega)

/-! ## Dressed Pairs -/

/-- A triangle paired with an opposite-orientation cycle. -/
structure DressedPair where
  core_orientation : ℤ
  h_core : core_orientation = 1 ∨ core_orientation = -1
  dressing_n : ℕ
  h_valid : dressing_n ≥ 3

/-- Total energy (unbound). -/
noncomputable def DressedPair.totalEnergy (e : DressedPair) : ℝ :=
  mass_of_cycle 3 + mass_of_cycle e.dressing_n

/-- Net momentum (momenta subtract due to opposite orientation). -/
noncomputable def DressedPair.netMomentum (e : DressedPair) : ℝ :=
  |mass_of_cycle 3 - mass_of_cycle e.dressing_n|

/-- Invariant mass squared. -/
noncomputable def DressedPair.massSq (e : DressedPair) : ℝ :=
  e.totalEnergy^2 - e.netMomentum^2

/-- Dressed pairs are timelike: m² > 0. -/
theorem dressed_pair_timelike (e : DressedPair) :
    e.massSq > 0 := by
  unfold DressedPair.massSq DressedPair.totalEnergy DressedPair.netMomentum
  unfold mass_of_cycle
  have hn_pos : e.dressing_n > 0 := Nat.lt_of_lt_of_le (by omega : 0 < 3) e.h_valid
  have h3 : (3 : ℝ) > 0 := by norm_num
  have hn : (e.dressing_n : ℝ) > 0 := Nat.cast_pos.mpr hn_pos
  have h_key : ∀ a b : ℝ, (a + b)^2 - |a - b|^2 = 4 * a * b := by
    intros a b; rw [sq_abs]; ring
  simp only [Nat.cast_ofNat]
  rw [h_key (1/3) (1/e.dressing_n)]
  positivity

/-- m² = 4/(3n) for triangle + n-cycle. -/
theorem dressed_mass_sq_formula (e : DressedPair) :
    e.massSq = 4 / (3 * e.dressing_n) := by
  unfold DressedPair.massSq DressedPair.totalEnergy DressedPair.netMomentum mass_of_cycle
  have hn_pos : e.dressing_n > 0 := Nat.lt_of_lt_of_le (by omega : 0 < 3) e.h_valid
  have hn : (e.dressing_n : ℝ) > 0 := Nat.cast_pos.mpr hn_pos
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have hn' : (e.dressing_n : ℝ) ≠ 0 := ne_of_gt hn
  simp only [Nat.cast_ofNat]
  rw [sq_abs]
  field_simp [h3, hn']
  ring

/-- Invariant mass of a dressed pair. -/
noncomputable def DressedPair.mass (e : DressedPair) : ℝ :=
  Real.sqrt e.massSq

/-- Dressed pair invariant mass is positive. -/
theorem dressed_mass_positive (e : DressedPair) :
    e.mass > 0 := by
  unfold DressedPair.mass
  exact Real.sqrt_pos.mpr (dressed_pair_timelike e)

/-! ## Symmetric Case -/

/-- Triangle + anti-triangle. -/
def symmetricPair : DressedPair where
  core_orientation := 1
  h_core := Or.inl rfl
  dressing_n := 3
  h_valid := by omega

/-- Symmetric pair has m² = 4/9. -/
theorem symmetric_pair_mass_sq :
    symmetricPair.massSq = 4/9 := by
  rw [dressed_mass_sq_formula]
  unfold symmetricPair
  simp only
  norm_num

/-- Symmetric pair is at rest. -/
theorem symmetric_pair_at_rest :
    symmetricPair.netMomentum = 0 := by
  unfold DressedPair.netMomentum symmetricPair mass_of_cycle
  simp

/-- Symmetric pair has invariant mass 2/3. -/
theorem symmetric_pair_mass :
    symmetricPair.mass = 2/3 := by
  unfold DressedPair.mass
  rw [symmetric_pair_mass_sq]
  have h : Real.sqrt (4/9) = 2/3 := by
    rw [show (4 : ℝ)/9 = (2/3)^2 by norm_num]
    exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2/3)
  exact h

/-! ## Rest Frames -/

/-- A system has a rest frame iff m² > 0. -/
def HasRestFrame (m_sq : ℝ) : Prop := m_sq > 0

/-- Bare triangles have no rest frame. -/
theorem bare_no_rest_frame :
    ¬HasRestFrame (invariant_mass_sq bareEnergy bareMomentum) := by
  unfold HasRestFrame
  rw [bare_triangle_lightlike]
  exact lt_irrefl 0

/-- Dressed pairs have a rest frame. -/
theorem dressed_has_rest_frame (e : DressedPair) :
    HasRestFrame e.massSq :=
  dressed_pair_timelike e

/-- Configuration: bare or dressed. -/
inductive TriangleConfig where
  | bare : BareTriangle → TriangleConfig
  | dressed : DressedPair → TriangleConfig

/-- Invariant mass squared of a configuration. -/
noncomputable def TriangleConfig.massSq : TriangleConfig → ℝ
  | .bare _ => invariant_mass_sq bareEnergy bareMomentum
  | .dressed e => e.massSq

/-- Rest frame implies dressed. -/
theorem rest_frame_implies_dressed (config : TriangleConfig) :
    HasRestFrame config.massSq → ∃ e : DressedPair, config = .dressed e := by
  intro h_rest
  cases config with
  | bare _ =>
    exfalso
    exact bare_no_rest_frame h_rest
  | dressed e =>
    exact ⟨e, rfl⟩

/-- Bare triangles cannot be at rest. -/
theorem bare_cannot_be_at_rest (e : BareTriangle) :
    ¬HasRestFrame (TriangleConfig.bare e).massSq := by
  unfold TriangleConfig.massSq
  exact bare_no_rest_frame

/-! ## Velocity Spectrum -/

/-- Velocity: v = |p|/E. -/
noncomputable def DressedPair.velocity (e : DressedPair) : ℝ :=
  e.netMomentum / e.totalEnergy

/-- Symmetric pair has v = 0. -/
theorem symmetric_velocity_zero :
    symmetricPair.velocity = 0 := by
  unfold DressedPair.velocity
  rw [symmetric_pair_at_rest]
  simp

/-- Dressed pairs are subluminal. -/
theorem dressed_subluminal (e : DressedPair) :
    e.velocity < 1 := by
  unfold DressedPair.velocity DressedPair.netMomentum DressedPair.totalEnergy mass_of_cycle
  have hn_pos : e.dressing_n > 0 := Nat.lt_of_lt_of_le (by omega : 0 < 3) e.h_valid
  have h3 : (3 : ℝ) > 0 := by norm_num
  have hn : (e.dressing_n : ℝ) > 0 := Nat.cast_pos.mpr hn_pos
  simp only [Nat.cast_ofNat]
  have h_E_pos : 1/3 + 1/(e.dressing_n : ℝ) > 0 := by positivity
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

/-- Larger dressing cycle gives smaller invariant mass. -/
theorem larger_dressing_smaller_mass (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_lt : n₁ < n₂) :
    (⟨1, Or.inl rfl, n₂, h₂⟩ : DressedPair).mass < (⟨1, Or.inl rfl, n₁, h₁⟩ : DressedPair).mass := by
  unfold DressedPair.mass
  apply Real.sqrt_lt_sqrt
  · exact le_of_lt (dressed_pair_timelike ⟨1, Or.inl rfl, n₂, h₂⟩)
  · rw [dressed_mass_sq_formula, dressed_mass_sq_formula]
    simp only
    have h1 : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    have h2 : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    have h_cast : (n₁ : ℝ) < n₂ := Nat.cast_lt.mpr h_lt
    have h3 : (3 : ℝ) > 0 := by norm_num
    apply div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 4)
    · exact mul_pos h3 h1
    · exact mul_lt_mul_of_pos_left h_cast h3

/-! ## Summary -/

/-- Lightlike dressing correspondence. -/
theorem the_lightlike_dressing_correspondence :
    (invariant_mass_sq bareEnergy bareMomentum = 0) ∧
    (∀ e : DressedPair, e.massSq > 0) ∧
    (∀ config : TriangleConfig, HasRestFrame config.massSq →
      ∃ e : DressedPair, config = .dressed e) ∧
    symmetricPair.netMomentum = 0 ∧
    symmetricPair.mass = 2/3 := by
  exact ⟨bare_triangle_lightlike, dressed_pair_timelike,
         rest_frame_implies_dressed, symmetric_pair_at_rest,
         symmetric_pair_mass⟩

end Diaspora.Dynamics.LightlikeDressing
