import Diaspora.Dynamics.BoundDressedElectron
import Diaspora.Dynamics.InelasticScattering

/-!
# Annihilation Kinematic Closure

When a symmetric dressed electron (triangle + anti-triangle, E=2/3, p=0) radiates,
the discrete mass spectrum constrains what it can emit. We prove that any valid
2-body emission must produce another triangle pair—the process is kinematically closed.

## Physical Interpretation

The symmetric dressed electron is a "fixed point" of radiative processes: it can only
decay into copies of itself. This provides a kinematic explanation for why the
electron configuration is stable against radiative decay, beyond just binding dynamics.

## Main Results

- `two_body_forces_equal_energies`: p₁+p₂=0 with lightlike products implies E₁=E₂
- `annihilation_energy_determines_mass`: E=1/3 for each product means triangles
- `annihilation_closure_two_body`: Symmetric dressed electron radiation → triangle pair
- `symmetric_electron_is_radiative_fixed_point`: The configuration reproduces itself
-/

namespace Diaspora.Dynamics.AnnihilationClosure

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.InvariantMass
open Diaspora.Dynamics.DressedElectron
open Diaspora.Dynamics.BoundDressedElectron

/-! ## Radiative Decay Structure -/

/-- A valid 2-body radiative decay: two lightlike cycles conserving energy and momentum. -/
structure TwoBodyDecay where
  n₁ : ℕ
  n₂ : ℕ
  σ₁ : ℤ  -- orientation: +1 or -1
  σ₂ : ℤ
  h_valid₁ : n₁ ≥ 3
  h_valid₂ : n₂ ≥ 3
  h_σ₁ : σ₁ = 1 ∨ σ₁ = -1
  h_σ₂ : σ₂ = 1 ∨ σ₂ = -1

/-- Energy of a decay product. -/
noncomputable def TwoBodyDecay.energy₁ (d : TwoBodyDecay) : ℝ := mass_of_cycle d.n₁
noncomputable def TwoBodyDecay.energy₂ (d : TwoBodyDecay) : ℝ := mass_of_cycle d.n₂

/-- Signed momentum of a decay product. -/
noncomputable def TwoBodyDecay.momentum₁ (d : TwoBodyDecay) : ℝ := d.σ₁ * momentum d.n₁
noncomputable def TwoBodyDecay.momentum₂ (d : TwoBodyDecay) : ℝ := d.σ₂ * momentum d.n₂

/-- Total energy of decay products. -/
noncomputable def TwoBodyDecay.totalEnergy (d : TwoBodyDecay) : ℝ :=
  d.energy₁ + d.energy₂

/-- Total momentum of decay products. -/
noncomputable def TwoBodyDecay.totalMomentum (d : TwoBodyDecay) : ℝ :=
  d.momentum₁ + d.momentum₂

/-! ## Conservation Constraints -/

/-- A decay from symmetric dressed electron: E_total = 2/3, p_total = 0. -/
def IsSymmetricAnnihilationDecay (d : TwoBodyDecay) : Prop :=
  d.totalEnergy = 2/3 ∧ d.totalMomentum = 0

/-! ## The Closure Theorem -/

/-- Momentum conservation with lightlike products forces equal energies.
    Since E = |p| for each cycle, p₁ + p₂ = 0 implies |p₁| = |p₂|, hence E₁ = E₂. -/
theorem two_body_forces_equal_energies (d : TwoBodyDecay) (h_p : d.totalMomentum = 0) :
    |d.momentum₁| = |d.momentum₂| := by
  unfold TwoBodyDecay.totalMomentum at h_p
  have h_eq : d.momentum₁ = -d.momentum₂ := by linarith
  rw [h_eq, abs_neg]

/-- When momenta cancel, energies equal the common |momentum|. -/
theorem equal_energies_from_momentum (d : TwoBodyDecay) (h_p : d.totalMomentum = 0) :
    d.energy₁ = d.energy₂ := by
  have h_abs := two_body_forces_equal_energies d h_p
  unfold TwoBodyDecay.momentum₁ TwoBodyDecay.momentum₂ momentum at h_abs
  simp only [abs_mul] at h_abs
  have h_σ₁_abs : |(d.σ₁ : ℝ)| = 1 := by
    cases d.h_σ₁ with | inl h => simp [h] | inr h => simp [h]
  have h_σ₂_abs : |(d.σ₂ : ℝ)| = 1 := by
    cases d.h_σ₂ with | inl h => simp [h] | inr h => simp [h]
  have hn₁ : (d.n₁ : ℝ) > 0 := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega : 0 < 3) d.h_valid₁)
  have hn₂ : (d.n₂ : ℝ) > 0 := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega : 0 < 3) d.h_valid₂)
  have hm₁ : mass_of_cycle d.n₁ > 0 := by unfold mass_of_cycle; positivity
  have hm₂ : mass_of_cycle d.n₂ > 0 := by unfold mass_of_cycle; positivity
  simp only [h_σ₁_abs, h_σ₂_abs, one_mul] at h_abs
  rw [abs_of_pos hm₁, abs_of_pos hm₂] at h_abs
  unfold TwoBodyDecay.energy₁ TwoBodyDecay.energy₂
  exact h_abs

/-- Total energy 2/3 with equal parts means each is 1/3. -/
theorem each_energy_is_third (d : TwoBodyDecay) (h : IsSymmetricAnnihilationDecay d) :
    d.energy₁ = 1/3 ∧ d.energy₂ = 1/3 := by
  have h_eq := equal_energies_from_momentum d h.2
  have h_sum := h.1
  unfold TwoBodyDecay.totalEnergy at h_sum
  constructor
  · linarith
  · linarith

/-- Energy 1/3 means cycle length 3 (triangle). -/
theorem energy_third_means_triangle (n : ℕ) (h_valid : n ≥ 3) (h_E : mass_of_cycle n = 1/3) :
    n = 3 := by
  unfold mass_of_cycle at h_E
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h_n : (n : ℝ) = 3 := by field_simp [hn] at h_E; linarith
  have h_cast : (n : ℕ) = (3 : ℕ) := by
    have := @Nat.cast_injective ℝ _ _ n 3
    exact this h_n
  exact h_cast

/-- Both decay products must be triangles. -/
theorem annihilation_produces_triangles (d : TwoBodyDecay) (h : IsSymmetricAnnihilationDecay d) :
    d.n₁ = 3 ∧ d.n₂ = 3 := by
  have ⟨h₁, h₂⟩ := each_energy_is_third d h
  unfold TwoBodyDecay.energy₁ at h₁
  unfold TwoBodyDecay.energy₂ at h₂
  exact ⟨energy_third_means_triangle d.n₁ d.h_valid₁ h₁,
         energy_third_means_triangle d.n₂ d.h_valid₂ h₂⟩

/-- Momentum conservation requires opposite orientations. -/
theorem annihilation_requires_opposite_orientations (d : TwoBodyDecay)
    (h : IsSymmetricAnnihilationDecay d) :
    d.σ₁ = -d.σ₂ := by
  have ⟨hn₁, hn₂⟩ := annihilation_produces_triangles d h
  have h_p := h.2
  unfold TwoBodyDecay.totalMomentum TwoBodyDecay.momentum₁ TwoBodyDecay.momentum₂ at h_p
  unfold momentum at h_p
  simp only [hn₁, hn₂] at h_p
  have h_sum : d.σ₁ * (1/3 : ℝ) + d.σ₂ * (1/3 : ℝ) = 0 := h_p
  have h_factor : (d.σ₁ + d.σ₂ : ℝ) * (1/3) = 0 := by linarith
  have h_sum_zero : (d.σ₁ : ℝ) + d.σ₂ = 0 := by
    have : (1/3 : ℝ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h_factor).resolve_right this
  have h_int : d.σ₁ + d.σ₂ = 0 := by
    have := @Int.cast_injective ℝ _ _
    apply this
    simp only [Int.cast_add, Int.cast_zero]
    exact h_sum_zero
  omega

/-! ## The Main Closure Theorem -/

/-- **Annihilation Kinematic Closure**: Any valid 2-body decay of a symmetric dressed
    electron (E=2/3, p=0) must produce another triangle-antitriangle pair. -/
theorem annihilation_closure_two_body (d : TwoBodyDecay) (h : IsSymmetricAnnihilationDecay d) :
    d.n₁ = 3 ∧ d.n₂ = 3 ∧ d.σ₁ = -d.σ₂ := by
  have ⟨h₁, h₂⟩ := annihilation_produces_triangles d h
  exact ⟨h₁, h₂, annihilation_requires_opposite_orientations d h⟩

/-! ## The Fixed Point Interpretation -/

/-- The symmetric dressed electron configuration. -/
def trianglePairConfig : TwoBodyDecay where
  n₁ := 3
  n₂ := 3
  σ₁ := 1
  σ₂ := -1
  h_valid₁ := by omega
  h_valid₂ := by omega
  h_σ₁ := Or.inl rfl
  h_σ₂ := Or.inr rfl

/-- The triangle pair satisfies the annihilation energy-momentum constraints. -/
theorem trianglePair_is_valid_decay : IsSymmetricAnnihilationDecay trianglePairConfig := by
  constructor
  · -- Energy = 2/3
    unfold TwoBodyDecay.totalEnergy TwoBodyDecay.energy₁ TwoBodyDecay.energy₂
    unfold trianglePairConfig mass_of_cycle
    norm_num
  · -- Momentum = 0
    unfold TwoBodyDecay.totalMomentum TwoBodyDecay.momentum₁ TwoBodyDecay.momentum₂
    unfold trianglePairConfig momentum mass_of_cycle
    norm_num

/-- **Radiative Fixed Point**: The symmetric dressed electron is the unique valid
    2-body decay product of symmetric dressed electron annihilation (up to orientation flip). -/
theorem symmetric_electron_is_radiative_fixed_point (d : TwoBodyDecay)
    (h : IsSymmetricAnnihilationDecay d) :
    -- The decay produces triangles with opposite orientation (up to sign flip)
    d.n₁ = 3 ∧ d.n₂ = 3 ∧
    ((d.σ₁ = 1 ∧ d.σ₂ = -1) ∨ (d.σ₁ = -1 ∧ d.σ₂ = 1)) := by
  have ⟨hn₁, hn₂, h_opp⟩ := annihilation_closure_two_body d h
  refine ⟨hn₁, hn₂, ?_⟩
  cases d.h_σ₁ with
  | inl h₁ =>
    left
    constructor
    · exact h₁
    · simp only [h₁] at h_opp
      -- h_opp : 1 = -d.σ₂, need d.σ₂ = -1
      omega
  | inr h₁ =>
    right
    constructor
    · exact h₁
    · simp only [h₁] at h_opp
      -- h_opp : -1 = -d.σ₂, need d.σ₂ = 1
      omega

/-! ## Generalization: The Kinematic Isolation -/

/-- No valid 2-body decay can reduce the number of triangles.
    Starting with 2 triangles, you end with 2 triangles. -/
theorem triangle_count_conserved (d : TwoBodyDecay) (h : IsSymmetricAnnihilationDecay d) :
    (if d.n₁ = 3 then 1 else 0) + (if d.n₂ = 3 then 1 else 0) = 2 := by
  have ⟨h₁, h₂, _⟩ := annihilation_closure_two_body d h
  simp [h₁, h₂]

/-- The total winding (sum of orientations) is conserved at zero. -/
theorem winding_conserved_at_zero (d : TwoBodyDecay) (h : IsSymmetricAnnihilationDecay d) :
    d.σ₁ + d.σ₂ = 0 := by
  have h_opp := annihilation_requires_opposite_orientations d h
  omega

/-! ## The Annihilation Closure Correspondence -/

/-- Summary: The complete kinematic closure theorem. -/
theorem the_annihilation_closure_correspondence :
    -- Triangle pair satisfies constraints
    IsSymmetricAnnihilationDecay trianglePairConfig ∧
    -- Any valid decay produces triangles
    (∀ d : TwoBodyDecay, IsSymmetricAnnihilationDecay d → d.n₁ = 3 ∧ d.n₂ = 3) ∧
    -- Orientations must be opposite
    (∀ d : TwoBodyDecay, IsSymmetricAnnihilationDecay d → d.σ₁ = -d.σ₂) ∧
    -- Configuration is fixed point
    (∀ d : TwoBodyDecay, IsSymmetricAnnihilationDecay d →
      d.n₁ = 3 ∧ d.n₂ = 3 ∧ d.σ₁ = -d.σ₂) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact trianglePair_is_valid_decay
  · exact fun d h => annihilation_produces_triangles d h
  · exact fun d h => annihilation_requires_opposite_orientations d h
  · exact fun d h => annihilation_closure_two_body d h

end Diaspora.Dynamics.AnnihilationClosure
