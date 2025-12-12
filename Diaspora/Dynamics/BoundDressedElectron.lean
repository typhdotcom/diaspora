import Diaspora.Dynamics.DressedElectron
import Diaspora.Dynamics.BoundStateKinematics

/-!
# Bound Dressed Electron Theory

The DressedElectron theory treats dressing as unbound (no shared edges). But what happens
when the core triangle and its dressing cycle share edges? Binding reduces energy while
preserving momentum, leading to:

1. Partial binding: Reduced invariant mass, still timelike
2. Complete binding (symmetric case): Annihilation to the null state

## Main Results

- `BoundDressed.massSq`: m² = 4(3-k)(n-k)/(3n)² for k shared edges
- `symmetric_annihilation`: Triangle + anti-triangle with k=3 gives m² = 0
- `dressed_electron_metastable`: Symmetric dressing can annihilate with enough binding
- `partial_binding_still_timelike`: For k < min(3,n), bound dressed electron has m² > 0
-/

namespace Diaspora.Dynamics.BoundDressedElectron

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.Dispersion
open Diaspora.Dynamics.InvariantMass
open Diaspora.Dynamics.BoundStateKinematics
open Diaspora.Dynamics.DressedElectron

/-! ## Bound Dressed Electron Structure -/

/-- A bound dressed electron: triangle + opposite-orientation n-cycle sharing k edges. -/
structure BoundDressed where
  core_orientation : ℤ
  h_core : core_orientation = 1 ∨ core_orientation = -1
  dressing_n : ℕ
  h_valid : dressing_n ≥ 3
  shared_edges : ℕ
  h_shared_bound : shared_edges ≤ min 3 dressing_n

/-- The unbound dressed electron is the k=0 case. -/
def unboundDressed (d : Dressed) : BoundDressed where
  core_orientation := d.core_orientation
  h_core := d.h_core
  dressing_n := d.dressing_n
  h_valid := d.h_valid
  shared_edges := 0
  h_shared_bound := Nat.zero_le _

/-- Total energy of bound dressed electron. -/
noncomputable def BoundDressed.totalEnergy (e : BoundDressed) : ℝ :=
  bound_total_energy 3 e.dressing_n e.shared_edges

/-- Net momentum of bound dressed electron (independent of binding!). -/
noncomputable def BoundDressed.netMomentum (e : BoundDressed) : ℝ :=
  |bound_total_momentum 3 e.dressing_n|

/-- Invariant mass squared using the bound state formula. -/
noncomputable def BoundDressed.massSq (e : BoundDressed) : ℝ :=
  bound_invariant_mass_sq 3 e.dressing_n e.shared_edges

/-- At k=0, we recover the unbound DressedElectron formula. -/
theorem bound_at_zero_is_unbound (d : Dressed) :
    (unboundDressed d).massSq = d.massSq := by
  unfold unboundDressed BoundDressed.massSq Dressed.massSq
  unfold Dressed.totalEnergy Dressed.netMomentum
  unfold bound_invariant_mass_sq mass_of_cycle
  simp only [Nat.cast_zero, sub_zero]
  have h_ge := d.h_valid
  have hn : (d.dressing_n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (by omega))
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have h_prod : (3 : ℝ) * d.dressing_n ≠ 0 := mul_ne_zero h3 hn
  rw [sq_abs]
  field_simp [hn, h3, h_prod]
  ring

/-! ## Bound Dressed Electron Mass Formula -/

/-- The bound dressed electron mass formula: m² = 4(3-k)(n-k)/(3n)². -/
theorem bound_dressed_mass_formula (e : BoundDressed) :
    e.massSq = 4 * (3 - e.shared_edges : ℝ) * (e.dressing_n - e.shared_edges) /
               ((3 : ℝ) * e.dressing_n)^2 := by
  unfold BoundDressed.massSq bound_invariant_mass_sq
  ring

/-! ## Symmetric Dressed Electron: The Metastable Case -/

/-- Symmetric bound dressed: triangle + anti-triangle sharing k edges. -/
def symmetricBound (k : ℕ) (hk : k ≤ 3) : BoundDressed where
  core_orientation := 1
  h_core := Or.inl rfl
  dressing_n := 3
  h_valid := le_refl 3
  shared_edges := k
  h_shared_bound := by simp only [Nat.min_self]; exact hk

/-- At k=0, symmetric bound has m² = 4/9 (matches symmetric_dressing_mass_sq). -/
theorem symmetric_bound_zero_mass_sq :
    (symmetricBound 0 (by omega)).massSq = 4/9 := by
  unfold symmetricBound BoundDressed.massSq bound_invariant_mass_sq
  simp only [Nat.cast_zero, sub_zero]
  norm_num

/-- At k=3, symmetric bound annihilates: m² = 0. -/
theorem symmetric_annihilation :
    (symmetricBound 3 (by omega)).massSq = 0 := by
  unfold symmetricBound BoundDressed.massSq bound_invariant_mass_sq
  simp only [sub_self, mul_zero, zero_div]

/-- The symmetric dressed electron is metastable: it can annihilate with enough binding. -/
theorem dressed_electron_metastable :
    (symmetricBound 0 (by omega)).massSq > 0 ∧
    (symmetricBound 3 (by omega)).massSq = 0 := by
  constructor
  · rw [symmetric_bound_zero_mass_sq]
    norm_num
  · exact symmetric_annihilation

/-! ## Partial Binding: Still Timelike -/

/-- For k < min(3, n), bound dressed electron remains timelike (m² > 0). -/
theorem partial_binding_still_timelike (e : BoundDressed)
    (h_partial : e.shared_edges < min 3 e.dressing_n) :
    e.massSq > 0 := by
  unfold BoundDressed.massSq bound_invariant_mass_sq
  have h_ge := e.h_valid
  have h3 : (3 : ℝ) > 0 := by norm_num
  have hn : (e.dressing_n : ℝ) > 0 := Nat.cast_pos.mpr (by omega : e.dressing_n > 0)
  have h_k_lt_3 : e.shared_edges < 3 :=
    Nat.lt_of_lt_of_le h_partial (Nat.min_le_left 3 e.dressing_n)
  have h_k_lt_n : e.shared_edges < e.dressing_n :=
    Nat.lt_of_lt_of_le h_partial (Nat.min_le_right 3 e.dressing_n)
  have h1 : (3 : ℝ) - e.shared_edges > 0 := by
    have : (e.shared_edges : ℝ) < 3 := Nat.cast_lt.mpr h_k_lt_3
    linarith
  have h2 : (e.dressing_n : ℝ) - e.shared_edges > 0 := by
    have : (e.shared_edges : ℝ) < e.dressing_n := Nat.cast_lt.mpr h_k_lt_n
    linarith
  have h_prod_sq_pos : ((3 : ℝ) * e.dressing_n)^2 > 0 := by positivity
  positivity

/-- The binding spectrum for symmetric dressing: m² decreases with k. -/
theorem symmetric_mass_spectrum (k : ℕ) (hk : k ≤ 3) :
    (symmetricBound k hk).massSq = 4 * (3 - k : ℝ)^2 / 81 := by
  unfold symmetricBound BoundDressed.massSq bound_invariant_mass_sq
  simp only [Nat.cast_ofNat]
  ring

/-- Each binding level has a specific mass. -/
theorem symmetric_mass_values :
    (symmetricBound 0 (by omega)).massSq = 4/9 ∧
    (symmetricBound 1 (by omega)).massSq = 16/81 ∧
    (symmetricBound 2 (by omega)).massSq = 4/81 ∧
    (symmetricBound 3 (by omega)).massSq = 0 := by
  constructor
  · exact symmetric_bound_zero_mass_sq
  constructor
  · rw [symmetric_mass_spectrum 1 (by omega)]
    norm_num
  constructor
  · rw [symmetric_mass_spectrum 2 (by omega)]
    norm_num
  · exact symmetric_annihilation

/-! ## Bound Dressed Velocity -/

/-- Velocity of a bound dressed electron. -/
noncomputable def BoundDressed.velocity (e : BoundDressed) : ℝ :=
  e.netMomentum / e.totalEnergy

/-- Symmetric bound dressing is always at rest (equal masses). -/
theorem symmetric_bound_at_rest (k : ℕ) (hk : k ≤ 3) (_hk_lt : k < 3) :
    (symmetricBound k hk).velocity = 0 := by
  unfold BoundDressed.velocity BoundDressed.netMomentum BoundDressed.totalEnergy
  unfold symmetricBound bound_total_momentum
  simp only [mass_of_cycle, sub_self, abs_zero, zero_div]

/-! ## The Annihilation Energy Barrier -/

/-- Energy released in going from binding k to binding k+1. -/
noncomputable def binding_energy_step (e : BoundDressed) : ℝ :=
  2 / (3 * e.dressing_n)

/-- Total energy released by complete annihilation of symmetric dressed electron. -/
theorem symmetric_annihilation_energy :
    (symmetricBound 0 (by omega)).totalEnergy - (symmetricBound 3 (by omega)).totalEnergy = 2/3 := by
  unfold symmetricBound BoundDressed.totalEnergy bound_total_energy
  unfold mass_of_cycle sharing_energy_reduction
  simp only [Nat.cast_zero, mul_zero, Nat.cast_ofNat]
  norm_num

/-! ## The Bound Dressed Electron Correspondence -/

/-- Summary: The complete bound dressed electron theory. -/
theorem the_bound_dressed_electron_correspondence :
    -- k=0 recovers unbound theory
    (∀ d : Dressed, (unboundDressed d).massSq = d.massSq) ∧
    -- Partial binding is still timelike
    (∀ e : BoundDressed, e.shared_edges < min 3 e.dressing_n → e.massSq > 0) ∧
    -- Symmetric dressing can annihilate
    ((symmetricBound 0 (by omega)).massSq > 0 ∧ (symmetricBound 3 (by omega)).massSq = 0) ∧
    -- Symmetric is always at rest (until annihilation)
    (∀ k : ℕ, ∀ hk : k ≤ 3, k < 3 → (symmetricBound k hk).velocity = 0) ∧
    -- Annihilation releases energy 2/3
    ((symmetricBound 0 (by omega)).totalEnergy - (symmetricBound 3 (by omega)).totalEnergy = 2/3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact bound_at_zero_is_unbound
  · exact partial_binding_still_timelike
  · exact dressed_electron_metastable
  · exact symmetric_bound_at_rest
  · exact symmetric_annihilation_energy

end Diaspora.Dynamics.BoundDressedElectron
