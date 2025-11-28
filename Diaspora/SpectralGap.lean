/-
# Spectral Gap Theorem

Non-trivial first cohomology class implies strictly positive energy lower bound.

If γ is harmonic with non-zero integer winding m on an n-cycle, then:
  ‖γ‖² = m²/n ≥ 1/n
-/

import Diaspora.HarmonicAnalysis
import Diaspora.Resilience

namespace DiscreteHodge

open BigOperators

/-! ## Helper Lemmas -/

/-- Non-zero integer has square at least 1. -/
lemma int_sq_ge_one (m : ℤ) (h : m ≠ 0) : (m : ℝ)^2 ≥ 1 := by
  have h_abs : |m| ≥ 1 := Int.one_le_abs h
  have h_m_sq : m^2 ≥ 1 := by nlinarith [sq_abs m]
  exact_mod_cast h_m_sq

/-- Zero form has zero holonomy on any chain. -/
lemma holonomy_zero_form {n : ℕ} [Fintype (Fin n)] (c : Chain1 n) :
    holonomy ({ val := fun _ _ => 0, skew := fun _ _ => by ring } : C1 n) c = 0 := by
  unfold holonomy eval
  simp

/-- If a form is identically zero, its holonomy on any chain is zero. -/
lemma holonomy_of_zero_val {n : ℕ} [Fintype (Fin n)] (γ : C1 n) (c : Chain1 n)
    (h_zero : ∀ i j, γ.val i j = 0) :
    holonomy γ c = 0 := by
  unfold holonomy eval
  simp only [h_zero, zero_mul, Finset.sum_const_zero, mul_zero]

/-! ## Non-trivial Cohomology -/

/-- A harmonic form has non-trivial cohomology if it has non-zero holonomy on some cycle. -/
def HasNontrivialCohomology {n : ℕ} [Fintype (Fin n)] (γ : C1 n) : Prop :=
  IsHarmonic γ ∧ ∃ c : Chain1 n, Chain1.IsCycle c ∧ holonomy γ c ≠ 0

/-! ## Qualitative Spectral Gap -/

/-- Spectral Gap (Qualitative): Non-trivial cohomology implies positive energy.

  Proof: By contradiction. If ‖γ‖² = 0, then γ = 0 (by norm_sq_zero_iff_zero),
  but then holonomy γ c = 0 for all chains, contradicting non-trivial cohomology.
-/
theorem spectral_gap_qualitative {n : ℕ} [Fintype (Fin n)]
    (γ : C1 n) (h : HasNontrivialCohomology γ) : norm_sq γ > 0 := by
  by_contra h_not_pos
  push_neg at h_not_pos
  have h_zero : norm_sq γ = 0 := le_antisymm h_not_pos (norm_sq_nonneg γ)
  have h_val_zero : ∀ i j, γ.val i j = 0 := norm_sq_zero_iff_zero γ h_zero
  obtain ⟨_, c, _, h_hol_ne⟩ := h
  have h_hol_zero : holonomy γ c = 0 := holonomy_of_zero_val γ c h_val_zero
  exact h_hol_ne h_hol_zero

/-! ## Quantitative Spectral Gap -/

/-- Spectral Gap (Quantitative): For cycle-supported harmonic forms with integer winding m ≠ 0,
    energy is bounded below by 1/n.

  Builds directly on quantized_energy_spectrum: ‖γ‖² = m²/n, and m² ≥ 1.
-/
theorem spectral_gap_quantitative {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (cycle : SimpleCycle n) (γ : C1 n)
    (h_harm : IsHarmonic γ)
    (h_support : SupportedOnCycle cycle γ)
    (m : ℤ) (h_m_ne : m ≠ 0)
    (h_winding : holonomy γ (SimpleCycle.toChain1 cycle) = m)
    (h_n_ge_3 : n ≥ 3) :
    norm_sq γ ≥ 1 / (Fintype.card (Fin n)) := by
  have h_spectrum := quantized_energy_spectrum cycle γ h_harm h_support m h_winding h_n_ge_3
  rw [h_spectrum]
  have h_m_sq : (m : ℝ)^2 ≥ 1 := int_sq_ge_one m h_m_ne
  have h_n_pos : (0 : ℝ) < Fintype.card (Fin n) := by
    have h1 : 0 < n := NeZero.pos n
    have h2 : Fintype.card (Fin n) = n := by convert Fintype.card_fin n
    rw [h2]
    exact Nat.cast_pos.mpr h1
  exact div_le_div_of_nonneg_right h_m_sq (le_of_lt h_n_pos)

/-! ## Main Theorem: Soliton Lower Bound -/

/-- For harmonic form with integer winding m ≠ 0 on an n-cycle:
    ‖γ‖² = m²/n and ‖γ‖² ≥ 1/n. -/
theorem soliton_lower_bound {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (cycle : SimpleCycle n) (γ : C1 n)
    (h_harm : IsHarmonic γ)
    (h_support : SupportedOnCycle cycle γ)
    (m : ℤ) (h_m_ne : m ≠ 0)
    (h_winding : holonomy γ (SimpleCycle.toChain1 cycle) = m)
    (h_n_ge_3 : n ≥ 3) :
    norm_sq γ = (m : ℝ)^2 / n ∧ norm_sq γ ≥ 1 / n := by
  have h_card : Fintype.card (Fin n) = n := by convert Fintype.card_fin n
  constructor
  · -- Exact value from quantized_energy_spectrum
    have h := quantized_energy_spectrum cycle γ h_harm h_support m h_winding h_n_ge_3
    simp only [h_card] at h
    exact h
  · -- Lower bound from spectral_gap_quantitative
    have h := spectral_gap_quantitative cycle γ h_harm h_support m h_m_ne h_winding h_n_ge_3
    simp only [h_card] at h
    exact h

end DiscreteHodge
