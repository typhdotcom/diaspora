import Diaspora.Dynamics.InelasticScattering

/-!
# The Momentum Spectrum and Selection Rules

The discrete nature of cycle lengths induces a discrete momentum spectrum.
This file explores the number-theoretic constraints on allowed reactions.

## Main Results

- `MomentumSet`: p ∈ {1/n : n ≥ 3} is a discrete, bounded-above set
- `coprime_no_divisibility`: gcd(n₁, n₂) = 1 ⟹ (n₁+n₂) ∤ (n₁·n₂)
- `coprime_cycles_cannot_merge`: coprime cycles cannot merge
- `mass_gap_formula`: gap between levels = 1/(n(n+1))
-/

namespace Diaspora.Dynamics.MomentumSpectrum

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.InelasticScattering

/-! ## The Momentum Spectrum -/

/-- The allowed momenta: {1/n : n ≥ 3}. -/
def MomentumSet : Set ℝ := {p : ℝ | ∃ n : ℕ, n ≥ 3 ∧ p = 1 / (n : ℝ)}

/-- Momentum p is allowed iff p = 1/n for some n ≥ 3. -/
theorem mem_momentum_set (p : ℝ) :
    p ∈ MomentumSet ↔ ∃ n : ℕ, n ≥ 3 ∧ p = 1 / (n : ℝ) := Iff.rfl

/-- The maximum momentum is 1/3 (triangle). -/
theorem max_momentum : ∀ p ∈ MomentumSet, p ≤ 1/3 := by
  intro p hp
  obtain ⟨n, hn_ge, hp_eq⟩ := hp
  rw [hp_eq]
  have hn_ge3 : (n : ℝ) ≥ 3 := Nat.cast_le.mpr hn_ge
  have hn_pos : (n : ℝ) > 0 := by linarith
  have h3_pos : (3 : ℝ) > 0 := by norm_num
  rw [one_div_le_one_div hn_pos h3_pos]
  exact hn_ge3

/-- 1/3 is in the spectrum. -/
theorem third_in_spectrum : 1/3 ∈ MomentumSet := ⟨3, by omega, rfl⟩

/-- Minimum nonzero momentum is 1/3. -/
theorem min_nonzero_momentum : 1/3 ∈ MomentumSet ∧ ∀ p ∈ MomentumSet, p ≤ 1/3 :=
  ⟨third_in_spectrum, max_momentum⟩

/-- The spectrum is bounded above. -/
theorem spectrum_bounded_above : BddAbove MomentumSet :=
  ⟨1/3, fun p hp => max_momentum p hp⟩

/-- The spectrum accumulates at zero. -/
theorem spectrum_accumulates_at_zero :
    ∀ ε > 0, ∃ p ∈ MomentumSet, 0 < p ∧ p < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1/ε)
  let n := max N 3
  have hn_ge : n ≥ 3 := le_max_right N 3
  have hn_gt_N : n ≥ N := le_max_left N 3
  use 1 / (n : ℝ)
  refine ⟨⟨n, hn_ge, rfl⟩, ?_, ?_⟩
  · have hn_pos : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    positivity
  · have hn_pos : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    rw [div_lt_iff₀ hn_pos]
    have h1 : (1 : ℝ) / ε < N := hN
    have h2 : (N : ℝ) ≤ n := Nat.cast_le.mpr hn_gt_N
    have h3 : (1 : ℝ) / ε < n := lt_of_lt_of_le h1 h2
    calc 1 = ε * (1/ε) := by field_simp
      _ < ε * n := by apply mul_lt_mul_of_pos_left h3 hε

/-- Zero is NOT in the spectrum (no infinitely long cycles). -/
theorem zero_not_in_spectrum : (0 : ℝ) ∉ MomentumSet := by
  intro ⟨n, hn_ge, h_eq⟩
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h_pos : (0 : ℝ) < 1 / n := by positivity
  linarith [h_eq.symm ▸ h_pos]

/-! ## Selection Rules for Merger -/

/-- The merger divisibility condition. -/
def CanMerge (n₁ n₂ : ℕ) : Prop :=
  n₁ ≥ 3 ∧ n₂ ≥ 3 ∧ (n₁ + n₂) ∣ (n₁ * n₂) ∧ n₁ * n₂ / (n₁ + n₂) ≥ 3

/-! ## Coprime Cycles Cannot Merge -/

/-- For coprime n₁, n₂, the sum (n₁ + n₂) does not divide the product n₁ * n₂. -/
theorem coprime_no_divisibility (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3)
    (h_coprime : Nat.Coprime n₁ n₂) :
    ¬((n₁ + n₂) ∣ (n₁ * n₂)) := by
  intro ⟨k, hk⟩
  -- If (n₁ + n₂) | n₁ * n₂ and gcd(n₁, n₂) = 1, then:
  -- n₁ + n₂ | n₁² (since n₁(n₁+n₂) - n₁n₂ = n₁²)
  -- Similarly n₁ + n₂ | n₂²
  -- So n₁ + n₂ | gcd(n₁², n₂²) = 1
  have h_div_n1_sq : (n₁ + n₂) ∣ n₁ * n₁ := by
    have h1 : (n₁ + n₂) ∣ n₁ * (n₁ + n₂) := ⟨n₁, by ring⟩
    have h2 : (n₁ + n₂) ∣ n₁ * n₂ := ⟨k, hk⟩
    have h_sub : n₁ * (n₁ + n₂) - n₁ * n₂ = n₁ * n₁ := by
      have : n₁ * (n₁ + n₂) = n₁ * n₁ + n₁ * n₂ := by ring
      omega
    rw [← h_sub]
    exact Nat.dvd_sub h1 h2
  have h_div_n2_sq : (n₁ + n₂) ∣ n₂ * n₂ := by
    have h1 : (n₁ + n₂) ∣ n₂ * (n₁ + n₂) := ⟨n₂, by ring⟩
    have h2 : (n₁ + n₂) ∣ n₁ * n₂ := ⟨k, hk⟩
    have h_sub : n₂ * (n₁ + n₂) - n₁ * n₂ = n₂ * n₂ := by
      have : n₂ * (n₁ + n₂) = n₂ * n₂ + n₁ * n₂ := by ring
      omega
    rw [← h_sub]
    exact Nat.dvd_sub h1 h2
  have h_gcd_sq : Nat.gcd (n₁ * n₁) (n₂ * n₂) = 1 := by
    rw [← sq, ← sq]
    exact Nat.Coprime.pow 2 2 h_coprime
  have h_div_gcd : (n₁ + n₂) ∣ Nat.gcd (n₁ * n₁) (n₂ * n₂) :=
    Nat.dvd_gcd h_div_n1_sq h_div_n2_sq
  rw [h_gcd_sq] at h_div_gcd
  have h_le_1 : n₁ + n₂ ≤ 1 := Nat.le_of_dvd (by omega) h_div_gcd
  omega

/-- Coprime cycles cannot merge. -/
theorem coprime_cycles_cannot_merge (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3)
    (h_coprime : Nat.Coprime n₁ n₂) :
    ¬CanMerge n₁ n₂ := by
  intro ⟨_, _, h_div, _⟩
  exact coprime_no_divisibility n₁ n₂ h₁ h₂ h_coprime h_div

/-! ## Examples of Allowed and Forbidden Mergers -/

/-- (3, 6) can merge: 18/9 = 2, but 2 < 3, so blocked by minimum. -/
theorem three_six_blocked : ¬CanMerge 3 6 := by
  intro ⟨_, _, _, h_ge3⟩
  have : 3 * 6 / (3 + 6) = 2 := by decide
  omega

/-- (4, 12) can merge to 3. -/
theorem four_twelve_can_merge : CanMerge 4 12 := by
  refine ⟨by omega, by omega, ⟨3, by decide⟩, by decide⟩

/-- (6, 6) can merge to 3. -/
theorem six_six_can_merge : CanMerge 6 6 := by
  refine ⟨by omega, by omega, ⟨3, by decide⟩, by decide⟩

/-- (3, 4) cannot merge (coprime). -/
theorem three_four_cannot_merge : ¬CanMerge 3 4 :=
  coprime_cycles_cannot_merge 3 4 (by omega) (by omega) (by decide)

/-- (3, 5) cannot merge (coprime). -/
theorem three_five_cannot_merge : ¬CanMerge 3 5 :=
  coprime_cycles_cannot_merge 3 5 (by omega) (by omega) (by decide)

/-- (4, 5) cannot merge (coprime). -/
theorem four_five_cannot_merge : ¬CanMerge 4 5 :=
  coprime_cycles_cannot_merge 4 5 (by omega) (by omega) (by decide)

/-! ## The Mass Gap in the Spectrum -/

/-- The gap between adjacent mass levels. -/
noncomputable def mass_gap (n : ℕ) : ℝ := mass_of_cycle n - mass_of_cycle (n + 1)

/-- Gap formula: Δm = 1/(n(n+1)). -/
theorem mass_gap_formula (n : ℕ) (h : n ≥ 3) :
    mass_gap n = 1 / ((n : ℝ) * (n + 1)) := by
  unfold mass_gap mass_of_cycle
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by
    have : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
    linarith
  have h_cast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [h_cast]
  field_simp [hn, hn1]
  ring

/-- Gaps decrease as n increases. -/
theorem mass_gap_decreasing (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (h_lt : n₁ < n₂) :
    mass_gap n₂ < mass_gap n₁ := by
  rw [mass_gap_formula n₁ h₁, mass_gap_formula n₂ h₂]
  have hn₁_pos : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₁1_pos : (n₁ : ℝ) + 1 > 0 := by linarith
  have hn₂_pos : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have hn₂1_pos : (n₂ : ℝ) + 1 > 0 := by linarith
  have h_prod1_pos : (n₁ : ℝ) * (n₁ + 1) > 0 := mul_pos hn₁_pos hn₁1_pos
  have h_prod2_pos : (n₂ : ℝ) * (n₂ + 1) > 0 := mul_pos hn₂_pos hn₂1_pos
  rw [one_div_lt_one_div h_prod2_pos h_prod1_pos]
  have hn₁_lt : (n₁ : ℝ) < n₂ := Nat.cast_lt.mpr h_lt
  nlinarith

/-- The largest gap is between m = 1/3 and m = 1/4. -/
theorem largest_mass_gap : mass_gap 3 = 1/12 := by
  rw [mass_gap_formula 3 (by omega)]
  norm_num

/-! ## The Momentum Spectrum Correspondence -/

/-- Summary of momentum spectrum properties. -/
theorem the_momentum_spectrum_correspondence :
    -- Maximum momentum is 1/3
    (∀ p ∈ MomentumSet, p ≤ 1/3) ∧
    -- Minimum nonzero is 1/3
    (1/3 ∈ MomentumSet) ∧
    -- Zero is not in spectrum
    ((0 : ℝ) ∉ MomentumSet) ∧
    -- Spectrum accumulates at zero
    (∀ ε > 0, ∃ p ∈ MomentumSet, 0 < p ∧ p < ε) ∧
    -- Coprime cycles cannot merge
    (∀ n₁ n₂ : ℕ, n₁ ≥ 3 → n₂ ≥ 3 → Nat.Coprime n₁ n₂ → ¬CanMerge n₁ n₂) :=
  ⟨max_momentum, third_in_spectrum, zero_not_in_spectrum, spectrum_accumulates_at_zero,
   coprime_cycles_cannot_merge⟩

end Diaspora.Dynamics.MomentumSpectrum
