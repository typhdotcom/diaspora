import Diaspora.Dynamics.MomentumSpectrum

/-!
# GCD Characterization of Cycle Merger

The divisibility condition for merger has a beautiful number-theoretic characterization
in terms of the greatest common divisor.

## Main Results

- `gcd_merger_criterion`: (n₁+n₂) | n₁n₂ iff (a+b) | g, where n₁ = ga, n₂ = gb, gcd(a,b) = 1
- `merger_requires_gcd_bound`: Merger requires gcd(n₁,n₂) ≥ (n₁/g + n₂/g)
- `merged_length_gcd_formula`: n₃ = g·a·b / (a+b) when merger is valid
- `minimum_gcd_merger`: When g = a+b exactly, n₃ = a·b
- `triangle_producers`: Complete characterization of pairs that produce n₃ = 3
-/

namespace Diaspora.Dynamics.MergerGCD

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.InelasticScattering
open Diaspora.Dynamics.MomentumSpectrum

/-! ## GCD Decomposition -/

/-- Decompose n₁, n₂ into gcd form: n₁ = g·a, n₂ = g·b with gcd(a,b) = 1. -/
structure GCDDecomp (n₁ n₂ : ℕ) where
  g : ℕ
  a : ℕ
  b : ℕ
  h_g_pos : g > 0
  h_a_pos : a > 0
  h_b_pos : b > 0
  h_n1 : n₁ = g * a
  h_n2 : n₂ = g * b
  h_coprime : Nat.Coprime a b

/-- Every pair of positive naturals has a GCD decomposition. -/
def gcd_decomp (n₁ n₂ : ℕ) (h₁ : n₁ > 0) (h₂ : n₂ > 0) : GCDDecomp n₁ n₂ where
  g := Nat.gcd n₁ n₂
  a := n₁ / Nat.gcd n₁ n₂
  b := n₂ / Nat.gcd n₁ n₂
  h_g_pos := Nat.gcd_pos_of_pos_left n₂ h₁
  h_a_pos := Nat.div_pos (Nat.gcd_le_left n₂ h₁) (Nat.gcd_pos_of_pos_left n₂ h₁)
  h_b_pos := Nat.div_pos (Nat.gcd_le_right n₁ h₂) (Nat.gcd_pos_of_pos_left n₂ h₁)
  h_n1 := by
    have h := Nat.div_mul_cancel (Nat.gcd_dvd_left n₁ n₂)
    -- h : n₁ / gcd * gcd = n₁, need n₁ = gcd * (n₁ / gcd)
    rw [mul_comm] at h
    exact h.symm
  h_n2 := by
    have h := Nat.div_mul_cancel (Nat.gcd_dvd_right n₁ n₂)
    rw [mul_comm] at h
    exact h.symm
  h_coprime := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left n₂ h₁)

/-! ## Key Number-Theoretic Lemma -/

/-- For coprime a, b: gcd(ab, a+b) = 1. -/
theorem coprime_prod_sum (a b : ℕ) (h : Nat.Coprime a b) : Nat.Coprime (a * b) (a + b) := by
  have ha : Nat.Coprime a (a + b) := by
    rw [Nat.coprime_comm, Nat.Coprime]
    rw [add_comm, Nat.gcd_add_self_left, Nat.gcd_comm]
    exact h
  have hb : Nat.Coprime b (a + b) := by
    rw [Nat.coprime_comm, Nat.Coprime]
    rw [Nat.gcd_add_self_left]
    exact h
  rw [Nat.coprime_comm] at ha hb ⊢
  exact Nat.Coprime.mul_right ha hb

/-! ## The Main Divisibility Criterion -/

/-- The divisibility condition in GCD form: (n₁+n₂) | n₁n₂ iff (a+b) | g. -/
theorem gcd_merger_criterion (n₁ n₂ : ℕ) (h₁ : n₁ > 0) (h₂ : n₂ > 0) :
    let d := gcd_decomp n₁ n₂ h₁ h₂
    (n₁ + n₂) ∣ (n₁ * n₂) ↔ (d.a + d.b) ∣ d.g := by
  -- Use raw definitions to avoid dependent type issues
  let g := Nat.gcd n₁ n₂
  let a := n₁ / g
  let b := n₂ / g
  have h_g_pos : g > 0 := Nat.gcd_pos_of_pos_left n₂ h₁
  have h_a_pos : a > 0 := Nat.div_pos (Nat.gcd_le_left n₂ h₁) h_g_pos
  have h_b_pos : b > 0 := Nat.div_pos (Nat.gcd_le_right n₁ h₂) h_g_pos
  have h_coprime : Nat.Coprime a b := Nat.coprime_div_gcd_div_gcd h_g_pos
  have hdvd1 := Nat.gcd_dvd_left n₁ n₂
  have hdvd2 := Nat.gcd_dvd_right n₁ n₂
  have h1 := Nat.div_mul_cancel hdvd1
  have h2 := Nat.div_mul_cancel hdvd2
  have h_sum : n₁ + n₂ = g * (a + b) := by
    calc n₁ + n₂
        = a * g + b * g := by rw [h1, h2]
      _ = g * (a + b) := by ring
  have h_prod : n₁ * n₂ = g * g * (a * b) := by
    calc n₁ * n₂
        = (a * g) * (b * g) := by rw [h1, h2]
      _ = g * g * (a * b) := by ring
  -- The result is for the let-bound d which equals (g, a, b)
  -- Note: d.a = a, d.b = b, d.g = g by definition
  show (n₁ + n₂) ∣ (n₁ * n₂) ↔ (a + b) ∣ g
  constructor
  · -- (→) If g(a+b) | g²ab, then (a+b) | g
    intro h_div
    rw [h_sum, h_prod] at h_div
    -- g(a+b) | g²ab means ∃k, g²ab = g(a+b)·k
    obtain ⟨k, hk⟩ := h_div
    -- g·ab = k·(a+b) after canceling g
    have h_cancel : g * (a * b) = k * (a + b) := by
      have hk' : g * g * (a * b) = g * (a + b) * k := hk
      have h_factor : g * g * (a * b) = g * (g * (a * b)) := by ring
      have h_factor2 : g * (a + b) * k = g * (k * (a + b)) := by ring
      rw [h_factor, h_factor2] at hk'
      exact Nat.eq_of_mul_eq_mul_left h_g_pos hk'
    -- So (a+b) | g·ab. Since gcd(ab, a+b) = 1, we get (a+b) | g.
    have h_coprime_prod := coprime_prod_sum a b h_coprime
    have h_dvd_gab : (a + b) ∣ g * (a * b) := by
      use k
      calc g * (a * b) = k * (a + b) := h_cancel
        _ = (a + b) * k := by ring
    have h_mul_comm : g * (a * b) = a * b * g := by ring
    rw [h_mul_comm] at h_dvd_gab
    exact Nat.Coprime.dvd_of_dvd_mul_left h_coprime_prod.symm h_dvd_gab
  · -- (←) If (a+b) | g, then g(a+b) | g²ab
    intro h_div
    rw [h_sum, h_prod]
    -- (a+b) | g means g = m(a+b) for some m
    obtain ⟨m, hm⟩ := h_div
    use m * (a * b)
    have hg_eq : g = (a + b) * m := by
      -- hm : n₁.gcd n₂ = (n₁ / n₁.gcd n₂ + n₂ / n₁.gcd n₂) * m
      -- but g = n₁.gcd n₂ and a + b = n₁ / n₁.gcd n₂ + n₂ / n₁.gcd n₂
      exact hm
    calc g * g * (a * b)
        = (a + b) * m * ((a + b) * m) * (a * b) := by rw [hg_eq]
      _ = g * (a + b) * (m * (a * b)) := by rw [hg_eq]; ring

/-- Merger requires the gcd to be at least a + b. -/
theorem merger_requires_gcd_bound (n₁ n₂ : ℕ) (h₁ : n₁ > 0) (h₂ : n₂ > 0)
    (h_div : (n₁ + n₂) ∣ (n₁ * n₂)) :
    let d := gcd_decomp n₁ n₂ h₁ h₂
    d.g ≥ d.a + d.b := by
  intro d
  have h_crit := (gcd_merger_criterion n₁ n₂ h₁ h₂).mp h_div
  have h_sum_pos : d.a + d.b > 0 := Nat.add_pos_left d.h_a_pos d.b
  exact Nat.le_of_dvd d.h_g_pos h_crit

/-! ## Merged Length Formula -/

/-- The merged length in terms of gcd decomposition. -/
theorem merged_length_gcd_formula (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3)
    (h_div : (n₁ + n₂) ∣ (n₁ * n₂)) :
    let d := gcd_decomp n₁ n₂ (by omega) (by omega)
    n₁ * n₂ / (n₁ + n₂) = d.g / (d.a + d.b) * (d.a * d.b) := by
  -- Work with raw definitions
  let g := Nat.gcd n₁ n₂
  let a := n₁ / g
  let b := n₂ / g
  have h_g_pos : g > 0 := Nat.gcd_pos_of_pos_left n₂ (by omega)
  have h_a_pos : a > 0 := Nat.div_pos (Nat.gcd_le_left n₂ (by omega : n₁ > 0)) h_g_pos
  have h_b_pos : b > 0 := Nat.div_pos (Nat.gcd_le_right n₁ (by omega : n₂ > 0)) h_g_pos
  have hdvd1 := Nat.gcd_dvd_left n₁ n₂
  have hdvd2 := Nat.gcd_dvd_right n₁ n₂
  have h1 := Nat.div_mul_cancel hdvd1
  have h2 := Nat.div_mul_cancel hdvd2
  have h_sum : n₁ + n₂ = g * (a + b) := by
    calc n₁ + n₂ = a * g + b * g := by rw [h1, h2]
      _ = g * (a + b) := by ring
  have h_prod : n₁ * n₂ = g * g * (a * b) := by
    calc n₁ * n₂ = (a * g) * (b * g) := by rw [h1, h2]
      _ = g * g * (a * b) := by ring
  have h_crit := (gcd_merger_criterion n₁ n₂ (by omega) (by omega)).mp h_div
  obtain ⟨m, hm⟩ := h_crit
  have hg_eq : g = (a + b) * m := hm
  rw [h_sum, h_prod]
  have h_sum_pos : a + b > 0 := Nat.add_pos_left h_a_pos b
  -- g² ab / g(a+b) = g·ab / (a+b) = m·ab when g = m(a+b)
  calc g * g * (a * b) / (g * (a + b))
      = g * (a * b) / (a + b) := by
        rw [Nat.mul_assoc, Nat.mul_div_mul_left _ _ h_g_pos]
    _ = (a + b) * m * (a * b) / (a + b) := by rw [hg_eq]
    _ = m * (a * b) := by
        have : (a + b) * m * (a * b) = (a + b) * (m * (a * b)) := by ring
        rw [this]
        exact Nat.mul_div_cancel_left (m * (a * b)) h_sum_pos
    _ = g / (a + b) * (a * b) := by
        have hm_eq : m = g / (a + b) := by
          rw [hg_eq]
          exact (Nat.mul_div_cancel_left m h_sum_pos).symm
        rw [hm_eq]

/-- At minimum gcd (g = a+b), the merged length is simply ab. -/
theorem minimum_gcd_merger (a b : ℕ) (ha : a > 0) (_hb : b > 0) (_h_coprime : Nat.Coprime a b)
    (n₁ n₂ : ℕ) (h_n1 : n₁ = (a + b) * a) (h_n2 : n₂ = (a + b) * b) :
    n₁ * n₂ / (n₁ + n₂) = a * b := by
  -- n₁ + n₂ = (a+b)a + (a+b)b = (a+b)²
  have h_sum : n₁ + n₂ = (a + b) * (a + b) := by rw [h_n1, h_n2]; ring
  -- n₁ * n₂ = (a+b)a * (a+b)b = (a+b)² ab
  have h_prod : n₁ * n₂ = (a + b) * (a + b) * (a * b) := by rw [h_n1, h_n2]; ring
  have h_sum_pos : a + b > 0 := Nat.add_pos_left ha b
  have h_sq_pos : (a + b) * (a + b) > 0 := Nat.mul_pos h_sum_pos h_sum_pos
  rw [h_sum, h_prod]
  exact Nat.mul_div_cancel_left (a * b) h_sq_pos

/-! ## Triangle Production -/

/-- A pair (n₁, n₂) that produces a triangle (n₃ = 3) under merger. -/
structure TriangleProducer where
  n₁ : ℕ
  n₂ : ℕ
  h₁ : n₁ ≥ 3
  h₂ : n₂ ≥ 3
  h_valid : merger_valid n₁ n₂ 3

/-- 4 + 12 produces a triangle. -/
def four_twelve_triangle : TriangleProducer where
  n₁ := 4
  n₂ := 12
  h₁ := by omega
  h₂ := by omega
  h_valid := four_twelve_merger

/-- 6 + 6 produces a triangle. -/
def six_six_triangle : TriangleProducer where
  n₁ := 6
  n₂ := 6
  h₁ := by omega
  h₂ := by omega
  h_valid := six_six_merger

/-- The two fundamental triangle-producing pairs are (6,6) and (4,12). -/
theorem triangle_production_characterization :
    -- The two fundamental triangle-producing pairs
    (merger_valid 6 6 3) ∧
    (merger_valid 4 12 3) ∧
    -- These correspond to the two factorizations of 3
    -- 3 = 3 × 1 (from ab = 1, m = 3) and 3 = 1 × 3 (from ab = 3, m = 1)
    True := by
  refine ⟨six_six_merger, four_twelve_merger, trivial⟩

/-- Merger to n₃ = 3 requires (n₁, n₂) ∈ {(4, 12), (6, 6)} (up to ordering). -/
theorem triangle_requires_specific_pairs (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3)
    (h₁_le : n₁ ≤ n₂) (h_valid : merger_valid n₁ n₂ 3) :
    (n₁ = 4 ∧ n₂ = 12) ∨ (n₁ = 6 ∧ n₂ = 6) := by
  -- n₃ = 3 means n₁n₂/(n₁+n₂) = 3, so n₁n₂ = 3(n₁+n₂)
  have h_eq := h_valid.2  -- (n₁ : ℝ) * n₂ / (n₁ + n₂) = 3
  -- Convert to ℕ equation: n₁n₂ = 3(n₁+n₂)
  have h_nat : n₁ * n₂ = 3 * (n₁ + n₂) := by
    have h_sum_ne : (n₁ : ℝ) + n₂ ≠ 0 := by positivity
    have h_real : (n₁ : ℝ) * n₂ = 3 * (n₁ + n₂) := by
      have h' := h_eq
      field_simp [h_sum_ne] at h'
      calc (n₁ : ℝ) * n₂ = (n₁ + n₂) * 3 := h'
        _ = 3 * (n₁ + n₂) := by ring
    have h_lhs : ((n₁ * n₂ : ℕ) : ℝ) = (n₁ : ℝ) * n₂ := by push_cast; ring
    have h_rhs : ((3 * (n₁ + n₂) : ℕ) : ℝ) = 3 * ((n₁ : ℝ) + n₂) := by push_cast; ring
    rw [← h_lhs, ← h_rhs] at h_real
    exact Nat.cast_injective h_real
  -- Factor: (n₁ - 3)(n₂ - 3) = 9
  have h_factor : (n₁ - 3) * (n₂ - 3) = 9 := by
    -- Cast to Int for proper subtraction handling
    have hn₁_ge : (n₁ : ℤ) ≥ 3 := by exact_mod_cast h₁
    have hn₂_ge : (n₂ : ℤ) ≥ 3 := by exact_mod_cast h₂
    have h1 : ((n₁ - 3 : ℕ) : ℤ) = (n₁ : ℤ) - 3 := Int.ofNat_sub h₁
    have h2 : ((n₂ - 3 : ℕ) : ℤ) = (n₂ : ℤ) - 3 := Int.ofNat_sub h₂
    have h_eq : (n₁ : ℤ) * n₂ = 3 * (n₁ + n₂) := by exact_mod_cast h_nat
    have h_cast : (((n₁ - 3) * (n₂ - 3) : ℕ) : ℤ) = (9 : ℤ) := by
      push_cast
      rw [h1, h2]
      linarith
    exact Int.ofNat_inj.mp h_cast
  -- 9 = 1 × 9 = 3 × 3 (since n₁ ≤ n₂, we have n₁ - 3 ≤ n₂ - 3)
  have h_le_diff : n₁ - 3 ≤ n₂ - 3 := Nat.sub_le_sub_right h₁_le 3
  have h_pos1 : n₁ - 3 > 0 := by
    by_contra h_zero
    push_neg at h_zero
    have : n₁ - 3 = 0 := Nat.le_zero.mp h_zero
    simp [this] at h_factor
  -- The divisors of 9 with product = 9 and ≤ relation are (1,9) and (3,3)
  have h_cases : (n₁ - 3 = 1 ∧ n₂ - 3 = 9) ∨ (n₁ - 3 = 3 ∧ n₂ - 3 = 3) := by
    have h_upper : n₁ - 3 ≤ 3 := by
      -- (n₁-3)² ≤ (n₁-3)(n₂-3) = 9, so n₁-3 ≤ 3
      have hsq : (n₁ - 3) * (n₁ - 3) ≤ (n₁ - 3) * (n₂ - 3) :=
        Nat.mul_le_mul_left (n₁ - 3) h_le_diff
      rw [h_factor] at hsq
      nlinarith [h_pos1]
    -- Since (n₁-3) ∈ {1,2,3} and divides 9, we have (n₁-3) ∈ {1,3}
    have h_dvd : (n₁ - 3) ∣ 9 := by
      use n₂ - 3
      -- Need to show 9 = (n₁ - 3) * (n₂ - 3)
      exact h_factor.symm
    have h_val : n₁ - 3 = 1 ∨ n₁ - 3 = 3 := by
      have h1 : n₁ - 3 ≥ 1 := h_pos1
      rcases Nat.eq_or_lt_of_le h_upper with h3 | hlt3
      · right; exact h3
      · rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hlt3) with h2 | hlt2
        · -- n₁ - 3 = 2, but 2 ∤ 9
          exfalso
          have : 2 ∣ 9 := h2 ▸ h_dvd
          omega
        · left; omega
    rcases h_val with h1 | h3
    · left; constructor; exact h1
      have : 1 * (n₂ - 3) = 9 := by
        calc 1 * (n₂ - 3) = (n₂ - 3) * 1 := by ring
          _ = (n₂ - 3) * (n₁ - 3) := by rw [h1]
          _ = (n₁ - 3) * (n₂ - 3) := mul_comm _ _
          _ = 9 := h_factor
      omega
    · right; constructor; exact h3
      have : 3 * (n₂ - 3) = 9 := by
        calc 3 * (n₂ - 3) = (n₂ - 3) * 3 := by ring
          _ = (n₂ - 3) * (n₁ - 3) := by rw [h3]
          _ = (n₁ - 3) * (n₂ - 3) := mul_comm _ _
          _ = 9 := h_factor
      omega
  cases h_cases with
  | inl h => left; omega
  | inr h => right; omega

/-! ## The Merger GCD Correspondence -/

/-- Summary of the GCD characterization of merger. -/
theorem the_merger_gcd_correspondence (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    let d := gcd_decomp n₁ n₂ (by omega) (by omega)
    -- Divisibility criterion in GCD form
    ((n₁ + n₂) ∣ (n₁ * n₂) ↔ (d.a + d.b) ∣ d.g) ∧
    -- Coprime cycles cannot merge (special case: g = 1, a + b ≥ 6)
    (d.g = 1 → ¬(n₁ + n₂) ∣ (n₁ * n₂)) ∧
    -- Triangle production requires specific structure
    (merger_valid 6 6 3 ∧ merger_valid 4 12 3) := by
  intro d
  have h_crit := gcd_merger_criterion n₁ n₂ (by omega) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · exact h_crit
  · intro h_g_eq_1 h_div
    have h_ab_dvd_g := h_crit.mp h_div
    have h_le := Nat.le_of_dvd d.h_g_pos h_ab_dvd_g
    have h_sum : d.a + d.b ≥ 2 := Nat.add_le_add d.h_a_pos d.h_b_pos
    have : d.a + d.b ≤ 1 := by rw [h_g_eq_1] at h_le; exact h_le
    omega
  · exact ⟨six_six_merger, four_twelve_merger⟩

end Diaspora.Dynamics.MergerGCD
