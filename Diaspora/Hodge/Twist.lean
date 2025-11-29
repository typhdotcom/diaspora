/-
# Dehn Twist Operator

Given a cycle, construct a harmonic form with non-trivial winding number.
-/

import Diaspora.Hodge.Harmonic

open BigOperators Diaspora.Core

namespace Diaspora.Hodge

/-! ## The Dehn Twist Construction -/

/-- The Dehn twist along a simple cycle: creates a harmonic form with winding 1.
    Value 1/n on each forward edge (non-period-2), skew-symmetric by definition.
    For n ≥ 3, gives non-trivial harmonic form; for n = 2 (period-2), degenerates to zero. -/
noncomputable def dehn_twist {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (cycle : SimpleCycle n) : C1 n where
  val := fun i j =>
    if j = cycle.next i ∧ i ≠ cycle.next j then 1 / n
    else if i = cycle.next j ∧ j ≠ cycle.next i then -(1 / n)
    else 0
  skew := by
    intro i j
    split_ifs with h1 h2
    · exact absurd h2.1 h1.2
    · ring
    · ring
    · ring

/-! ## Properties of the Dehn Twist -/

/-- Helper: n ≥ 3 implies prev ≠ next for any vertex -/
lemma prev_ne_next_of_n_ge_3 {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3) (v : Fin n) :
    cycle.prev v ≠ cycle.next v := by
  intro h_eq
  have h_period : cycle.next (cycle.next v) = v := by
    calc cycle.next (cycle.next v)
        = cycle.next (cycle.prev v) := by rw [h_eq]
      _ = v := cycle.next_prev v
  have h_card : Fintype.card (Fin n) ≤ 2 := by
    classical
    have h_all : ∀ k : Fin n, k = v ∨ k = cycle.next v := by
      intro k
      have h_conn := cycle.connected v k
      obtain ⟨m, hm⟩ := h_conn
      induction m generalizing k with
      | zero => left; simp only [Function.iterate_zero, id_eq] at hm; exact hm.symm
      | succ m' ih =>
        simp only [Function.iterate_succ_apply'] at hm
        specialize ih (cycle.next^[m'] v) rfl
        cases ih with
        | inl h => right; rw [← hm, h]
        | inr h => left; rw [← hm, h, h_period]
    have h_subset : (Finset.univ : Finset (Fin n)) ⊆ {v, cycle.next v} := by
      intro k _; simp [h_all k]
    calc Fintype.card (Fin n) = Finset.card Finset.univ := (Finset.card_univ).symm
      _ ≤ Finset.card {v, cycle.next v} := Finset.card_le_card h_subset
      _ ≤ 2 := Finset.card_le_two
  have h_n_le : n ≤ 2 := by
    have h1 : Fintype.card (Fin n) = n := by convert Fintype.card_fin n
    omega
  omega

/-- The Dehn twist has constant value 1/n on forward edges (for n ≥ 3). -/
lemma dehn_twist_constant {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3) (i : Fin n) :
    (dehn_twist cycle).val i (cycle.next i) = 1 / n := by
  unfold dehn_twist
  have h_ne : i ≠ cycle.next (cycle.next i) := by
    intro h_eq
    have h_period := prev_ne_next_of_n_ge_3 cycle h_n_ge_3 i
    have : cycle.prev i = cycle.next i := by
      apply cycle.next_injective
      calc cycle.next (cycle.prev i) = i := cycle.next_prev i
        _ = cycle.next (cycle.next i) := h_eq
    exact h_period this
  simp only [true_and, if_pos h_ne]

/-- The Dehn twist is harmonic for n ≥ 3. -/
theorem dehn_twist_is_harmonic {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3) : IsHarmonic (dehn_twist cycle) := by
  -- IsHarmonic requires: ∀ i, ∑ j, val i j = 0 (sum over second index)
  intro i
  have h_ne := prev_ne_next_of_n_ge_3 cycle h_n_ge_3 i
  -- For row i, non-zero entries are at j = next i (value 1/n) and j = prev i (value -1/n)
  have h_zero : ∀ k, k ≠ cycle.next i → k ≠ cycle.prev i → (dehn_twist cycle).val i k = 0 := by
    intro k hk_next hk_prev
    unfold dehn_twist
    have h2 : i ≠ cycle.next k := by
      intro h_eq
      have : k = cycle.prev i := by rw [h_eq, cycle.prev_next]
      exact hk_prev this
    simp only [hk_next, h2, false_and, ite_false]
  have h_next_val : (dehn_twist cycle).val i (cycle.next i) = 1 / n :=
    dehn_twist_constant cycle h_n_ge_3 i
  have h_prev_val : (dehn_twist cycle).val i (cycle.prev i) = -(1 / n) := by
    have h_ne_next : cycle.prev i ≠ cycle.next i := h_ne
    have h_i_eq : i = cycle.next (cycle.prev i) := (cycle.next_prev i).symm
    show (dehn_twist cycle).val i (cycle.prev i) = -(1 / n)
    simp only [dehn_twist, h_ne_next, false_and, ite_false, h_i_eq.symm, ne_eq, not_true_eq_false, not_false_eq_true, true_and, ite_true]
  -- Sum over all k
  have h_sum_split : ∑ k : Fin n, (dehn_twist cycle).val i k =
      ∑ k ∈ Finset.univ.filter (fun k => k = cycle.next i ∨ k = cycle.prev i),
        (dehn_twist cycle).val i k +
      ∑ k ∈ Finset.univ.filter (fun k => k ≠ cycle.next i ∧ k ≠ cycle.prev i),
        (dehn_twist cycle).val i k := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => k = cycle.next i ∨ k = cycle.prev i)]
    congr 1
    apply Finset.sum_congr
    · ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or]
    · intros; rfl
  rw [h_sum_split]
  have h_first : ∑ k ∈ Finset.univ.filter (fun k => k = cycle.next i ∨ k = cycle.prev i),
      (dehn_twist cycle).val i k = 1 / n + (-(1 / n)) := by
    rw [Finset.filter_or]
    have h_eq1 : Finset.filter (fun k => k = cycle.next i) Finset.univ = {cycle.next i} := by
      ext k; simp
    have h_eq2 : Finset.filter (fun k => k = cycle.prev i) Finset.univ = {cycle.prev i} := by
      ext k; simp
    rw [h_eq1, h_eq2, Finset.sum_union, Finset.sum_singleton, Finset.sum_singleton, h_next_val, h_prev_val]
    simp only [Finset.disjoint_singleton]
    exact Ne.symm h_ne
  have h_second : ∑ k ∈ Finset.univ.filter (fun k => k ≠ cycle.next i ∧ k ≠ cycle.prev i),
      (dehn_twist cycle).val i k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact h_zero k hk.1 hk.2
  rw [h_first, h_second]
  ring

/-- The Dehn twist has winding number 1 (for n ≥ 3). -/
theorem dehn_twist_winding_one {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3) :
    ∑ i : Fin n, (dehn_twist cycle).val i (cycle.next i) = 1 := by
  have h : ∀ i, (dehn_twist cycle).val i (cycle.next i) = 1 / n := dehn_twist_constant cycle h_n_ge_3
  have h_card : Fintype.card (Fin n) = n := by convert Fintype.card_fin n
  have h_n_ne : (n : ℝ) ≠ 0 := by simp [NeZero.ne n]
  calc ∑ i, (dehn_twist cycle).val i (cycle.next i)
      = ∑ i : Fin n, (1 / n : ℝ) := Finset.sum_congr rfl (fun i _ => h i)
    _ = Fintype.card (Fin n) * (1 / n) := by rw [Finset.sum_const, Finset.card_univ]; ring
    _ = n * (1 / n) := by rw [h_card]
    _ = 1 := by field_simp [h_n_ne]

/-! ## Main Theorems -/

/-- Dehn twist has the minimum possible non-zero energy: 1/n. -/
theorem dehn_twist_energy {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3) :
    norm_sq (dehn_twist cycle) = 1 / n := by
  unfold norm_sq inner_product_C1
  have h_card : Fintype.card (Fin n) = n := by convert Fintype.card_fin n
  have h_each : ∀ i : Fin n, ∑ j : Fin n, (dehn_twist cycle).val i j * (dehn_twist cycle).val i j =
                2 * (1 / n)^2 := by
    intro i
    have h_ne := prev_ne_next_of_n_ge_3 cycle h_n_ge_3 i
    have h_zero : ∀ j, j ≠ cycle.next i → j ≠ cycle.prev i →
                  (dehn_twist cycle).val i j * (dehn_twist cycle).val i j = 0 := by
      intro j hj_next hj_prev
      unfold dehn_twist
      have h2 : i ≠ cycle.next j := by
        intro h_eq
        have h_prev_eq : j = cycle.prev i := by rw [h_eq, cycle.prev_next]
        exact hj_prev h_prev_eq
      simp only [hj_next, h2, false_and, ite_false, mul_zero]
    have h_next : (dehn_twist cycle).val i (cycle.next i) = 1 / n := dehn_twist_constant cycle h_n_ge_3 i
    have h_prev : (dehn_twist cycle).val i (cycle.prev i) = -(1 / n) := by
      have h_ne_next : cycle.prev i ≠ cycle.next i := h_ne
      have h_i_eq : i = cycle.next (cycle.prev i) := (cycle.next_prev i).symm
      show (dehn_twist cycle).val i (cycle.prev i) = -(1 / n)
      simp only [dehn_twist, h_ne_next, false_and, ite_false, h_i_eq.symm, ne_eq, not_true_eq_false, not_false_eq_true, true_and, ite_true]
    have h_sum_split : ∑ j : Fin n, (dehn_twist cycle).val i j * (dehn_twist cycle).val i j =
        ∑ j ∈ Finset.univ.filter (fun j => j = cycle.next i ∨ j = cycle.prev i),
          (dehn_twist cycle).val i j * (dehn_twist cycle).val i j +
        ∑ j ∈ Finset.univ.filter (fun j => j ≠ cycle.next i ∧ j ≠ cycle.prev i),
          (dehn_twist cycle).val i j * (dehn_twist cycle).val i j := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j = cycle.next i ∨ j = cycle.prev i)]
      congr 1
      apply Finset.sum_congr
      · ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or]
      · intros; rfl
    rw [h_sum_split]
    have h_first : ∑ j ∈ Finset.univ.filter (fun j => j = cycle.next i ∨ j = cycle.prev i),
        (dehn_twist cycle).val i j * (dehn_twist cycle).val i j =
        (1/n) * (1/n) + (-(1/n)) * (-(1/n)) := by
      rw [Finset.filter_or]
      have h_eq1 : Finset.filter (fun j => j = cycle.next i) Finset.univ = {cycle.next i} := by
        ext j; simp
      have h_eq2 : Finset.filter (fun j => j = cycle.prev i) Finset.univ = {cycle.prev i} := by
        ext j; simp
      rw [h_eq1, h_eq2, Finset.sum_union, Finset.sum_singleton, Finset.sum_singleton, h_next, h_prev]
      simp only [Finset.disjoint_singleton]
      exact Ne.symm h_ne
    have h_second : ∑ j ∈ Finset.univ.filter (fun j => j ≠ cycle.next i ∧ j ≠ cycle.prev i),
        (dehn_twist cycle).val i j * (dehn_twist cycle).val i j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact h_zero j hj.1 hj.2
    rw [h_first, h_second, add_zero]
    ring
  have h_n_ne : (n : ℝ) ≠ 0 := by simp [NeZero.ne n]
  calc (1 / 2) * ∑ i : Fin n, ∑ j : Fin n, (dehn_twist cycle).val i j * (dehn_twist cycle).val i j
      = (1 / 2) * ∑ i : Fin n, (2 : ℝ) * (1 / (n : ℝ))^2 := by
          congr 1; exact Finset.sum_congr rfl (fun i _ => h_each i)
    _ = 1 / (n : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, h_card, nsmul_eq_mul]; field_simp

/-- The Dehn twist is canonical: any harmonic form on a cycle with winding 1
    has the same value on forward edges. -/
theorem dehn_twist_is_canonical {n : ℕ} [Fintype (Fin n)] [NeZero n] [Inhabited (Fin n)]
    (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3) (γ : C1 n)
    (h_harm : IsHarmonic γ)
    (h_support : SupportedOnCycle cycle γ)
    (h_winding : ∑ i, γ.val i (cycle.next i) = 1) :
    ∀ i : Fin n, γ.val i (cycle.next i) = (dehn_twist cycle).val i (cycle.next i) := by
  intro i
  obtain ⟨k, h_const⟩ := harmonic_constant_on_simple_cycle cycle γ h_harm h_support
  have h_card : Fintype.card (Fin n) = n := by convert Fintype.card_fin n
  have h_k : k = 1 / n := by
    have : ∑ i : Fin n, k = 1 := by
      calc ∑ i : Fin n, k
          = ∑ i : Fin n, γ.val i (cycle.next i) := Finset.sum_congr rfl (fun i _ => (h_const i).symm)
        _ = 1 := h_winding
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, h_card] at this
    have h_ne : (n : ℝ) ≠ 0 := by simp [NeZero.ne n]
    field_simp [h_ne] at this ⊢
    linarith
  rw [h_const, h_k, dehn_twist_constant cycle h_n_ge_3]

end Diaspora.Hodge
