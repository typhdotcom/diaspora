/-
# Resilience of Self-Reference

Harmonic content is self-maintaining under plasticity: if σ has non-zero harmonic
component on a cycle, those edges carry irreducible strain that protects them from atrophy.
-/

import Diaspora.Dynamics.Plasticity
import Diaspora.Hodge.Harmonic

open BigOperators Diaspora.Core Diaspora.Hodge Diaspora.Dynamics

namespace Diaspora.Models

/-! ## Helper Lemmas for Norm -/

lemma norm_sq_nonneg {n : ℕ} [Fintype (Fin n)] (σ : C1 n) : 0 ≤ norm_sq σ := by
  unfold norm_sq inner_product_C1
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  exact mul_self_nonneg _

lemma norm_sq_zero_iff_zero {n : ℕ} [Fintype (Fin n)] (σ : C1 n) (h : norm_sq σ = 0) :
    ∀ i j, σ.val i j = 0 := by
  unfold norm_sq inner_product_C1 at h
  have h_sum : ∑ i : Fin n, ∑ j : Fin n, (σ.val i j) * (σ.val i j) = 0 := by linarith
  intro i j
  have h_term_nonneg : ∀ i' j', 0 ≤ (σ.val i' j') * (σ.val i' j') := fun _ _ => mul_self_nonneg _
  have h_sum_nonneg : ∀ i', 0 ≤ ∑ j', (σ.val i' j') * (σ.val i' j') :=
    fun i' => Finset.sum_nonneg (fun j' _ => h_term_nonneg i' j')
  have h_outer := Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (fun i' _ => h_sum_nonneg i')
  rw [h_outer] at h_sum
  have h_inner := h_sum i (Finset.mem_univ i)
  have h_inner' := Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (fun j' _ => h_term_nonneg i j')
  rw [h_inner'] at h_inner
  have h_sq := h_inner j (Finset.mem_univ j)
  exact mul_self_eq_zero.mp h_sq

/-! ## Irreducible Strain from Harmonic Content -/

/-- At the optimal potential, strain equals the harmonic component squared. -/
lemma strain_at_optimal_eq_harmonic_sq {n : ℕ} [Fintype (Fin n)]
    (σ : C1 n) (ϕ_opt : C0 n) (γ : C1 n)
    (h_decomp : ∀ i j, σ.val i j = (d0 ϕ_opt).val i j + γ.val i j)
    (i j : Fin n) :
    raw_strain ϕ_opt σ i j = (γ.val i j)^2 := by
  unfold raw_strain d0
  have h := h_decomp i j
  simp only [d0] at h
  calc ((ϕ_opt j - ϕ_opt i) - σ.val i j)^2
      = ((ϕ_opt j - ϕ_opt i) - ((ϕ_opt j - ϕ_opt i) + γ.val i j))^2 := by rw [h]
    _ = (-γ.val i j)^2 := by ring_nf
    _ = (γ.val i j)^2 := by ring

lemma total_strain_at_optimal_eq_harmonic_norm {n : ℕ} [Fintype (Fin n)]
    (σ : C1 n) (ϕ_opt : C0 n) (γ : C1 n)
    (h_decomp : ∀ i j, σ.val i j = (d0 ϕ_opt).val i j + γ.val i j) :
    ∑ i, ∑ j, raw_strain ϕ_opt σ i j = 2 * norm_sq γ := by
  unfold norm_sq inner_product_C1
  have h_each : ∀ i j, raw_strain ϕ_opt σ i j = (γ.val i j)^2 :=
    fun i j => strain_at_optimal_eq_harmonic_sq σ ϕ_opt γ h_decomp i j
  simp only [h_each, sq]
  ring

lemma harmonic_norm_pos_implies_strain_pos {n : ℕ} [Fintype (Fin n)]
    (σ : C1 n) (ϕ_opt : C0 n) (γ : C1 n)
    (h_decomp : ∀ i j, σ.val i j = (d0 ϕ_opt).val i j + γ.val i j)
    (h_norm_pos : norm_sq γ > 0) :
    ∑ i, ∑ j, raw_strain ϕ_opt σ i j > 0 := by
  rw [total_strain_at_optimal_eq_harmonic_norm σ ϕ_opt γ h_decomp]
  linarith

lemma harmonic_nonzero_implies_strain_pos {n : ℕ} [Fintype (Fin n)]
    (σ : C1 n) (ϕ_opt : C0 n) (γ : C1 n)
    (h_decomp : ∀ i j, σ.val i j = (d0 ϕ_opt).val i j + γ.val i j)
    (i j : Fin n) (h_γ_nonzero : γ.val i j ≠ 0) :
    raw_strain ϕ_opt σ i j > 0 := by
  rw [strain_at_optimal_eq_harmonic_sq σ ϕ_opt γ h_decomp]
  exact sq_pos_of_ne_zero h_γ_nonzero

/-! ## Harmonic Content on Cycles -/

/-- Non-zero winding implies non-zero harmonic component on all cycle edges. -/
lemma cycle_winding_implies_harmonic_nonzero {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (cycle : SimpleCycle n) (γ : C1 n)
    (h_harm : IsHarmonic γ)
    (h_support : SupportedOnCycle cycle γ)
    (m : ℤ) (h_m_nonzero : m ≠ 0)
    (h_winding : holonomy γ (SimpleCycle.toChain1 cycle) = m)
    [Inhabited (Fin n)] (i : Fin n) :
    γ.val i (cycle.next i) ≠ 0 := by
  obtain ⟨k, h_const⟩ := harmonic_constant_on_simple_cycle cycle γ h_harm h_support
  have h_k := topological_quantization cycle γ k h_const m h_winding
  rw [h_const]
  intro h_k_zero
  rw [h_k_zero] at h_k
  have h_card_pos : (Fintype.card (Fin n) : ℝ) > 0 := by
    have : 0 < Fintype.card (Fin n) := Fintype.card_pos
    exact Nat.cast_pos.mpr this
  have hm_real : (m : ℝ) = 0 := by field_simp [ne_of_gt h_card_pos] at h_k; linarith
  have : m = 0 := Int.cast_eq_zero.mp hm_real
  exact h_m_nonzero this

/-! ## The Resilience Theorem -/

/-- Cycle edges with harmonic content have positive strain and resist atrophy. -/
theorem harmonic_cycle_resists_atrophy {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (cycle : SimpleCycle n)
    (σ : C1 n)
    (h_harm_decomp : ∃ (ϕ_opt : C0 n) (γ : C1 n),
      (∀ i j, σ.val i j = (d0 ϕ_opt).val i j + γ.val i j) ∧
      IsHarmonic γ ∧
      SupportedOnCycle cycle γ ∧
      ∃ m : ℤ, m ≠ 0 ∧ holonomy γ (SimpleCycle.toChain1 cycle) = m)
    [Inhabited (Fin n)] :
    ∃ (ϕ_opt : C0 n),
      (∀ i : Fin n, raw_strain ϕ_opt σ i (cycle.next i) > 0) ∧
      (∑ i, ∑ j, raw_strain ϕ_opt σ i j > 0) := by
  obtain ⟨ϕ_opt, γ, h_decomp, h_harm, h_support, m, h_m_ne, h_winding⟩ := h_harm_decomp
  use ϕ_opt
  constructor
  · intro i
    have h_nonzero := cycle_winding_implies_harmonic_nonzero cycle γ h_harm h_support m h_m_ne h_winding i
    exact harmonic_nonzero_implies_strain_pos σ ϕ_opt γ h_decomp i (cycle.next i) h_nonzero
  · have h_norm_pos : norm_sq γ > 0 := by
      by_contra h_not_pos
      push_neg at h_not_pos
      have h_norm_zero : norm_sq γ = 0 := le_antisymm h_not_pos (norm_sq_nonneg γ)
      have h_γ_zero : ∀ i j, γ.val i j = 0 := norm_sq_zero_iff_zero γ h_norm_zero
      have h_holonomy_zero : holonomy γ (SimpleCycle.toChain1 cycle) = 0 := by
        unfold holonomy eval
        simp only [h_γ_zero, zero_mul, Finset.sum_const_zero, mul_zero]
      rw [h_holonomy_zero] at h_winding
      exact h_m_ne (Int.cast_eq_zero.mp h_winding.symm)
    exact harmonic_norm_pos_implies_strain_pos σ ϕ_opt γ h_decomp h_norm_pos

/-- Cycle edges receive positive Hebbian contribution. -/
theorem cycle_edges_dont_atrophy {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (G : WeightedGraph n)
    (cycle : SimpleCycle n)
    (σ : C1 n)
    (ϕ : C0 n) (γ : C1 n)
    (h_decomp : ∀ i j, σ.val i j = (d0 ϕ).val i j + γ.val i j)
    (h_harm : IsHarmonic γ)
    (h_support : SupportedOnCycle cycle γ)
    (m : ℤ) (h_m_ne : m ≠ 0)
    (h_winding : holonomy γ (SimpleCycle.toChain1 cycle) = m)
    (η : ℝ) (h_eta : η > 0)
    [Inhabited (Fin n)]
    (i : Fin n) :
    G.weights i (cycle.next i) + η * raw_strain ϕ σ i (cycle.next i) >
    G.weights i (cycle.next i) := by
  have h_strain_pos : raw_strain ϕ σ i (cycle.next i) > 0 := by
    have h_nonzero := cycle_winding_implies_harmonic_nonzero cycle γ h_harm h_support m h_m_ne h_winding i
    exact harmonic_nonzero_implies_strain_pos σ ϕ γ h_decomp i (cycle.next i) h_nonzero
  have h_contrib : η * raw_strain ϕ σ i (cycle.next i) > 0 := mul_pos h_eta h_strain_pos
  linarith

/-! ## Ghost Strain -/

/-- Exact σ achieves zero strain at its generating potential. -/
theorem exact_implies_zero_strain {n : ℕ} [Fintype (Fin n)]
    (σ : C1 n) (ψ : C0 n) (h_exact : ∀ i j, σ.val i j = (d0 ψ).val i j) :
    ∀ i j, raw_strain ψ σ i j = 0 := by
  intro i j
  unfold raw_strain
  rw [h_exact i j]
  ring

theorem zero_strain_preserves_death {n : ℕ} [Fintype (Fin n)]
    (G : WeightedGraph n) (ϕ : C0 n) (σ : C1 n) (η : ℝ)
    (i j : Fin n) (h_dead : G.weights i j = 0) (h_no_ghost : raw_strain ϕ σ i j = 0) :
    G.weights i j + η * raw_strain ϕ σ i j = 0 := by
  simp [h_dead, h_no_ghost]

/-- Exact σ: dead edges stay dead. -/
theorem zombie_stays_dead {n : ℕ} [Fintype (Fin n)]
    (G : WeightedGraph n) (σ : C1 n) (ψ : C0 n) (η : ℝ)
    (h_exact : ∀ i j, σ.val i j = (d0 ψ).val i j)
    (i j : Fin n) (h_dead : G.weights i j = 0) :
    G.weights i j + η * raw_strain ψ σ i j = 0 := by
  have h_no_ghost := exact_implies_zero_strain σ ψ h_exact i j
  exact zero_strain_preserves_death G ψ σ η i j h_dead h_no_ghost

/-- Positive strain on a dead edge produces positive update. -/
theorem ghost_strain_resurrects {n : ℕ} [Fintype (Fin n)]
    (G : WeightedGraph n) (ϕ : C0 n) (σ : C1 n) (η : ℝ) (h_η : η > 0)
    (i j : Fin n) (h_dead : G.weights i j = 0) (h_ghost : raw_strain ϕ σ i j > 0) :
    G.weights i j + η * raw_strain ϕ σ i j > 0 := by
  rw [h_dead, zero_add]
  exact mul_pos h_η h_ghost

/-- Harmonic σ: dead cycle edges resurrect. -/
theorem harmonic_resurrects {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (G : WeightedGraph n)
    (cycle : SimpleCycle n)
    (σ : C1 n)
    (ϕ : C0 n) (γ : C1 n)
    (h_decomp : ∀ i j, σ.val i j = (d0 ϕ).val i j + γ.val i j)
    (h_harm : IsHarmonic γ)
    (h_support : SupportedOnCycle cycle γ)
    (m : ℤ) (h_m_ne : m ≠ 0)
    (h_winding : holonomy γ (SimpleCycle.toChain1 cycle) = m)
    (η : ℝ) (h_η : η > 0)
    [Inhabited (Fin n)]
    (i : Fin n) (h_dead : G.weights i (cycle.next i) = 0) :
    G.weights i (cycle.next i) + η * raw_strain ϕ σ i (cycle.next i) > 0 := by
  have h_nonzero := cycle_winding_implies_harmonic_nonzero cycle γ h_harm h_support m h_m_ne h_winding i
  have h_ghost := harmonic_nonzero_implies_strain_pos σ ϕ γ h_decomp i (cycle.next i) h_nonzero
  exact ghost_strain_resurrects G ϕ σ η h_η i (cycle.next i) h_dead h_ghost

/-! ## Manifestation Threshold -/

theorem ghost_weight_unnormalized {n : ℕ} [Fintype (Fin n)]
    (G : WeightedGraph n) (ϕ : C0 n) (σ : C1 n) (η : ℝ)
    (i j : Fin n) (h_dead : G.weights i j = 0) :
    G.weights i j + η * raw_strain ϕ σ i j = η * raw_strain ϕ σ i j := by
  rw [h_dead, zero_add]

/-- Above threshold: edge survives pruning. -/
theorem ghost_manifests {n : ℕ} [Fintype (Fin n)]
    (G : WeightedGraph n) (ϕ : C0 n) (σ : C1 n) (η ε : ℝ)
    (i j : Fin n) (h_dead : G.weights i j = 0)
    (h_threshold : η * raw_strain ϕ σ i j ≥ ε) :
    ¬(G.weights i j + η * raw_strain ϕ σ i j < ε) := by
  rw [ghost_weight_unnormalized G ϕ σ η i j h_dead]
  linarith

/-- Below threshold: edge is pruned. -/
theorem ghost_trapped {n : ℕ} [Fintype (Fin n)]
    (G : WeightedGraph n) (ϕ : C0 n) (σ : C1 n) (η ε : ℝ)
    (i j : Fin n) (h_dead : G.weights i j = 0)
    (h_subthreshold : η * raw_strain ϕ σ i j < ε) :
    G.weights i j + η * raw_strain ϕ σ i j < ε := by
  rw [ghost_weight_unnormalized G ϕ σ η i j h_dead]
  exact h_subthreshold

/-- Threshold condition in terms of harmonic component: η * γ² ≥ ε. -/
theorem harmonic_manifestation_threshold {n : ℕ} [Fintype (Fin n)]
    (σ : C1 n) (ϕ : C0 n) (γ : C1 n)
    (h_decomp : ∀ i j, σ.val i j = (d0 ϕ).val i j + γ.val i j)
    (η ε : ℝ) (i j : Fin n) :
    (η * raw_strain ϕ σ i j ≥ ε) ↔ (η * (γ.val i j)^2 ≥ ε) := by
  rw [strain_at_optimal_eq_harmonic_sq σ ϕ γ h_decomp i j]

/-- Harmonic cycle edge with sufficient amplitude survives pruning. -/
theorem harmonic_manifests {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (G : WeightedGraph n)
    (cycle : SimpleCycle n)
    (σ : C1 n)
    (ϕ : C0 n) (γ : C1 n)
    (h_decomp : ∀ i j, σ.val i j = (d0 ϕ).val i j + γ.val i j)
    (_h_harm : IsHarmonic γ)
    (_h_support : SupportedOnCycle cycle γ)
    (m : ℤ) (_h_m_ne : m ≠ 0)
    (_h_winding : holonomy γ (SimpleCycle.toChain1 cycle) = m)
    (η ε : ℝ) (_h_η : η > 0)
    [Inhabited (Fin n)]
    (i : Fin n) (h_dead : G.weights i (cycle.next i) = 0)
    (h_loud : η * (γ.val i (cycle.next i))^2 ≥ ε) :
    G.weights i (cycle.next i) + η * raw_strain ϕ σ i (cycle.next i) ≥ ε := by
  rw [ghost_weight_unnormalized G ϕ σ η i (cycle.next i) h_dead]
  rw [strain_at_optimal_eq_harmonic_sq σ ϕ γ h_decomp i (cycle.next i)]
  exact h_loud

end Diaspora.Models
