/-
# Diffusion: The Local Mechanism of Relaxation

Defines a discrete heat equation on the graph and proves that its fixed points
are exactly the global energy minima (Hodge potentials).

This replaces the "Global Solver" oracle with a purely local dynamical process.
-/

import Diaspora.DiscreteCalculus
import Diaspora.TopologyChange
import Diaspora.PhaseField
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace DiscreteHodge

open BigOperators

/-! ## 1. The Local Imbalance (The Force) -/

/--
The "Force" acting on a vertex i.
It is the sum of residual strains on all active edges incident to i.
Vertex i increases its potential if its neighbors are higher (relative to σ).
-/
noncomputable def local_imbalance {n : ℕ} (G : DynamicGraph n) (ϕ : C0 n) (σ : C1 n) (i : Fin n) : ℝ :=
  ∑ j, if (i, j) ∈ G.active_edges then (residual ϕ σ).val i j else 0

/-- The residual restricted to active edges (as an ActiveForm) -/
noncomputable def active_residual {n : ℕ} (G : DynamicGraph n) (ϕ : C0 n) (σ : C1 n) : ActiveForm G :=
  ⟨{ val := fun i j => if (i, j) ∈ G.active_edges then (residual ϕ σ).val i j else 0,
     skew := by
       intro i j
       by_cases h : (i, j) ∈ G.active_edges
       · have h' : (j, i) ∈ G.active_edges := G.symmetric i j |>.mp h
         simp only [h, h', ↓reduceIte]
         rw [(residual ϕ σ).skew]
       · have h' : (j, i) ∉ G.active_edges := by
            intro hcontra
            have := G.symmetric j i |>.mp hcontra
            exact h this
         simp only [h, h', ↓reduceIte, neg_zero] },
   by intro i j h_not_active
      simp only [h_not_active, ↓reduceIte]⟩

/-- Graph divergence of the residual. -/
lemma imbalance_is_divergence {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (ϕ : C0 n) (σ : C1 n) :
    local_imbalance G ϕ σ = δ_G G (active_residual G ϕ σ) := by
  ext i
  unfold local_imbalance δ_G active_residual
  simp
  convert rfl

/-! ## 2. The Diffusion Step (The Mechanism) -/

/--
One step of the discrete heat equation (forward Euler).
ϕ_{t+1}(i) = ϕ_t(i) + α * ∑_{j~i} (residual_{ij})
-/
noncomputable def diffusion_step {n : ℕ} (G : DynamicGraph n) (ϕ : C0 n) (σ : C1 n) (α : ℝ) : C0 n :=
  fun i => ϕ i + α * local_imbalance G ϕ σ i

/-- Iteratively apply the diffusion step `k` times from zero potential. -/
noncomputable def diffusion_process {n : ℕ} (G : DynamicGraph n) (σ : C1 n) (α : ℝ) (k : ℕ) : C0 n :=
  match k with
  | 0 => (fun _ => 0)
  | s + 1 => diffusion_step G (diffusion_process G σ α s) σ α

/-! ## Phase Synchronization (Kuramoto Dynamics) -/

/-- Phase imbalance at vertex i: sum of geodesic phase differences to neighbors.
    Replaces linear heat diffusion with phase-aware synchronization. -/
noncomputable def phase_imbalance {n k : ℕ} [NeZero k] [Fintype (Fin n)]
    (G : DynamicGraph n) (ϕ : PC0 n k) (σ : PC1 n k) (i : Fin n) : ℤ :=
  ∑ j, if (i, j) ∈ G.active_edges then
    let delta := (pd0 ϕ).val i j - σ.val i j
    let dist := geodesic_dist delta 0
    if dist ≤ k / 2 then -(delta.val : ℤ) else (k - delta.val : ℤ)
  else 0

/-- One step of Kuramoto-style phase synchronization.
    Adjusts local phase to minimize geodesic distance to neighbors + constraint. -/
noncomputable def phase_synchronization_step {n k : ℕ} [NeZero k] [Fintype (Fin n)]
    (G : DynamicGraph n) (ϕ : PC0 n k) (σ : PC1 n k) (α : ℝ) : PC0 n k :=
  fun i =>
    let imb := phase_imbalance G ϕ σ i
    ϕ i + (Int.floor (α * imb) : ℤ)

/-! ## 3. Convergence and Optimality -/

/-- The total strain energy on the currently active graph topology. -/
noncomputable def dynamic_energy {n : ℕ} (G : DynamicGraph n) (ϕ : C0 n) (σ : C1 n) : ℝ :=
  (1/2) * ∑ i, ∑ j, if (i, j) ∈ G.active_edges then edge_strain ϕ σ i j else 0

/-- Global optimum on a specific graph topology. -/
def is_hodge_optimal {n : ℕ} (G : DynamicGraph n) (ϕ_opt : C0 n) (σ : C1 n) : Prop :=
  ∀ ϕ', dynamic_energy G ϕ_opt σ ≤ dynamic_energy G ϕ' σ

/-- The linear term in energy expansion relates exactly to local imbalance. -/
lemma linear_term_is_imbalance {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (ϕ_star : C0 n) (σ : C1 n) (δ : C0 n) :
    (∑ i, ∑ j, if (i,j) ∈ G.active_edges then
      (ϕ_star j - ϕ_star i - σ.val i j) * (δ j - δ i) else 0)
    = -2 * ∑ i, δ i * local_imbalance G ϕ_star σ i := by
  have h_split : (∑ i, ∑ j, if (i,j) ∈ G.active_edges then
                    (ϕ_star j - ϕ_star i - σ.val i j) * (δ j - δ i) else 0)
                 = (∑ i, ∑ j, if (i,j) ∈ G.active_edges then
                      (ϕ_star j - ϕ_star i - σ.val i j) * δ j else 0)
                  -(∑ i, ∑ j, if (i,j) ∈ G.active_edges then
                      (ϕ_star j - ϕ_star i - σ.val i j) * δ i else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _
    by_cases h : (i, j) ∈ G.active_edges
    · simp [h, mul_sub]
    · simp [h]
  rw [h_split]
  have h_second : (∑ i, ∑ j, if (i,j) ∈ G.active_edges then
                    (ϕ_star j - ϕ_star i - σ.val i j) * δ i else 0)
                  = ∑ i, δ i * local_imbalance G ϕ_star σ i := by
    apply Finset.sum_congr rfl
    intro i _
    unfold local_imbalance residual d0
    simp only
    trans (δ i * ∑ j, if (i, j) ∈ G.active_edges then (ϕ_star j - ϕ_star i - σ.val i j) else 0)
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : (i, j) ∈ G.active_edges
      · simp [h]; ring
      · simp [h]
    · apply congr_arg
      exact Finset.sum_bij (fun j _ => j) (by simp) (by simp) (by simp) (by simp)
  have h_first : (∑ i, ∑ j, if (i,j) ∈ G.active_edges then
                    (ϕ_star j - ϕ_star i - σ.val i j) * δ j else 0)
                 = -(∑ i, δ i * local_imbalance G ϕ_star σ i) := by
    calc (∑ i, ∑ j, if (i,j) ∈ G.active_edges then (ϕ_star j - ϕ_star i - σ.val i j) * δ j else 0)
        = ∑ j, ∑ i, if (i,j) ∈ G.active_edges then (ϕ_star j - ϕ_star i - σ.val i j) * δ j else 0 := Finset.sum_comm
      _ = ∑ j, ∑ i, if (j,i) ∈ G.active_edges then (ϕ_star j - ϕ_star i - σ.val i j) * δ j else 0 := by
          apply Finset.sum_congr rfl; intro j _
          apply Finset.sum_congr rfl; intro i _
          by_cases h : (i, j) ∈ G.active_edges
          · simp [h, G.symmetric i j |>.mp h]
          · have h' : (j, i) ∉ G.active_edges := mt (G.symmetric i j |>.mpr) h
            simp [h, h']
      _ = -∑ i, δ i * local_imbalance G ϕ_star σ i := by
          have h_expand : ∑ i, δ i * local_imbalance G ϕ_star σ i =
                          ∑ i, ∑ k, if (i,k) ∈ G.active_edges then δ i * (ϕ_star k - ϕ_star i - σ.val i k) else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            simp only [local_imbalance, residual, d0, Finset.mul_sum, mul_ite, mul_zero]
            exact Finset.sum_bij (fun j _ => j) (by simp) (by simp) (by simp) (by simp)
          rw [h_expand, ← Finset.sum_neg_distrib]
          congr 1; ext i
          rw [← Finset.sum_neg_distrib]
          congr 1; ext k
          by_cases h : (i,k) ∈ G.active_edges
          · simp [h]
            have : σ.val k i = -σ.val i k := σ.skew k i
            rw [this]; ring
          · simp [h]
  rw [h_first, h_second]
  ring

/-- Local balance implies global optimality, and vice versa. -/
lemma optimality_condition {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (ϕ_star : C0 n) (σ : C1 n) :
    is_hodge_optimal G ϕ_star σ ↔ ∀ i, local_imbalance G ϕ_star σ i = 0 := by
  constructor
  -- Direction 1: Global Opt -> Local Balance (by contradiction)
  · intro h_opt i
    by_contra h_ne
    let imb := local_imbalance G ϕ_star σ i
    let ε : ℝ := imb / (4 * n * n)
    let ϕ' : C0 n := fun j => if j = i then ϕ_star j + ε else ϕ_star j
    have h_better : dynamic_energy G ϕ' σ < dynamic_energy G ϕ_star σ := by
      unfold dynamic_energy edge_strain d0
      simp only
      let δ : C0 n := fun j => if j = i then ε else 0
      have h_phi' : ϕ' = fun j => ϕ_star j + δ j := by
        funext j
        simp only [δ]
        by_cases h : j = i
        · simp [ϕ', h]
        · simp [ϕ', h]
      rw [h_phi']
      suffices h_suff : (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges
                  then ((ϕ_star x_1 + δ x_1) - (ϕ_star x + δ x) - σ.val x x_1) ^ 2 else 0) <
               (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges
                  then (ϕ_star x_1 - ϕ_star x - σ.val x x_1) ^ 2 else 0) by
        have : (0:ℝ) < 1/2 := by norm_num
        convert mul_lt_mul_of_pos_left h_suff this
      have h_expand : ∀ a b : ℝ, (a + b)^2 - a^2 = 2*a*b + b^2 := by intro a b; ring
      suffices (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges
                  then ((ϕ_star x_1 + δ x_1 - (ϕ_star x + δ x) - σ.val x x_1) ^ 2 -
                        (ϕ_star x_1 - ϕ_star x - σ.val x x_1) ^ 2) else 0) < 0 by
        have h_diff : (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges
                        then (ϕ_star x_1 + δ x_1 - (ϕ_star x + δ x) - σ.val x x_1) ^ 2 else 0) -
                      (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges
                        then (ϕ_star x_1 - ϕ_star x - σ.val x x_1) ^ 2 else 0) < 0 := by
          have : (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges
                      then ((ϕ_star x_1 + δ x_1 - (ϕ_star x + δ x) - σ.val x x_1) ^ 2 -
                            (ϕ_star x_1 - ϕ_star x - σ.val x x_1) ^ 2) else 0) < 0 := this
          calc (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges
                  then (ϕ_star x_1 + δ x_1 - (ϕ_star x + δ x) - σ.val x x_1) ^ 2 else 0) -
               (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges
                  then (ϕ_star x_1 - ϕ_star x - σ.val x x_1) ^ 2 else 0)
            _ = (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges
                    then ((ϕ_star x_1 + δ x_1 - (ϕ_star x + δ x) - σ.val x x_1) ^ 2 -
                          (ϕ_star x_1 - ϕ_star x - σ.val x x_1) ^ 2) else 0) := by
                  rw [← Finset.sum_sub_distrib]; congr 1; ext x
                  rw [← Finset.sum_sub_distrib]; congr 1; ext x_1
                  split_ifs <;> ring
            _ < 0 := this
        linarith
      have h_rewrite : (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges
                  then ((ϕ_star x_1 + δ x_1 - (ϕ_star x + δ x) - σ.val x x_1) ^ 2 -
                        (ϕ_star x_1 - ϕ_star x - σ.val x x_1) ^ 2) else 0) =
               (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges
                  then (2 * (ϕ_star x_1 - ϕ_star x - σ.val x x_1) * (δ x_1 - δ x) +
                        (δ x_1 - δ x) ^ 2) else 0) := by
        congr 1; ext x; congr 1; ext x_1
        by_cases h : (x, x_1) ∈ G.active_edges
        · simp [h]; ring
        · simp [h]
      rw [h_rewrite]
      have h_split : (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges
                        then 2 * (ϕ_star x_1 - ϕ_star x - σ.val x x_1) * (δ x_1 - δ x) +
                             (δ x_1 - δ x) ^ 2 else 0) =
                     (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges
                        then 2 * (ϕ_star x_1 - ϕ_star x - σ.val x x_1) * (δ x_1 - δ x) else 0) +
                     (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges
                        then (δ x_1 - δ x) ^ 2 else 0) := by
        rw [← Finset.sum_add_distrib]
        congr 1; ext x
        rw [← Finset.sum_add_distrib]
        congr 1; ext x_1
        split_ifs <;> ring
      rw [h_split]
      -- Use linear_term_is_imbalance to rewrite the linear term
      have h_linear := linear_term_is_imbalance G ϕ_star σ δ
      calc ((∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges
                then 2 * (ϕ_star x_1 - ϕ_star x - σ.val x x_1) * (δ x_1 - δ x) else 0) +
            ∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges then (δ x_1 - δ x) ^ 2 else 0)
        _ = 2 * (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges
                then (ϕ_star x_1 - ϕ_star x - σ.val x x_1) * (δ x_1 - δ x) else 0) +
            (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges then (δ x_1 - δ x) ^ 2 else 0) := by
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x _
              rw [Finset.mul_sum]
              simp only [mul_ite, mul_zero]
              apply Finset.sum_congr rfl
              intro
              split_ifs <;> (simp; try ring)
        _ = 2 * (-2 * ∑ x, δ x * local_imbalance G ϕ_star σ x) +
            (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges then (δ x_1 - δ x) ^ 2 else 0) := by
              congr 1; rw [h_linear]
        _ = -4 * (∑ x, δ x * local_imbalance G ϕ_star σ x) +
            (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges then (δ x_1 - δ x) ^ 2 else 0) := by ring
        _ = -4 * (δ i * imb) +
            (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges then (δ x_1 - δ x) ^ 2 else 0) := by
              congr 2
              trans (∑ x, (if x = i then δ x * local_imbalance G ϕ_star σ x else 0))
              · congr 1; ext x; simp only [δ]; split_ifs <;> ring
              · simp [Finset.sum_ite_eq', imb]
        _ = -4 * ε * imb + (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges then (δ x_1 - δ x) ^ 2 else 0) := by
              simp [δ]; ring
        _ < 0 := by
              have h_quad_bound : (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges
                                  then (δ x_1 - δ x) ^ 2 else 0) ≤ n * n * ε^2 := by
                have h_delta_diff : ∀ x x_1, (δ x_1 - δ x)^2 ≤ ε^2 := by
                  intro x x_1
                  simp [δ]
                  split_ifs <;> simp [sq_nonneg, le_refl]
                calc (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges then (δ x_1 - δ x) ^ 2 else 0)
                  _ ≤ ∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges then ε^2 else 0 := by
                      apply Finset.sum_le_sum; intro x _
                      apply Finset.sum_le_sum; intro x_1 _
                      split_ifs <;> [exact h_delta_diff x x_1; exact le_refl 0]
                  _ ≤ ∑ x, ∑ x_1, ε^2 := by
                      apply Finset.sum_le_sum; intro x _
                      apply Finset.sum_le_sum; intro x_1 _
                      split_ifs <;> [exact le_refl _; exact sq_nonneg _]
                  _ = n * n * ε^2 := by
                      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
                      have : Fintype.card (Fin n) = n := by convert Fintype.card_fin n
                      rw [this]
                      ring
              have h_linear_val : -4 * ε * imb = -imb^2 / (n * n) := by
                field_simp; ring
              calc -4 * ε * imb + (∑ x, ∑ x_1, if (x, x_1) ∈ G.active_edges
                                    then (δ x_1 - δ x) ^ 2 else 0)
                _ ≤ -4 * ε * imb + n * n * ε^2 := by linarith
                _ = -imb^2 / (n * n) + n * n * (imb / (4 * n * n))^2 := by rw [h_linear_val]
                _ = -imb^2 / (n * n) + imb^2 / (16 * n * n) := by field_simp; ring
                _ = -15 * imb^2 / (16 * n * n) := by field_simp; ring
                _ < 0 := by
                    apply div_neg_of_neg_of_pos
                    · apply mul_neg_of_neg_of_pos
                      · norm_num
                      · exact sq_pos_of_ne_zero h_ne
                    · have h_n_pos : 0 < n := Fin.pos_iff_nonempty.mpr ⟨i⟩
                      apply mul_pos
                      · apply mul_pos
                        · norm_num
                        · exact Nat.cast_pos.mpr h_n_pos
                      · exact Nat.cast_pos.mpr h_n_pos
    have h_opt_le := h_opt ϕ'
    linarith

  -- Direction 2: Local Balance -> Global Opt (Convexity)
  · intro h_balanced ϕ'
    show dynamic_energy G ϕ_star σ ≤ dynamic_energy G ϕ' σ
    unfold dynamic_energy edge_strain d0
    simp only
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/2)
    let δ : C0 n := fun i => ϕ' i - ϕ_star i
    suffices h_diff : 0 ≤ ∑ i, ∑ j, if (i,j) ∈ G.active_edges then
                      ((ϕ' j - ϕ' i - σ.val i j)^2 - (ϕ_star j - ϕ_star i - σ.val i j)^2) else 0 by
      convert calc (∑ i, ∑ j, if (i,j) ∈ G.active_edges then (ϕ_star j - ϕ_star i - σ.val i j)^2 else 0)
        _ ≤ (∑ i, ∑ j, if (i,j) ∈ G.active_edges then (ϕ_star j - ϕ_star i - σ.val i j)^2 else 0) +
            (∑ i, ∑ j, if (i,j) ∈ G.active_edges then
              ((ϕ' j - ϕ' i - σ.val i j)^2 - (ϕ_star j - ϕ_star i - σ.val i j)^2) else 0) := by linarith
        _ = ∑ i, ∑ j, if (i,j) ∈ G.active_edges then (ϕ' j - ϕ' i - σ.val i j)^2 else 0 := by
            rw [← Finset.sum_add_distrib]; congr 1; ext i
            rw [← Finset.sum_add_distrib]; congr 1; ext j
            split_ifs <;> ring
    have h_expand : ∀ i j, (ϕ' j - ϕ' i - σ.val i j)^2 - (ϕ_star j - ϕ_star i - σ.val i j)^2
                          = 2 * (ϕ_star j - ϕ_star i - σ.val i j) * (δ j - δ i) + (δ j - δ i)^2 := by
      intro i j; ring
    calc ∑ i, ∑ j, if (i,j) ∈ G.active_edges then
           ((ϕ' j - ϕ' i - σ.val i j)^2 - (ϕ_star j - ϕ_star i - σ.val i j)^2) else 0
      _ = ∑ i, ∑ j, if (i,j) ∈ G.active_edges then
            (2 * (ϕ_star j - ϕ_star i - σ.val i j) * (δ j - δ i) + (δ j - δ i)^2) else 0 := by
          congr 1; ext i; congr 1; ext j; split_ifs <;> [rw [h_expand]; rfl]
      _ = (∑ i, ∑ j, if (i,j) ∈ G.active_edges then
            2 * (ϕ_star j - ϕ_star i - σ.val i j) * (δ j - δ i) else 0) +
          (∑ i, ∑ j, if (i,j) ∈ G.active_edges then (δ j - δ i)^2 else 0) := by
          rw [← Finset.sum_add_distrib]
          congr 1; ext i
          rw [← Finset.sum_add_distrib]
          congr 1; ext j
          split_ifs <;> ring
      _ = 2 * (∑ i, ∑ j, if (i,j) ∈ G.active_edges then
            (ϕ_star j - ϕ_star i - σ.val i j) * (δ j - δ i) else 0) +
          (∑ i, ∑ j, if (i,j) ∈ G.active_edges then (δ j - δ i)^2 else 0) := by
          congr 1
          rw [Finset.mul_sum]
          congr 1; ext i
          rw [Finset.mul_sum]
          congr 1; ext j
          split_ifs <;> ring
      _ = 2 * (-2 * ∑ i, δ i * local_imbalance G ϕ_star σ i) +
          (∑ i, ∑ j, if (i,j) ∈ G.active_edges then (δ j - δ i)^2 else 0) := by
          rw [linear_term_is_imbalance]
      _ = -4 * (∑ i, δ i * local_imbalance G ϕ_star σ i) +
          (∑ i, ∑ j, if (i,j) ∈ G.active_edges then (δ j - δ i)^2 else 0) := by ring
      _ = -4 * (∑ i, δ i * 0) +
          (∑ i, ∑ j, if (i,j) ∈ G.active_edges then (δ j - δ i)^2 else 0) := by
          congr 2
          apply Finset.sum_congr rfl
          intro i _
          rw [h_balanced]
      _ = ∑ i, ∑ j, if (i,j) ∈ G.active_edges then (δ j - δ i)^2 else 0 := by simp
      _ ≥ 0 := by
          apply Finset.sum_nonneg; intro i _
          apply Finset.sum_nonneg; intro j _
          split_ifs <;> [exact sq_nonneg _; exact le_refl 0]

/-- Stationary diffusion implies global optimality. -/
theorem stationary_diffusion_is_optimal {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (σ : C1 n) (α : ℝ) (h_alpha : α ≠ 0) (ϕ_star : C0 n)
    (h_stationary : diffusion_step G ϕ_star σ α = ϕ_star) :
    is_hodge_optimal G ϕ_star σ := by
  have h_zero_update : ∀ i, α * local_imbalance G ϕ_star σ i = 0 := by
    intro i
    have h_eq_at_i := congr_fun h_stationary i
    unfold diffusion_step at h_eq_at_i
    linarith
  have h_balanced : ∀ i, local_imbalance G ϕ_star σ i = 0 := by
    intro i
    specialize h_zero_update i
    exact (mul_eq_zero.mp h_zero_update).resolve_left h_alpha
  rw [optimality_condition]
  exact h_balanced

/-! ## 4. The Pragmatic Solver -/

/-- Solver using `K` iterations of the local diffusion process. -/
noncomputable def pragmatic_diffusion_solver {n : ℕ} (K : ℕ) (α : ℝ) :
    DynamicGraph n → C1 n → C0 n :=
  fun G σ => diffusion_process G σ α K

end DiscreteHodge
