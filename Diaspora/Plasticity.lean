import Diaspora.WeightedGraph
import Diaspora.PhaseField
import Diaspora.DehnTwist
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecificLimits.Basic

namespace DiscreteHodge
open BigOperators

/--
One step of Plasticity.
1. HEBBIAN PHASE: Edges under strain grow stronger.
2. SCARCITY PHASE: Renormalize to fixed constant.
-/
noncomputable def plasticity_step {n : ℕ}
    (G : WeightedGraph n) (ϕ : C0 n) (σ : C1 n) (η : ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    let strain := raw_strain ϕ σ i j
    let w_unnormalized := G.weights i j + η * strain
    let total_unnormalized := ∑ x, ∑ y, (G.weights x y + η * raw_strain ϕ σ x y)
    let scale_factor := ((n : ℝ)^2) / total_unnormalized
    w_unnormalized * scale_factor

/--
Phase-aware plasticity step: Hebbian learning with geodesic strain.
Uses phase_strain instead of raw_strain for cyclic phase fields.
-/
noncomputable def phase_plasticity_step {n k : ℕ} [NeZero k]
    (G : WeightedGraph n) (ϕ : PC0 n k) (σ : PC1 n k) (η : ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    let strain := phase_strain ϕ σ i j
    let w_unnormalized := G.weights i j + η * strain
    let total_unnormalized := ∑ x, ∑ y, (G.weights x y + η * phase_strain ϕ σ x y)
    let scale_factor := ((n : ℝ)^2) / total_unnormalized
    w_unnormalized * scale_factor

/--
The generalized Atrophy Theorem:
Any edge with zero strain strictly decreases in weight if the total system strain is positive.
-/
theorem plasticity_atrophy_of_unstressed {n : ℕ}
    (G : WeightedGraph n) (ϕ : C0 n) (σ : C1 n) (η : ℝ)
    (h_eta : η > 0)
    (h_strain_pos : ∑ i, ∑ j, raw_strain ϕ σ i j > 0)
    (i j : Fin n) (h_peace : raw_strain ϕ σ i j = 0)
    (h_weight_pos : G.weights i j > 0) :
    let w_new := plasticity_step G ϕ σ η
    w_new i j < G.weights i j := by
  intro w_new
  let total_initial := ∑ x, ∑ y, G.weights x y
  let total_strain := ∑ x, ∑ y, raw_strain ϕ σ x y
  let total_unnormalized := ∑ x, ∑ y, (G.weights x y + η * raw_strain ϕ σ x y)

  have h_total_split : total_unnormalized = total_initial + η * total_strain := by
    show ∑ x, ∑ y, (G.weights x y + η * raw_strain ϕ σ x y) =
         ∑ x, ∑ y, G.weights x y + η * ∑ x, ∑ y, raw_strain ϕ σ x y
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

  have h_inflation : total_unnormalized > total_initial := by
    rw [h_total_split]
    have : η * total_strain > 0 := mul_pos h_eta h_strain_pos
    linarith

  have h_target : total_initial = (n : ℝ)^2 := G.total_capacity_fixed
  let scale_factor := ((n : ℝ)^2) / total_unnormalized

  have h_scale_lt_one : scale_factor < 1 := by
    have h_pos : 0 < total_unnormalized :=
      calc total_unnormalized
         > total_initial := h_inflation
         _ = (n : ℝ)^2 := G.total_capacity_fixed
         _ ≥ 0 := sq_nonneg _
    unfold scale_factor
    rw [← h_target]
    exact (div_lt_one h_pos).mpr h_inflation

  have h_peace_update : G.weights i j + η * raw_strain ϕ σ i j = G.weights i j := by
    rw [h_peace]; ring

  calc w_new i j
     = (G.weights i j + η * raw_strain ϕ σ i j) * scale_factor := rfl
   _ = G.weights i j * scale_factor := by rw [h_peace_update]
   _ < G.weights i j * 1 := by apply mul_lt_mul_of_pos_left h_scale_lt_one h_weight_pos
   _ = G.weights i j := mul_one _

/-! ## 3. Symmetry Preservation -/

/-- plasticity_step preserves symmetry. -/
lemma plasticity_step_symm {n : ℕ} (G : WeightedGraph n) (ϕ : C0 n) (σ : C1 n) (η : ℝ) (i j : Fin n) :
    plasticity_step G ϕ σ η i j = plasticity_step G ϕ σ η j i := by
  unfold plasticity_step
  simp only
  rw [G.symmetric i j, raw_strain_symm ϕ σ i j]

lemma plasticity_step_nonneg {n : ℕ} (G : WeightedGraph n) (ϕ : C0 n) (σ : C1 n) (η : ℝ)
    (h_eta : η ≥ 0)
    (h_total : ∑ x, ∑ y, (G.weights x y + η * raw_strain ϕ σ x y) > 0)
    (i j : Fin n) :
    0 ≤ plasticity_step G ϕ σ η i j := by
  unfold plasticity_step
  apply mul_nonneg
  · apply add_nonneg (G.nonneg i j)
    apply mul_nonneg h_eta (raw_strain_nonneg ϕ σ i j)
  · apply div_nonneg (sq_nonneg _) (le_of_lt h_total)

/-! ## 4. Pruning and Renormalization -/

noncomputable def prune_weights_raw {n : ℕ} (weights : Fin n → Fin n → ℝ) (ε : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => if weights i j < ε then 0 else weights i j

noncomputable def surviving_total {n : ℕ} (weights : Fin n → Fin n → ℝ) (ε : ℝ) : ℝ :=
  ∑ i, ∑ j, prune_weights_raw weights ε i j

noncomputable def prune_then_renormalize {n : ℕ} (weights : Fin n → Fin n → ℝ) (ε : ℝ)
    (target : ℝ) : Fin n → Fin n → ℝ :=
  let pruned := prune_weights_raw weights ε
  let surviving := surviving_total weights ε
  fun i j => if surviving = 0 then 0 else pruned i j * (target / surviving)

lemma prune_weights_raw_symm {n : ℕ} (weights : Fin n → Fin n → ℝ)
    (h_symm : ∀ i j, weights i j = weights j i) (ε : ℝ) (i j : Fin n) :
    prune_weights_raw weights ε i j = prune_weights_raw weights ε j i := by
  unfold prune_weights_raw
  simp only [h_symm i j]

lemma prune_then_renormalize_symm {n : ℕ} (weights : Fin n → Fin n → ℝ)
    (h_symm : ∀ i j, weights i j = weights j i) (ε target : ℝ) (i j : Fin n) :
    prune_then_renormalize weights ε target i j = prune_then_renormalize weights ε target j i := by
  unfold prune_then_renormalize
  simp only [prune_weights_raw_symm weights h_symm]

lemma surviving_total_nonneg {n : ℕ} (weights : Fin n → Fin n → ℝ)
    (h_nonneg : ∀ i j, 0 ≤ weights i j) (ε : ℝ) :
    0 ≤ surviving_total weights ε := by
  unfold surviving_total
  apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro j _
  unfold prune_weights_raw
  split_ifs <;> linarith [h_nonneg i j]

lemma prune_then_renormalize_nonneg {n : ℕ} (weights : Fin n → Fin n → ℝ)
    (h_nonneg : ∀ i j, 0 ≤ weights i j) (ε target : ℝ) (h_target : 0 ≤ target) (i j : Fin n) :
    0 ≤ prune_then_renormalize weights ε target i j := by
  unfold prune_then_renormalize
  split_ifs with h
  · exact le_refl 0
  · apply mul_nonneg
    · unfold prune_weights_raw; split_ifs <;> linarith [h_nonneg i j]
    · apply div_nonneg h_target (surviving_total_nonneg weights h_nonneg ε)

/-! ## 5. The Plasticity Cycle -/

/-- One complete cycle: Hebbian update → prune → renormalize. -/
noncomputable def plasticity_cycle {n : ℕ}
    (G : WeightedGraph n) (ϕ : C0 n) (σ : C1 n) (η ε : ℝ)
    (h_eta : η ≥ 0)
    (h_total : ∑ x, ∑ y, (G.weights x y + η * raw_strain ϕ σ x y) > 0)
    (h_survive : surviving_total (plasticity_step G ϕ σ η) ε > 0) : WeightedGraph n :=
  let weights_hebbian := plasticity_step G ϕ σ η
  let weights_final := prune_then_renormalize weights_hebbian ε ((n : ℝ)^2)
  { weights := weights_final,
    symmetric := fun i j => prune_then_renormalize_symm _ (plasticity_step_symm G ϕ σ η) ε _ i j,
    nonneg := fun i j => prune_then_renormalize_nonneg _
      (plasticity_step_nonneg G ϕ σ η h_eta h_total) _ _ (sq_nonneg _) i j,
    total_capacity_fixed := by
      show ∑ i, ∑ j, prune_then_renormalize (plasticity_step G ϕ σ η) ε (↑n ^ 2) i j = ↑n ^ 2
      unfold prune_then_renormalize
      simp only [ne_of_gt h_survive, ↓reduceIte]
      have h_factor : ∀ (c : ℝ) (f : Fin n → Fin n → ℝ),
          ∑ i, ∑ j, f i j * c = (∑ i, ∑ j, f i j) * c := fun _ _ => by simp_rw [Finset.sum_mul]
      rw [h_factor]; unfold surviving_total
      rw [mul_div_assoc', mul_div_cancel_left_of_imp]
      intro h; exact absurd h (ne_of_gt h_survive)
  }

/-! ## The Shape of Memory: Dehn Twists as Attractors -/

/--
Symmetry Preservation Lemma.
If the graph weights are uniform on a cycle, and the strain is uniform (Dehn Twist),
then the plasticity step preserves this uniformity.
-/
theorem dehn_twist_preserves_symmetry {n : ℕ} [NeZero n]
    (G : WeightedGraph n) (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3)
    (w_val : ℝ) (h_weights_uniform : ∀ i, G.weights i (cycle.next i) = w_val)
    (η : ℝ) :
    let twist := dehn_twist cycle
    let ϕ := fun (_ : Fin n) => (0 : ℝ)
    let w_next := plasticity_step G ϕ twist η
    ∃ (w_new : ℝ), ∀ i, w_next i (cycle.next i) = w_new := by
  intro twist ϕ w_next

  -- The strain of a Dehn Twist is constant on the cycle
  have h_strain_uniform : ∀ i, raw_strain ϕ twist i (cycle.next i) = (1 / (n : ℝ))^2 := by
    intro i
    unfold raw_strain d0
    have h_phi_zero : ϕ (cycle.next i) - ϕ i = 0 := by simp only [ϕ, sub_self]
    simp only [h_phi_zero, zero_sub, neg_sq]
    rw [dehn_twist_constant cycle h_n_ge_3 i]

  -- The unnormalized weight update is uniform
  let strain_val := (1 / (n : ℝ))^2

  -- The renormalization factor is global, so it scales everything equally
  use (w_val + η * strain_val) * (((n : ℝ)^2) / (∑ x : Fin n, ∑ y : Fin n, (G.weights x y + η * raw_strain ϕ twist x y)))

  intro i
  unfold w_next plasticity_step
  dsimp only

  have h_w : G.weights i (cycle.next i) = w_val := h_weights_uniform i
  have h_s : raw_strain ϕ twist i (cycle.next i) = strain_val := h_strain_uniform i

  rw [h_w, h_s]

/-- One step of Dehn Twist plasticity guarantees cycle edges become active. -/
theorem dehn_twist_guarantees_existence {n : ℕ} [NeZero n]
    (G : WeightedGraph n) (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3)
    (η : ℝ) (h_eta : η > 0)
    (h_total_pos : ∑ x : Fin n, ∑ y : Fin n, (G.weights x y + η * raw_strain (fun _ => (0 : ℝ)) (dehn_twist cycle) x y) > 0) :
    let twist := dehn_twist cycle
    let ϕ := fun (_ : Fin n) => (0 : ℝ)
    ∀ i, plasticity_step G ϕ twist η i (cycle.next i) > 0 := by
  intro twist ϕ i
  unfold plasticity_step
  dsimp only
  
  -- 1. Prove Strain is Strictly Positive
  have h_strain_pos : raw_strain ϕ twist i (cycle.next i) > 0 := by
    unfold raw_strain d0
    have h_phi_zero : ϕ (cycle.next i) - ϕ i = 0 := by simp only [ϕ, sub_self]
    simp only [h_phi_zero, zero_sub, neg_sq]
    apply sq_pos_of_ne_zero
    rw [dehn_twist_constant cycle h_n_ge_3 i]
    have h_n_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    exact one_div_ne_zero h_n_ne

  -- 2. Prove Scale Factor is Positive
  have h_scale_pos : 0 < ((n : ℝ)^2) / (∑ x, ∑ y, (G.weights x y + η * raw_strain ϕ twist x y)) := by
    apply div_pos (sq_pos_of_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne n)))
    convert h_total_pos

  -- 3. Combine: (w + η*pos) * pos > 0
  apply mul_pos
  · -- The unnormalized weight is positive
    apply add_pos_of_nonneg_of_pos (G.nonneg i (cycle.next i))
    apply mul_pos h_eta h_strain_pos
  · exact h_scale_pos

end DiscreteHodge
