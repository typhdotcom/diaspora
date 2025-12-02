/-
# Walk-Chain Holonomy Correspondence

Proves that walk_sum around a cycle equals the algebraic winding number.
This bridges the walk-based holonomy (Universal.lean) with the algebraic
winding (Harmonic.lean).
-/

import Diaspora.Logic.Universal
import Diaspora.Hodge.Twist

namespace Diaspora.Logic.WalkHolonomy

open Diaspora.Core Diaspora.Hodge Diaspora.Logic.Universal

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-! ## 1. Iteration Commutativity -/

set_option linter.unusedSectionVars false in
/-- Key lemma: iteration commutes with next. -/
lemma iterate_next_comm (cycle : SimpleCycle n) (k : ℕ) (v : Fin n) :
    cycle.next^[k] (cycle.next v) = cycle.next (cycle.next^[k] v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih]

/-- Helper: permutation power equals function iteration. -/
lemma perm_pow_eq_iterate (cycle : SimpleCycle n) (h_bij : Function.Bijective cycle.next)
    (k : ℕ) (x : Fin n) :
    ((Equiv.ofBijective cycle.next h_bij) ^ k) x = cycle.next^[k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ, Equiv.Perm.mul_apply, Function.iterate_succ_apply',
               Equiv.ofBijective_apply]
    rw [ih, iterate_next_comm]

/-- next^[n] = id for a SimpleCycle (uses that next is a bijection on Fin n). -/
lemma next_iterate_n [NeZero n] (cycle : SimpleCycle n) (v : Fin n) :
    cycle.next^[n] v = v := by
  have h_bij := next_bijective cycle
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective cycle.next h_bij
  -- Show σ is a cycle on all of Fin n using IsCycleOn
  have h_cycle_on : σ.IsCycleOn (Finset.univ : Finset (Fin n)) := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · -- MapsTo
      intro x _; exact Finset.mem_univ (σ x)
    · -- InjOn
      intro x _ y _ h; exact σ.injective h
    · -- SurjOn
      intro x _; exact ⟨σ.symm x, Finset.mem_univ _, σ.apply_symm_apply x⟩
    · -- SameCycle: any two elements are in the same cycle (by connectedness)
      intro x _ y _
      obtain ⟨k, hk⟩ := cycle.connected x y
      use k
      rw [zpow_natCast, perm_pow_eq_iterate cycle h_bij k x, hk]
  -- Apply IsCycleOn.pow_card_apply: σ^(#univ) v = v
  have h_pow := h_cycle_on.pow_card_apply (Finset.mem_univ v)
  simp only [Finset.card_univ, σ] at h_pow
  -- Fintype.card (Fin n) = n regardless of instance
  have h_card : Fintype.card (Fin n) = n := by convert Fintype.card_fin n
  rw [h_card] at h_pow
  rw [← perm_pow_eq_iterate cycle h_bij n v]
  exact h_pow

/-! ## 2. Building Cycle Walks -/

/-- Build a walk of k steps following next, starting from v. -/
def cycle_walk_aux (cycle : SimpleCycle n) (G : DynamicGraph n)
    (h_embedded : cycleEmbeddedIn cycle G) :
    ∀ (k : ℕ) (v : Fin n), (DynamicGraph.toSimpleGraph G).Walk v (cycle.next^[k] v)
  | 0, v => SimpleGraph.Walk.nil
  | k + 1, v =>
    have h_adj : (DynamicGraph.toSimpleGraph G).Adj v (cycle.next v) := h_embedded v
    have h_eq : cycle.next^[k + 1] v = cycle.next^[k] (cycle.next v) := by
      simp only [Function.iterate_succ_apply']
      rw [iterate_next_comm]
    let rest := cycle_walk_aux cycle G h_embedded k (cycle.next v)
    (SimpleGraph.Walk.cons h_adj rest).copy rfl h_eq

/-- The canonical closed walk around a SimpleCycle. -/
noncomputable def canonical_cycle_walk [NeZero n] (cycle : SimpleCycle n)
    (G : DynamicGraph n) (h_embedded : cycleEmbeddedIn cycle G) (v : Fin n) :
    (DynamicGraph.toSimpleGraph G).Walk v v :=
  (cycle_walk_aux cycle G h_embedded n v).copy rfl (next_iterate_n cycle v)

/-! ## 3. Walk Sum on Auxiliary Walk -/

/-- walk_sum of the auxiliary walk equals the partial sum. -/
lemma walk_sum_cycle_aux (cycle : SimpleCycle n) (G : DynamicGraph n)
    (h_embedded : cycleEmbeddedIn cycle G) (σ : ActiveForm G) (v : Fin n) (k : ℕ) :
    walk_sum G σ (cycle_walk_aux cycle G h_embedded k v) =
    ∑ i ∈ Finset.range k, σ.val.val (cycle.next^[i] v) (cycle.next^[i + 1] v) := by
  induction k generalizing v with
  | zero => simp [cycle_walk_aux, walk_sum]
  | succ k ih =>
    -- Unfold the definition
    have h_unfold : cycle_walk_aux cycle G h_embedded (k + 1) v =
        (SimpleGraph.Walk.cons (h_embedded v) (cycle_walk_aux cycle G h_embedded k (cycle.next v))).copy rfl
          (by simp only [Function.iterate_succ_apply']; rw [iterate_next_comm]) := rfl
    rw [h_unfold, walk_sum_copy]
    -- walk_sum of cons
    conv_lhs => rw [walk_sum.eq_def]
    simp only
    rw [ih (cycle.next v)]
    -- Reindex the sum
    have h_reindex : ∑ i ∈ Finset.range k, σ.val.val (cycle.next^[i] (cycle.next v)) (cycle.next^[i + 1] (cycle.next v)) =
                     ∑ i ∈ Finset.range k, σ.val.val (cycle.next^[i + 1] v) (cycle.next^[i + 2] v) := by
      apply Finset.sum_congr rfl
      intro i _
      rfl
    rw [h_reindex, Finset.sum_range_succ']
    simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply']
    ring

/-! ## 4. Main Theorem -/

/-- **Main Theorem:** For the canonical cycle walk, walk_sum equals sum over edges.
    This connects the walk-based holonomy with the algebraic winding. -/
theorem walk_holonomy_eq_sum [NeZero n] (cycle : SimpleCycle n)
    (G : DynamicGraph n) (h_embedded : cycleEmbeddedIn cycle G)
    (σ : ActiveForm G) (v : Fin n) :
    walk_sum G σ (canonical_cycle_walk cycle G h_embedded v) =
    ∑ i ∈ Finset.range n, σ.val.val (cycle.next^[i] v) (cycle.next^[i + 1] v) := by
  unfold canonical_cycle_walk
  rw [walk_sum_copy, walk_sum_cycle_aux]

/-! ## 5. Connection to Winding -/

/-- When the orbit of v covers all of Fin n bijectively, we recover SimpleCycleWinding. -/
theorem walk_sum_eq_winding [NeZero n] (cycle : SimpleCycle n)
    (G : DynamicGraph n) (h_embedded : cycleEmbeddedIn cycle G)
    (σ : ActiveForm G) (v : Fin n)
    (h_bij : Function.Bijective (fun i : Fin n => cycle.next^[i.val] v)) :
    walk_sum G σ (canonical_cycle_walk cycle G h_embedded v) =
    ∑ i : Fin n, σ.val.val i (cycle.next i) := by
  rw [walk_holonomy_eq_sum]
  let e := Equiv.ofBijective _ h_bij
  -- Convert sum over range to sum over Fin
  conv_lhs => rw [← Fin.sum_univ_eq_sum_range (fun i => σ.val.val (cycle.next^[i] v) (cycle.next^[i + 1] v))]
  -- LHS is now ∑ i : Fin n, σ.val.val (e i) (cycle.next (e i))
  have h_lhs : (fun i : Fin n => σ.val.val (cycle.next^[i.val] v) (cycle.next^[i.val + 1] v)) =
               (fun i : Fin n => σ.val.val (e i) (cycle.next (e i))) := by
    ext i
    simp only [e, Equiv.ofBijective_apply, Function.iterate_succ_apply']
  simp only [h_lhs]
  -- Reindex: ∑ i, f(e i) = ∑ j, f j (via bijective reindexing)
  symm
  convert Fintype.sum_bijective (M := ℝ) e.symm e.symm.bijective
    (fun i => σ.val.val i (cycle.next i))
    (fun j => σ.val.val (e j) (cycle.next (e j)))
    (fun i => by simp [e])

/-! ## 6. Consequence: Dehn Twist Detection -/

/-- The Dehn twist has walk_sum = 1 around its cycle. -/
theorem dehn_twist_walk_sum_one [NeZero n] (h_n_ge_3 : n ≥ 3)
    (cycle : SimpleCycle n) (G : DynamicGraph n)
    (h_embedded : cycleEmbeddedIn cycle G) (v : Fin n)
    (h_bij : Function.Bijective (fun i : Fin n => cycle.next^[i.val] v)) :
    walk_sum G (dehn_twist_active cycle G h_embedded) (canonical_cycle_walk cycle G h_embedded v) = 1 := by
  rw [walk_sum_eq_winding cycle G h_embedded _ v h_bij]
  have h_val : (dehn_twist_active cycle G h_embedded).val = dehn_twist cycle := rfl
  simp only [h_val]
  exact dehn_twist_winding_one cycle h_n_ge_3

end Diaspora.Logic.WalkHolonomy
