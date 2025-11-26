/-
# The Local Witness Theorem

Parallel transport along a cycle recovers the global harmonic form magnitude.
-/

import Diaspora.SelfMeasurement
import Diaspora.HarmonicAnalysis
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace DiscreteHodge

open Complex

/-! ## 1. The Blind Walker -/

/-- Local transport step from `curr` to `next`. -/
noncomputable def blind_step {n : ℕ} (σ : C1 n) (curr next : Fin n) (ψ : ℂ) : ℂ :=
  transport_step σ curr next ψ

/-- Recursively applies blind_step along a sequence of vertices. -/
noncomputable def walk_path {n : ℕ} (σ : C1 n) (path : List (Fin n)) (ψ_init : ℂ) : ℂ :=
  match path with
  | [] => ψ_init
  | _ :: [] => ψ_init -- Need at least two nodes to have an edge
  | curr :: next :: rest =>
      let ψ_next := blind_step σ curr next ψ_init
      walk_path σ (next :: rest) ψ_next

/-! ## 2. The Local Experience -/

/-- Measures the distortion after walking a full cycle. -/
noncomputable def measure_loop_distortion {n : ℕ} (σ : C1 n) (cycle_nodes : List (Fin n)) : ℂ :=
  walk_path σ cycle_nodes 1

/-! ## 3. The Equivalence Theorem -/

/-- For cycles with n ≥ 3 nodes, prev(i) ≠ next(i). -/
lemma SimpleCycle.prev_ne_next {n : ℕ} [Fintype (Fin n)] (cycle : SimpleCycle n)
    (h_n_ge_3 : n ≥ 3) (i : Fin n) : cycle.prev i ≠ cycle.next i := by
  haveI : Inhabited (Fin n) := ⟨0, by omega⟩
  intro h_eq
  have h_period_2 : cycle.next (cycle.next i) = i := by
    calc cycle.next (cycle.next i)
        = cycle.next (cycle.prev i) := by rw [← h_eq]
      _ = i := cycle.next_prev i
  have h_exists_third : ∃ j : Fin n, j ≠ i ∧ j ≠ cycle.next i := by
    by_contra h_not
    push_neg at h_not
    have h_all : ∀ j : Fin n, j = i ∨ j = cycle.next i := fun j =>
      by_cases (fun h : j = i => Or.inl h) (fun h => Or.inr (h_not j h))
    have h_card_le : Fintype.card (Fin n) ≤ 2 := by
      classical
      have h_subset : (Finset.univ : Finset (Fin n)) ⊆ {i, cycle.next i} := by
        intro j _
        simp [h_all j]
      calc Fintype.card (Fin n)
          = Finset.univ.card := Finset.card_univ.symm
        _ ≤ ({i, cycle.next i} : Finset (Fin n)).card := Finset.card_le_card h_subset
        _ ≤ 2 := Finset.card_le_two
    have h_card_eq : Fintype.card (Fin n) = n := by convert Fintype.card_fin n
    omega
  obtain ⟨j, hj_ne_i, hj_ne_next⟩ := h_exists_third
  have := cycle.connected i j
  obtain ⟨k_iter, hk⟩ := this
  have h_period_gen : ∀ m, cycle.next^[m] i = i ∨ cycle.next^[m] i = cycle.next i := by
    intro m
    induction m with
    | zero => left; rfl
    | succ m' ih =>
      cases ih with
      | inl h => right; simp [Function.iterate_succ_apply', h]
      | inr h => left; simp [Function.iterate_succ_apply', h, h_period_2]
  have h_periodic := h_period_gen k_iter
  cases h_periodic with
  | inl h => rw [←hk] at hj_ne_i; exact hj_ne_i h
  | inr h => rw [←hk] at hj_ne_next; exact hj_ne_next h

/--
Generates a list of nodes by following the cycle from a starting point.
For a cycle with n nodes, this produces a list of length n+1 where the last node
equals the first (completing the cycle).
-/
def cycle_nodes_list {n : ℕ} [Inhabited (Fin n)] (cycle : SimpleCycle n) : List (Fin n) :=
  let start := default
  let rec build_list (current : Fin n) (remaining : ℕ) : List (Fin n) :=
    match remaining with
    | 0 => [current]
    | k + 1 => current :: build_list (cycle.next current) k
  build_list start n

/-- Helper: walk_path on a two-node path -/
lemma walk_path_pair {n : ℕ} (σ : C1 n) (i j : Fin n) (ψ : ℂ) :
    walk_path σ [i, j] ψ = transport_step σ i j ψ := by
  unfold walk_path
  rfl

/-- Cons case of walk_path -/
lemma walk_path_cons {n : ℕ} (σ : C1 n) (curr next : Fin n) (rest : List (Fin n)) (ψ : ℂ) :
    walk_path σ (curr :: next :: rest) ψ =
    walk_path σ (next :: rest) (transport_step σ curr next ψ) := by
  cases rest with
  | nil => unfold walk_path blind_step; rfl
  | cons head tail => unfold walk_path blind_step; rfl

/-- walk_path scales linearly with initial value -/
lemma walk_path_linear {n : ℕ} (σ : C1 n) (path : List (Fin n)) (c ψ : ℂ) :
    walk_path σ path (c * ψ) = c * walk_path σ path ψ := by
  induction path generalizing ψ with
  | nil => rfl
  | cons head tail ih =>
    cases tail with
    | nil => rfl
    | cons next rest =>
      rw [walk_path_cons, walk_path_cons]
      unfold transport_step
      rw [show cexp (I * ↑(σ.val head next)) * (c * ψ) = c * (cexp (I * ↑(σ.val head next)) * ψ) by ring]
      apply ih

/-- Walking accumulates exponentials -/
lemma walk_path_mul {n : ℕ} (σ : C1 n) (i j : Fin n) (rest : List (Fin n)) :
    walk_path σ (i :: j :: rest) 1 =
    cexp (I * (σ.val i j : ℂ)) * walk_path σ (j :: rest) 1 := by
  rw [walk_path_cons]
  unfold transport_step
  rw [walk_path_linear]

/-- Sum of values along cycle edges -/
noncomputable def cycle_edge_sum {n : ℕ} [Fintype (Fin n)]
    (cycle : SimpleCycle n) (σ : C1 n) : ℝ :=
  ∑ i : Fin n, σ.val i (cycle.next i)

/-- The holonomy of SimpleCycle.toChain1 equals the sum along edges -/
lemma holonomy_cycle_eq_sum {n : ℕ} [Fintype (Fin n)]
    (cycle : SimpleCycle n) (σ : C1 n) (h_n_ge_3 : n ≥ 3) :
    holonomy σ (SimpleCycle.toChain1 cycle) = cycle_edge_sum cycle σ := by
  unfold holonomy eval SimpleCycle.toChain1 cycle_edge_sum
  have h_double : (∑ i, ∑ j, σ.val i j * ↑(cycle.toChain1.coeff i j)) = 2 * ∑ i, σ.val i (cycle.next i) := by
    have h_each : ∀ i, ∑ j, σ.val i j * ↑(cycle.toChain1.coeff i j) =
                           σ.val i (cycle.next i) + σ.val (cycle.prev i) i := by
      intro i
      have h_ne : cycle.prev i ≠ cycle.next i := SimpleCycle.prev_ne_next cycle h_n_ge_3 i
      trans (σ.val i (cycle.next i) * ↑(cycle.toChain1.coeff i (cycle.next i)) +
             σ.val i (cycle.prev i) * ↑(cycle.toChain1.coeff i (cycle.prev i)))
      · symm
        convert Finset.sum_subset (s₂ := Finset.univ) (Finset.subset_univ {cycle.next i, cycle.prev i}) _ using 1
        · rw [Finset.sum_pair h_ne.symm]
        · intro j _ hj
          simp at hj; push_neg at hj
          -- Show coefficient is 0 when j ∉ {next i, prev i}
          have h1 : ¬(j = cycle.next i ∧ i ≠ cycle.next j) := fun h => hj.1 h.1
          have h2 : ¬(i = cycle.next j ∧ j ≠ cycle.next i) := by
            intro h
            have : j = cycle.prev i := by
              have : cycle.prev (cycle.next j) = cycle.prev i := by rw [h.1]
              rw [cycle.prev_next] at this; exact this
            exact hj.2 this
          show σ.val i j * ↑(cycle.toChain1.coeff i j) = 0
          rw [SimpleCycle.toChain1]
          simp only []
          rw [if_neg h1, if_neg h2]
          simp
      have h_next : cycle.toChain1.coeff i (cycle.next i) = 1 := by
        rw [SimpleCycle.toChain1]
        simp only []
        have h_ne2 : i ≠ cycle.next (cycle.next i) := by
          intro h_eq
          have := SimpleCycle.prev_ne_next cycle h_n_ge_3 (cycle.next i)
          apply this
          calc cycle.prev (cycle.next i) = i := cycle.prev_next i
             _ = cycle.next (cycle.next i) := h_eq
        simp only [true_and]
        rw [if_pos h_ne2]
      have h_prev : cycle.toChain1.coeff i (cycle.prev i) = -1 := by
        rw [SimpleCycle.toChain1]
        simp only []
        have h_eq : i = cycle.next (cycle.prev i) := (cycle.next_prev i).symm
        have h1 : ¬(cycle.prev i = cycle.next i ∧ i ≠ cycle.next (cycle.prev i)) := fun h => h_ne h.1
        have h2 : i = cycle.next (cycle.prev i) ∧ cycle.prev i ≠ cycle.next i := ⟨h_eq, h_ne⟩
        rw [if_neg h1, if_pos h2]
      calc σ.val i (cycle.next i) * ↑(cycle.toChain1.coeff i (cycle.next i)) +
           σ.val i (cycle.prev i) * ↑(cycle.toChain1.coeff i (cycle.prev i))
          = σ.val i (cycle.next i) * 1 + σ.val i (cycle.prev i) * (-1) := by simp [h_next, h_prev]
        _ = σ.val i (cycle.next i) + (-σ.val i (cycle.prev i)) := by ring
        _ = σ.val i (cycle.next i) + σ.val (cycle.prev i) i := by rw [σ.skew i (cycle.prev i)]; simp
    have prev_inj : ∀ i j, cycle.prev i = cycle.prev j → i = j := fun i j h => by
      have : cycle.next (cycle.prev i) = cycle.next (cycle.prev j) := by rw [h]
      simpa [cycle.next_prev] using this
    have h_reindex : ∑ i, σ.val (cycle.prev i) i = ∑ i, σ.val i (cycle.next i) := by
      convert Finset.sum_bij (fun i _ => cycle.prev i) _ _ _ _ using 1
      · intro i _; simp
      · intro i _ j _ h; exact prev_inj i j h
      · intro j _; use cycle.next j; simp; exact cycle.prev_next j
      · intro i _; simp [cycle.next_prev]
    calc ∑ i, ∑ j, σ.val i j * ↑(cycle.toChain1.coeff i j)
        = ∑ i, (σ.val i (cycle.next i) + σ.val (cycle.prev i) i) := Finset.sum_congr rfl (fun i _ => h_each i)
      _ = ∑ i, σ.val i (cycle.next i) + ∑ i, σ.val (cycle.prev i) i := Finset.sum_add_distrib
      _ = ∑ i, σ.val i (cycle.next i) + ∑ i, σ.val i (cycle.next i) := by rw [h_reindex]
      _ = 2 * ∑ i, σ.val i (cycle.next i) := by ring
  show 1 / 2 * (∑ i, ∑ j, σ.val i j * ↑(cycle.toChain1.coeff i j)) = ∑ i, σ.val i (cycle.next i)
  rw [h_double]; ring

/-- Walking along a path accumulates the product of transport steps -/
lemma walk_path_eq_prod_transport {n : ℕ} (σ : C1 n) (path : List (Fin n)) (ψ : ℂ) :
    walk_path σ path ψ = (List.zipWith (fun i j => cexp (I * (σ.val i j : ℂ))) path path.tail).prod * ψ := by
  induction path generalizing ψ with
  | nil => simp [walk_path]
  | cons head tail ih =>
    cases tail with
    | nil => simp [walk_path]
    | cons next rest =>
      rw [walk_path_cons]
      unfold transport_step
      simp only [List.tail_cons, List.zipWith_cons_cons, List.prod_cons]
      rw [ih]
      simp [mul_comm, mul_assoc]

/-- next as an equivalence using the inverse property -/
def SimpleCycle.toEquiv {n : ℕ} (cycle : SimpleCycle n) : Equiv.Perm (Fin n) where
  toFun := cycle.next
  invFun := cycle.prev
  left_inv := cycle.prev_next
  right_inv := cycle.next_prev

/-- The orbit of default under next has period n -/
lemma SimpleCycle.iterate_next_period {n : ℕ} [Fintype (Fin n)] [Inhabited (Fin n)]
    (cycle : SimpleCycle n) (_h_n_ge_3 : n ≥ 3) :
    (cycle.next^[n]) default = default := by
  -- Strategy: Show minimalPeriod cycle.next default = n, then use iterate_minimalPeriod
  have h_period : Function.minimalPeriod cycle.next default = n := by
    -- Default is a periodic point (since next is injective on finite Fin n)
    have h_periodic : default ∈ Function.periodicPts cycle.next :=
      Function.Injective.mem_periodicPts cycle.next_injective default
    -- Every element of Fin n is in the periodic orbit
    have h_all_in_orbit : ∀ x : Fin n, x ∈ Function.periodicOrbit cycle.next default := by
      intro x
      rw [Function.mem_periodicOrbit_iff h_periodic]
      exact cycle.connected default x
    -- The periodic orbit has length minimalPeriod and contains n distinct elements
    have h_len : (Function.periodicOrbit cycle.next default).length = Function.minimalPeriod cycle.next default :=
      Function.periodicOrbit_length
    -- Since periodicOrbit contains all n elements and has no duplicates, its cardinality is n
    have h_nodup : (Function.periodicOrbit cycle.next default).Nodup :=
      Function.nodup_periodicOrbit
    have h_card : (Function.periodicOrbit cycle.next default).toFinset.card = n := by
      have : (Function.periodicOrbit cycle.next default).toFinset = Finset.univ := by
        ext x
        simp only [Finset.mem_univ, iff_true]
        rw [Cycle.toFinset, Multiset.mem_toFinset]
        exact h_all_in_orbit x
      rw [this, Finset.card_univ]
      convert Fintype.card_fin n
    -- Since periodicOrbit has no duplicates, length equals toFinset.card
    have h_len_eq_card : (Function.periodicOrbit cycle.next default).length =
                          (Function.periodicOrbit cycle.next default).toFinset.card := by
      -- periodicOrbit is defined as a list coerced to Cycle
      -- Use length_coe and coe_toFinset to relate to the underlying list
      let l := (List.range (Function.minimalPeriod cycle.next default)).map (fun n => cycle.next^[n] default)
      show (l : Cycle (Fin n)).length = (l : Cycle (Fin n)).toFinset.card
      rw [Cycle.length_coe, Cycle.coe_toFinset, List.toFinset_card_of_nodup h_nodup]
    calc Function.minimalPeriod cycle.next default
        = (Function.periodicOrbit cycle.next default).length := h_len.symm
      _ = (Function.periodicOrbit cycle.next default).toFinset.card := h_len_eq_card
      _ = n := h_card
  convert Function.iterate_minimalPeriod (f := cycle.next) using 1
  exact congrArg (fun k => cycle.next^[k] default) h_period.symm

/-- The iteration map is injective. -/
lemma SimpleCycle.iterate_next_injective {n : ℕ} [Fintype (Fin n)] [Inhabited (Fin n)]
    (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3) :
    Function.Injective (fun i : Fin n => (cycle.next^[i.val]) default) := by
  intro i j h_eq
  simp only at h_eq
  by_contra h_ne
  have h_ival_ne : i.val ≠ j.val := by
    intro h_contra
    have : i = j := Fin.ext h_contra
    exact h_ne this
  wlog h_lt : i.val < j.val
  · exact this cycle h_n_ge_3 h_eq.symm (Ne.symm h_ne) (Ne.symm h_ival_ne)
      (Nat.lt_of_le_of_ne (Nat.le_of_not_lt h_lt) (Ne.symm h_ival_ne))
  have : (cycle.next^[j.val - i.val]) default = default := by
    have h : (cycle.next^[j.val - i.val]) ((cycle.next^[i.val]) default) = (cycle.next^[i.val]) default := by
      calc (cycle.next^[j.val - i.val]) ((cycle.next^[i.val]) default)
          = (cycle.next^[j.val - i.val + i.val]) default := by rw [← Function.iterate_add_apply]
        _ = (cycle.next^[j.val]) default := by rw [Nat.sub_add_cancel (Nat.le_of_lt h_lt)]
        _ = (cycle.next^[i.val]) default := h_eq.symm
    have h_comm : (cycle.next^[i.val]) ((cycle.next^[j.val - i.val]) default) =
                  (cycle.next^[i.val]) default := by
      calc (cycle.next^[i.val]) ((cycle.next^[j.val - i.val]) default)
          = (cycle.next^[i.val + (j.val - i.val)]) default := by
              rw [← Function.iterate_add_apply]
        _ = (cycle.next^[(j.val - i.val) + i.val]) default := by
              rw [add_comm]
        _ = (cycle.next^[j.val - i.val]) ((cycle.next^[i.val]) default) := by
              rw [Function.iterate_add_apply]
        _ = (cycle.next^[i.val]) default := h
    exact (cycle.next_injective.iterate i.val) h_comm
  have h_diff_pos : 0 < j.val - i.val := Nat.sub_pos_of_lt h_lt
  have h_diff_lt : j.val - i.val < n := Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.is_lt
  have h_period_le : Function.minimalPeriod cycle.next default ≤ j.val - i.val :=
    Function.IsPeriodicPt.minimalPeriod_le h_diff_pos this
  have h_period_eq : Function.minimalPeriod cycle.next default = n := by
    have h_periodic : default ∈ Function.periodicPts cycle.next :=
      Function.Injective.mem_periodicPts cycle.next_injective default
    have h_all_in_orbit : ∀ x : Fin n, x ∈ Function.periodicOrbit cycle.next default := by
      intro x
      rw [Function.mem_periodicOrbit_iff h_periodic]
      exact cycle.connected default x
    have h_len : (Function.periodicOrbit cycle.next default).length = Function.minimalPeriod cycle.next default :=
      Function.periodicOrbit_length
    have h_nodup : (Function.periodicOrbit cycle.next default).Nodup :=
      Function.nodup_periodicOrbit
    have h_card : (Function.periodicOrbit cycle.next default).toFinset.card = n := by
      have : (Function.periodicOrbit cycle.next default).toFinset = Finset.univ := by
        ext x
        simp only [Finset.mem_univ, iff_true]
        rw [Cycle.toFinset, Multiset.mem_toFinset]
        exact h_all_in_orbit x
      rw [this, Finset.card_univ]
      convert Fintype.card_fin n
    have h_len_eq_card : (Function.periodicOrbit cycle.next default).length =
                          (Function.periodicOrbit cycle.next default).toFinset.card := by
      let l := (List.range (Function.minimalPeriod cycle.next default)).map (fun n => cycle.next^[n] default)
      show (l : Cycle (Fin n)).length = (l : Cycle (Fin n)).toFinset.card
      rw [Cycle.length_coe, Cycle.coe_toFinset, List.toFinset_card_of_nodup h_nodup]
    calc Function.minimalPeriod cycle.next default
        = (Function.periodicOrbit cycle.next default).length := h_len.symm
      _ = (Function.periodicOrbit cycle.next default).toFinset.card := h_len_eq_card
      _ = n := h_card
  omega

/-- build_list produces a list matching the iteration structure -/
lemma cycle_nodes_list.build_list_eq_ofFn {n : ℕ} [Inhabited (Fin n)]
    (cycle : SimpleCycle n) (start : Fin n) (k : ℕ) :
    cycle_nodes_list.build_list cycle start k = List.ofFn (fun i : Fin (k + 1) => (cycle.next^[i.val]) start) := by
  induction k generalizing start with
  | zero =>
    unfold cycle_nodes_list.build_list
    rw [List.ofFn_succ, List.ofFn_zero]
    simp [Function.iterate_zero]
  | succ k ih =>
    unfold cycle_nodes_list.build_list
    rw [List.ofFn_succ]
    change start :: build_list cycle (cycle.next start) k = start :: List.ofFn fun i => cycle.next^[↑i.succ] start
    congr 1
    rw [ih]
    congr 1

/-- Walking the cycle equals exp of the holonomy -/
lemma walk_cycle_eq_exp_holonomy {n : ℕ} [Fintype (Fin n)] [Inhabited (Fin n)]
    (cycle : SimpleCycle n) (σ : C1 n) (h_n_ge_3 : n ≥ 3) :
    measure_loop_distortion σ (cycle_nodes_list cycle) =
    cexp (I * (holonomy σ (SimpleCycle.toChain1 cycle) : ℂ)) := by
  unfold measure_loop_distortion
  rw [holonomy_cycle_eq_sum cycle σ h_n_ge_3]
  unfold cycle_edge_sum
  rw [walk_path_eq_prod_transport]
  simp only [mul_one]
  -- Convert Finset sum to List, then use exp_list_sum
  -- Key: cycle visits each vertex exactly once, so list sum = Finset sum
  -- Helper: build_list creates a list by iterating next
  have build_spec : ∀ (start : Fin n) (k : ℕ),
      cycle_nodes_list.build_list cycle start (k + 1) =
      start :: cycle_nodes_list.build_list cycle (cycle.next start) k := by
    intros; rfl
  have h_list : (∑ i, σ.val i (cycle.next i) : ℝ) =
      (List.zipWith (σ.val · ·) (cycle_nodes_list cycle) (cycle_nodes_list cycle).tail).sum := by
    have h_list_struct : (List.zipWith (σ.val · ·) (cycle_nodes_list cycle) (cycle_nodes_list cycle).tail) =
        List.ofFn (fun i : Fin n => σ.val ((cycle.next^[i.val]) default) ((cycle.next^[i.val + 1]) default)) := by
      have h_build : cycle_nodes_list cycle = List.ofFn (fun i : Fin (n+1) => (cycle.next^[i.val]) default) :=
        cycle_nodes_list.build_list_eq_ofFn cycle default n
      rw [h_build]
      ext i : 1
      simp only [List.getElem?_ofFn, List.getElem?_zipWith, List.getElem?_tail]
      by_cases hi : i < n
      · simp only [hi]
        have h1 : i < n + 1 := Nat.lt_succ_of_lt hi
        have h2 : i + 1 < n + 1 := Nat.add_lt_add_right hi 1
        simp only [h1, h2, dite_true]
      · simp only [hi]
        have : ¬(i < n + 1) ∨ i = n := by omega
        cases this with
        | inl h => simp only [h, dite_false]
        | inr h =>
          simp only [h]
          have h1 : n < n + 1 := Nat.lt_succ_self n
          have h2 : ¬(n + 1 < n + 1) := Nat.lt_irrefl (n + 1)
          simp only [h1, h2, dite_true, dite_false]
    rw [h_list_struct, List.sum_ofFn]
    have h_iter_inj : Function.Injective (fun i : Fin n => (cycle.next^[i.val]) default) :=
      SimpleCycle.iterate_next_injective cycle h_n_ge_3
    have h_iter_bij : Function.Bijective (fun i : Fin n => (cycle.next^[i.val]) default) :=
      Finite.injective_iff_bijective.mp h_iter_inj
    rw [← Fintype.sum_bijective _ h_iter_bij]
    congr 1
    ext i
    · simp
    intro x
    rw [Function.iterate_succ_apply']
  rw [h_list, ← List.map_zipWith (f := cexp) (g := fun i j => I * ↑(σ.val i j))]
  rw [← Complex.exp_list_sum]
  congr 1
  rw [← List.map_zipWith (f := fun x => I * ↑x) (g := σ.val)]
  rw [List.sum_map_mul_left]
  congr 1
  exact List.sum_hom _ (algebraMap ℝ ℂ)

/-- Local holonomy measurement predicts global energy. -/
theorem local_holonomy_predicts_global_energy {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (cycle : SimpleCycle n)
    (σ : C1 n)
    (γ : C1 n)
    (h_decomp : ∃ ϕ, ∀ i j, σ.val i j = (d0 ϕ).val i j + γ.val i j)
    (h_harm : IsHarmonic γ)
    (h_support : SupportedOnCycle cycle γ)
    (h_n_ge_3 : n ≥ 3)
    (Z : ℂ) (h_measure : Z = measure_loop_distortion σ (cycle_nodes_list cycle))
    (h_branch : -Real.pi < holonomy γ cycle.toChain1 ∧ holonomy γ cycle.toChain1 ≤ Real.pi) :
    norm_sq γ = (Complex.log Z / I).re ^ 2 / (Fintype.card (Fin n)) := by
  have h_Z : Z = cexp (I * (holonomy γ (SimpleCycle.toChain1 cycle) : ℂ)) := by
    rw [h_measure, walk_cycle_eq_exp_holonomy cycle σ h_n_ge_3]
    obtain ⟨ϕ, h_decomp_eq⟩ := h_decomp
    have h_cycle : Chain1.IsCycle (SimpleCycle.toChain1 cycle) := by
      intro i
      simp only [SimpleCycle.toChain1]
      let s : Finset (Fin n) := {cycle.next i, cycle.prev i}
      have h_support : ∀ j ∉ s, (if j = cycle.next i ∧ i ≠ cycle.next j then (1 : ℤ)
                                   else if i = cycle.next j ∧ j ≠ cycle.next i then (-1 : ℤ)
                                   else 0) = 0 := by
        intro j hj
        simp [s, Finset.mem_insert, Finset.mem_singleton] at hj
        push_neg at hj
        split_ifs <;> try rfl
        · rename_i h; exact absurd h.1 hj.1
        · rename_i h; have : j = cycle.prev i := by
            have : cycle.prev (cycle.next j) = cycle.prev i := by rw [h.1]
            rw [cycle.prev_next] at this; exact this
          exact absurd this hj.2
      trans (∑ j ∈ s, (if j = cycle.next i ∧ i ≠ cycle.next j then (1 : ℤ)
                        else if i = cycle.next j ∧ j ≠ cycle.next i then (-1 : ℤ)
                        else 0))
      · symm; apply Finset.sum_subset (Finset.subset_univ s)
        intro j _ hj; exact h_support j hj
      have h_ne : cycle.prev i ≠ cycle.next i := SimpleCycle.prev_ne_next cycle h_n_ge_3 i
      rw [Finset.sum_pair h_ne.symm]
      have h_next : (if cycle.next i = cycle.next i ∧ i ≠ cycle.next (cycle.next i) then (1 : ℤ)
                     else if i = cycle.next (cycle.next i) ∧ cycle.next i ≠ cycle.next i then (-1 : ℤ)
                     else 0) = 1 := by
        have h_ne2 : i ≠ cycle.next (cycle.next i) := by
          intro h_eq
          have := SimpleCycle.prev_ne_next cycle h_n_ge_3 (cycle.next i)
          apply this
          calc cycle.prev (cycle.next i)
              = i := cycle.prev_next i
            _ = cycle.next (cycle.next i) := h_eq
        simp [h_ne2]
      -- Evaluate coeff(i, prev i) = -1
      have h_prev : (if cycle.prev i = cycle.next i ∧ i ≠ cycle.next (cycle.prev i) then (1 : ℤ)
                     else if i = cycle.next (cycle.prev i) ∧ cycle.prev i ≠ cycle.next i then (-1 : ℤ)
                     else 0) = -1 := by
        have h_eq : i = cycle.next (cycle.prev i) := (cycle.next_prev i).symm
        have h_cond1 : ¬(cycle.prev i = cycle.next i ∧ i ≠ cycle.next (cycle.prev i)) := fun h => h_ne h.1
        have h_cond2 : i = cycle.next (cycle.prev i) ∧ cycle.prev i ≠ cycle.next i := ⟨h_eq, h_ne⟩
        rw [if_neg h_cond1, if_pos h_cond2]
      rw [h_prev, h_next]; ring
    have h_sigma_eq : σ = {
      val := fun i j => (d0 ϕ).val i j + γ.val i j,
      skew := by intro i j; rw [γ.skew]; unfold d0; linarith [h_decomp_eq i j, h_decomp_eq j i, σ.skew i j]
    } := by
      ext i j
      exact h_decomp_eq i j
    rw [h_sigma_eq, holonomy_add_cochain, holonomy_exact_zero_on_cycles ϕ _ h_cycle]
    simp
  haveI : Inhabited (Fin n) := by
    constructor
    exact ⟨0, by omega⟩
  obtain ⟨k, h_const⟩ := harmonic_constant_on_simple_cycle cycle γ h_harm h_support
  have h_hol_eq : holonomy γ (SimpleCycle.toChain1 cycle) = (Fintype.card (Fin n)) * k :=
    holonomy_of_constant_harmonic cycle γ k h_const
  have h_norm : norm_sq γ = (Fintype.card (Fin n)) * k ^ 2 := by
    unfold norm_sq inner_product_C1
    have h_sum_eq : ∑ i : Fin n, ∑ j : Fin n, γ.val i j * γ.val i j =
                    (Fintype.card (Fin n)) * 2 * k^2 := by
      have h_each : ∀ i, ∑ j, γ.val i j * γ.val i j = 2 * k^2 := by
        intro i
        let s : Finset (Fin n) := {cycle.next i, cycle.prev i}
        trans (∑ j ∈ s, γ.val i j * γ.val i j)
        · symm
          refine Finset.sum_subset (Finset.subset_univ s) ?_
          intro j _ hj
          simp [s, Finset.mem_insert, Finset.mem_singleton] at hj
          push_neg at hj
          have h := h_support i j hj.1
          rw [h]
          ring
        have h_ne : cycle.prev i ≠ cycle.next i := SimpleCycle.prev_ne_next cycle h_n_ge_3 i
        have h_next : γ.val i (cycle.next i) = k := h_const i
        have h_prev : γ.val i (cycle.prev i) = -k := by
          calc γ.val i (cycle.prev i)
              = -γ.val (cycle.prev i) i := γ.skew i (cycle.prev i)
            _ = -γ.val (cycle.prev i) (cycle.next (cycle.prev i)) := by rw [cycle.next_prev]
            _ = -k := by rw [h_const]
        calc ∑ j ∈ s, γ.val i j * γ.val i j
            = γ.val i (cycle.next i) * γ.val i (cycle.next i) +
              γ.val i (cycle.prev i) * γ.val i (cycle.prev i) := by
                simp only [s]
                rw [Finset.sum_insert (by intro h; exact h_ne.symm (Finset.mem_singleton.mp h)),
                    Finset.sum_singleton]
          _ = k * k + (-k) * (-k) := by rw [h_next, h_prev]
          _ = 2 * k^2 := by ring
      calc ∑ i, ∑ j, γ.val i j * γ.val i j
          = ∑ i, 2 * k^2 := Finset.sum_congr rfl (fun i _ => h_each i)
        _ = (Fintype.card (Fin n)) * 2 * k^2 := by
            rw [Finset.sum_const, Finset.card_univ]; ring
    rw [h_sum_eq]
    ring

  -- From h_Z and h_norm, derive the relationship to (log Z / I).re^2 / n
  have h_norm_from_hol : norm_sq γ = (holonomy γ cycle.toChain1) ^ 2 / (Fintype.card (Fin n)) := by
    calc norm_sq γ
        = (Fintype.card (Fin n)) * k ^ 2 := h_norm
      _ = (Fintype.card (Fin n)) * (holonomy γ cycle.toChain1 / (Fintype.card (Fin n))) ^ 2 := by
          congr 1
          have h_ne : (Fintype.card (Fin n) : ℝ) ≠ 0 := by simp
          field_simp [h_ne]
          calc k ^ 2 * ↑(Fintype.card (Fin n)) ^ 2
              = (k * ↑(Fintype.card (Fin n))) ^ 2 := by ring
            _ = (↑(Fintype.card (Fin n)) * k) ^ 2 := by ring
            _ = (holonomy γ cycle.toChain1) ^ 2 := by rw [← h_hol_eq]
      _ = (holonomy γ cycle.toChain1) ^ 2 / (Fintype.card (Fin n)) := by
          have h_ne : (Fintype.card (Fin n) : ℝ) ≠ 0 := by simp
          field_simp [h_ne]
  have h_log_formula : (Complex.log Z / I).re ^ 2 = (holonomy γ cycle.toChain1) ^ 2 := by
    have h_Z_eq : Z = cexp (I * ↑(holonomy γ cycle.toChain1)) := h_Z
    have h_log : Complex.log Z = I * ↑(holonomy γ cycle.toChain1) := by
      rw [h_Z_eq]
      apply Complex.log_exp
      · simp only [mul_im, I_im, I_re, ofReal_im, ofReal_re]
        ring_nf
        exact h_branch.1
      · simp only [mul_im, I_im, I_re, ofReal_im, ofReal_re]
        ring_nf
        exact h_branch.2
    calc (Complex.log Z / I).re ^ 2
        = (I * ↑(holonomy γ cycle.toChain1) / I).re ^ 2 := by rw [h_log]
      _ = (↑(holonomy γ cycle.toChain1) : ℂ).re ^ 2 := by
          have : (I * ↑(holonomy γ cycle.toChain1) / I : ℂ) = ↑(holonomy γ cycle.toChain1) := by
            field_simp [I_ne_zero]
          simp [this]
      _ = (holonomy γ cycle.toChain1) ^ 2 := by simp
  calc norm_sq γ
      = (holonomy γ cycle.toChain1) ^ 2 / (Fintype.card (Fin n)) := h_norm_from_hol
    _ = (Complex.log Z / I).re ^ 2 / (Fintype.card (Fin n)) := by rw [← h_log_formula]

end DiscreteHodge
