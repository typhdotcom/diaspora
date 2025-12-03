import Diaspora.Logic.Classicality
import Diaspora.Logic.Theory

namespace Diaspora.Logic.Universal

open Diaspora.Core Diaspora.Hodge Diaspora.Logic

/-! # The Universal Cover -/

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-! ## 1. Constructing the Cover -/

/-- A History is a walk from root to curr. -/
structure History (G : DynamicGraph n) (root : Fin n) where
  curr : Fin n
  walk : (DynamicGraph.toSimpleGraph G).Walk root curr
  deriving DecidableEq

/-- Adjacency: one history extends the other by one step. -/
def UniversalCover (G : DynamicGraph n) (root : Fin n) : SimpleGraph (History G root) :=
  SimpleGraph.fromRel fun h1 h2 =>
    (∃ (hadj : (DynamicGraph.toSimpleGraph G).Adj h1.curr h2.curr),
       h2.walk = h1.walk.concat hadj) ∨
    (∃ (hadj : (DynamicGraph.toSimpleGraph G).Adj h2.curr h1.curr),
       h1.walk = h2.walk.concat hadj)

/-! ## 2. The Theorem of Innocence -/

/-- Walk length as a potential function on histories. -/
def History.len (h : History G root) : ℕ := h.walk.length

/-- Key lemma: adjacency in UniversalCover means walk lengths differ by exactly 1. -/
lemma cover_adj_length_diff (h1 h2 : History G root)
    (hadj : (UniversalCover G root).Adj h1 h2) :
    (h1.len + 1 = h2.len) ∨ (h2.len + 1 = h1.len) := by
  unfold UniversalCover at hadj
  simp only [SimpleGraph.fromRel_adj, ne_eq] at hadj
  obtain ⟨_, hrel⟩ := hadj
  rcases hrel with (⟨_, heq⟩ | ⟨_, heq⟩) | (⟨_, heq⟩ | ⟨_, heq⟩)
  · left; unfold History.len; rw [heq, SimpleGraph.Walk.length_concat]
  · right; unfold History.len; rw [heq, SimpleGraph.Walk.length_concat]
  · right; unfold History.len; rw [heq, SimpleGraph.Walk.length_concat]
  · left; unfold History.len; rw [heq, SimpleGraph.Walk.length_concat]

/-- If h2 extends h1 (h2.walk = h1.walk.concat e), h1's walk is a prefix of h2's. -/
lemma cover_adj_extends_walk {h1 h2 : History G root}
    (hadj : (UniversalCover G root).Adj h1 h2) (hlen : h2.len = h1.len + 1) :
    ∃ (e : (DynamicGraph.toSimpleGraph G).Adj h1.curr h2.curr),
      h2.walk = h1.walk.concat e := by
  unfold UniversalCover at hadj
  simp only [SimpleGraph.fromRel_adj, ne_eq] at hadj
  obtain ⟨_, hrel⟩ := hadj
  rcases hrel with (⟨e, heq⟩ | ⟨e, heq⟩) | (⟨e, heq⟩ | ⟨e, heq⟩)
  · exact ⟨e, heq⟩
  · unfold History.len at hlen; rw [heq, SimpleGraph.Walk.length_concat] at hlen; omega
  · unfold History.len at hlen; rw [heq, SimpleGraph.Walk.length_concat] at hlen; omega
  · exact ⟨e, heq⟩

/-- If two histories both extend to form the same longer history, they are equal. -/
lemma History.eq_of_same_extension {a b m : History G root}
    {e1 : (DynamicGraph.toSimpleGraph G).Adj a.curr m.curr}
    {e2 : (DynamicGraph.toSimpleGraph G).Adj b.curr m.curr}
    (h1 : m.walk = a.walk.concat e1) (h2 : m.walk = b.walk.concat e2) : a = b := by
  have heq : a.walk.concat e1 = b.walk.concat e2 := by rw [← h1, ← h2]
  obtain ⟨hcurr, hwalk⟩ := SimpleGraph.Walk.concat_inj heq
  cases a with | mk ca wa =>
  cases b with | mk cb wb =>
  simp only [History.mk.injEq]
  simp only at hcurr hwalk
  refine ⟨hcurr, ?_⟩
  subst hcurr
  simp only [SimpleGraph.Walk.copy_rfl_rfl] at hwalk
  exact heq_of_eq hwalk

/-- The reverse direction of cover_adj_extends_walk -/
lemma cover_adj_extends_walk' {h1 h2 : History G root}
    (hadj : (UniversalCover G root).Adj h1 h2) (hlen : h1.len = h2.len + 1) :
    ∃ (e : (DynamicGraph.toSimpleGraph G).Adj h2.curr h1.curr),
      h1.walk = h2.walk.concat e := by
  have hadj' := hadj.symm
  have hlen' : h1.len = h2.len + 1 := hlen
  exact cover_adj_extends_walk hadj' hlen'


set_option linter.unusedSectionVars false in
/-- If two vertices both extend to the same History by adjacency with the same length, they are equal. -/
lemma neighbors_of_local_max_eq {G : DynamicGraph n} {root : Fin n}
    {m pred succ : History G root}
    (hadj_pred : (UniversalCover G root).Adj pred m)
    (hadj_succ : (UniversalCover G root).Adj m succ)
    (hpred_len : m.len = pred.len + 1)
    (hsucc_len : m.len = succ.len + 1) : pred = succ := by
  obtain ⟨e1, hm_ext_pred⟩ := cover_adj_extends_walk hadj_pred hpred_len
  obtain ⟨e2, hm_ext_succ⟩ := cover_adj_extends_walk hadj_succ.symm hsucc_len
  exact History.eq_of_same_extension hm_ext_pred hm_ext_succ


/-- Cycles in the universal cover lead to contradiction. -/
lemma cycle_max_contradiction {G : DynamicGraph n} {root : Fin n}
    {v : History G root} (cyc : (UniversalCover G root).Walk v v)
    (h_cycle : cyc.IsCycle) : False := by
  have h_len := h_cycle.three_le_length
  have h_nodup := h_cycle.support_nodup
  have h_ne_nil := h_cycle.not_nil
  have h_tail_ne : cyc.support.tail ≠ [] := by
    intro h
    have h_support := SimpleGraph.Walk.length_support cyc
    have h_tail_len : cyc.support.tail.length = cyc.support.length - 1 := @List.length_tail _ cyc.support
    rw [h] at h_tail_len
    simp only [List.length_nil] at h_tail_len
    omega
  -- Find the maximum vertex by walk length using argmax
  have h_argmax_some : (cyc.support.tail.argmax History.len).isSome := by
    cases h : cyc.support.tail.argmax History.len with
    | none => simp only [List.argmax_eq_none] at h; exact absurd h h_tail_ne
    | some _ => rfl
  let m := (cyc.support.tail.argmax History.len).get h_argmax_some
  have hm_mem : m ∈ cyc.support.tail := List.argmax_mem (Option.get_mem h_argmax_some)
  have hm_max : ∀ x ∈ cyc.support.tail, x.len ≤ m.len := fun x hx =>
    List.le_of_mem_argmax hx (Option.get_mem h_argmax_some)
  have h_support_len : cyc.support.length = cyc.length + 1 := SimpleGraph.Walk.length_support cyc
  have htail_len : cyc.support.tail.length = cyc.length := by
    have := @List.length_tail _ cyc.support
    rw [h_support_len] at this
    omega
  -- Get v's neighbors in the cycle: v1 (first step) and vlast (penultimate)
  obtain ⟨v1, hadj_v_v1, cyc', hcyc_eq⟩ := SimpleGraph.Walk.not_nil_iff.mp h_ne_nil
  let vlast := cyc.penultimate
  have hvlast_adj : (UniversalCover G root).Adj vlast v := cyc.adj_penultimate h_ne_nil
  -- v1 and vlast are in support.tail (at positions 0 and length-2)
  have hv1_in_tail : v1 ∈ cyc.support.tail := by
    rw [hcyc_eq]
    simp only [SimpleGraph.Walk.support_cons, List.tail_cons]
    exact SimpleGraph.Walk.start_mem_support cyc'
  have hvlast_in_tail : vlast ∈ cyc.support.tail := by
    -- vlast = penultimate = getVert (length - 1)
    -- This is at position length - 1 in support, which is position length - 2 in tail
    simp only [vlast, SimpleGraph.Walk.penultimate]
    have hpos : cyc.length - 2 < cyc.support.tail.length := by rw [htail_len]; omega
    have h_eq : cyc.support.tail[cyc.length - 2]'hpos = cyc.getVert (cyc.length - 1) := by
      rw [List.getElem_tail]
      rw [SimpleGraph.Walk.getVert_eq_support_getElem cyc (by omega : cyc.length - 1 ≤ cyc.length)]
      congr; omega
    rw [← h_eq]
    exact List.getElem_mem hpos
  -- All vertices in support.tail have len ≤ m.len
  have hv1_le : v1.len ≤ m.len := hm_max v1 hv1_in_tail
  have hvlast_le : vlast.len ≤ m.len := hm_max vlast hvlast_in_tail
  -- By ±1 property on adjacencies
  have hdiff_v_v1 := cover_adj_length_diff v v1 hadj_v_v1
  have hdiff_vlast_v := cover_adj_length_diff vlast v hvlast_adj
  -- Case split on whether m = v (v is max) or not
  by_cases hm_eq_v : m = v
  · -- Case: v is the global maximum
    -- Both neighbors v1 and vlast have len ≤ v.len (= m.len)
    have hv1_le' : v1.len ≤ v.len := by rw [← hm_eq_v]; exact hv1_le
    have hvlast_le' : vlast.len ≤ v.len := by rw [← hm_eq_v]; exact hvlast_le
    -- By ±1: v1.len = v.len ± 1, and since v1.len ≤ v.len, we have v1.len = v.len - 1
    have hv1_len : v.len = v1.len + 1 := by
      rcases hdiff_v_v1 with h | h
      · -- v.len + 1 = v1.len, so v1.len > v.len, contradicts v1.len ≤ v.len
        omega
      · omega
    have hvlast_len : v.len = vlast.len + 1 := by
      rcases hdiff_vlast_v with h | h
      · omega
      · omega
    -- By extension equality: v1 = vlast
    have hv1_eq_vlast : v1 = vlast :=
      neighbors_of_local_max_eq hadj_v_v1.symm hvlast_adj.symm hv1_len hvlast_len
    -- But v1 and vlast are at different positions in support.tail
    -- v1 is at position 0, vlast is at position length - 2
    rw [hcyc_eq] at h_nodup h_len
    simp only [SimpleGraph.Walk.support_cons, List.tail_cons] at h_nodup
    simp only [SimpleGraph.Walk.length_cons] at h_len
    have h_cyc'_len : cyc'.length ≥ 2 := by omega
    -- v1 = head of cyc'.support
    have hv1_head : cyc'.support.head (SimpleGraph.Walk.support_ne_nil cyc') = v1 := by
      simp only [SimpleGraph.Walk.head_support]
    -- vlast = cyc'.getVert (cyc'.length - 1)
    have hvlast_pos : vlast = cyc'.getVert (cyc'.length - 1) := by
      simp only [vlast, SimpleGraph.Walk.penultimate, hcyc_eq, SimpleGraph.Walk.length_cons]
      have hn : cyc'.length ≠ 0 := by omega
      rw [Nat.add_sub_cancel, SimpleGraph.Walk.getVert_cons _ _ hn]
    have h_support_len' : cyc'.support.length = cyc'.length + 1 := SimpleGraph.Walk.length_support cyc'
    have h0_lt : 0 < cyc'.support.length := by omega
    have h_idx_valid : cyc'.length - 1 < cyc'.support.length := by omega
    have hv1_at_0 : v1 = cyc'.support[0]'h0_lt := by
      rw [← List.head_eq_getElem]; exact hv1_head.symm
    have hvlast_at_idx : vlast = cyc'.support[cyc'.length - 1]'h_idx_valid := by
      rw [hvlast_pos, SimpleGraph.Walk.getVert_eq_support_getElem cyc' (by omega)]
    -- v1 = vlast means indices 0 = cyc'.length - 1
    have h_elems_eq : cyc'.support[0]'h0_lt = cyc'.support[cyc'.length - 1]'h_idx_valid := by
      calc cyc'.support[0]'h0_lt = v1 := hv1_at_0.symm
        _ = vlast := hv1_eq_vlast
        _ = cyc'.support[cyc'.length - 1]'h_idx_valid := hvlast_at_idx
    have h_idx_eq := List.Nodup.get_inj_iff h_nodup |>.mp h_elems_eq
    simp only [Fin.ext_iff] at h_idx_eq
    omega
  · -- Case: m ≠ v, so m is an interior vertex in the cycle
    -- m ∈ support.tail and m ≠ v means m is at some position 0 ≤ k < tail.length - 1
    -- (The last position of tail is v)
    -- Find k = findIdx (· == m) in support.tail
    let k := cyc.support.tail.findIdx (· == m)
    have hk_lt : k < cyc.support.tail.length := by
      apply List.findIdx_lt_length_of_exists
      use m, hm_mem
      simp only [beq_self_eq_true]
    have hm_at_k : cyc.support.tail[k]'hk_lt = m := by
      have := @List.findIdx_getElem _ (· == m) cyc.support.tail hk_lt
      simp only [beq_iff_eq] at this
      exact this
    -- k < tail.length - 1 since m ≠ v and v is at position tail.length - 1
    have hk_lt_last : k < cyc.support.tail.length - 1 := by
      by_contra h
      push_neg at h
      have hk_eq : k = cyc.support.tail.length - 1 := by omega
      -- Then m = tail[length - 1] = v
      have hv_last : cyc.support.tail[cyc.support.tail.length - 1]'(by omega) = v := by
        have h1 : cyc.support.tail.getLast h_tail_ne = v := by
          rw [List.getLast_tail, SimpleGraph.Walk.getLast_support]
        rw [← List.getLast_eq_getElem h_tail_ne]
        exact h1
      have hm_eq_v' : m = v := by
        have hk_eq' : cyc.support.tail.length - 1 < cyc.support.tail.length := by omega
        calc m = cyc.support.tail[k]'hk_lt := hm_at_k.symm
          _ = cyc.support.tail[cyc.support.tail.length - 1]'hk_eq' := by simp only [hk_eq]
          _ = v := hv_last
      exact hm_eq_v hm_eq_v'
    -- m is at position k+1 in full support (since tail = support.drop 1)
    have hm_at_supp : cyc.support[k + 1]'(by rw [h_support_len]; omega) = m := by
      rw [← hm_at_k]
      simp only [List.getElem_tail]
    -- m's predecessors and successors in the cycle
    -- pred = support[k] (position k in support = position k-1 in tail, or v if k=0)
    -- succ = support[k+2] (position k+2 in support = position k+1 in tail)
    have hk_plus_1_lt : k + 1 < cyc.support.length := by rw [h_support_len]; omega
    have hk_plus_2_lt : k + 2 < cyc.support.length := by
      rw [h_support_len]; rw [htail_len] at hk_lt_last; omega
    have hk_lt_supp : k < cyc.support.length := by omega
    let pred := cyc.support[k]'hk_lt_supp
    let succ := cyc.support[k + 2]'hk_plus_2_lt
    -- pred and succ are adjacent to m in UniversalCover (via walk structure)
    have hadj_pred_m : (UniversalCover G root).Adj pred m := by
      have h1 : pred = cyc.getVert k := (SimpleGraph.Walk.getVert_eq_support_getElem cyc (by omega)).symm
      have h2 : m = cyc.getVert (k + 1) := by
        rw [← hm_at_supp, SimpleGraph.Walk.getVert_eq_support_getElem cyc (by omega)]
      rw [h1, h2]
      exact SimpleGraph.Walk.adj_getVert_succ cyc (by omega : k < cyc.length)
    have hadj_m_succ : (UniversalCover G root).Adj m succ := by
      have h1 : m = cyc.getVert (k + 1) := by
        rw [← hm_at_supp, SimpleGraph.Walk.getVert_eq_support_getElem cyc (by omega)]
      have h2 : succ = cyc.getVert (k + 2) := (SimpleGraph.Walk.getVert_eq_support_getElem cyc (by omega)).symm
      rw [h1, h2]
      exact SimpleGraph.Walk.adj_getVert_succ cyc (by omega : k + 1 < cyc.length)
    -- pred and succ are in support.tail (pred at k-1 or as v at last, succ at k+1)
    have hpred_in_tail : pred ∈ cyc.support.tail := by
      simp only [pred]
      by_cases hk_zero : k = 0
      · -- pred = support[0] = v, which is at tail[length - 1]
        have h0_lt : 0 < cyc.support.length := by omega
        have hpred_eq : cyc.support[k]'hk_lt_supp = cyc.support[0]'h0_lt := by simp only [hk_zero]
        have hv : cyc.support[0]'h0_lt = v := by
          rw [← List.head_eq_getElem]
          exact SimpleGraph.Walk.head_support cyc
        have hv_in_tail : v ∈ cyc.support.tail := by
          have hv_last : cyc.support.tail.getLast h_tail_ne = v := by
            rw [List.getLast_tail, SimpleGraph.Walk.getLast_support]
          simpa [hv_last] using List.getLast_mem h_tail_ne
        rw [hpred_eq, hv]
        exact hv_in_tail
      · -- pred = support[k] with k > 0, so it's tail[k-1]
        have hk_pos : k - 1 < cyc.support.tail.length := by omega
        have heq : cyc.support[k]'hk_lt_supp = cyc.support.tail[k - 1]'hk_pos := by
          rw [List.getElem_tail]; congr; omega
        rw [heq]
        exact List.getElem_mem hk_pos
    have hsucc_in_tail : succ ∈ cyc.support.tail := by
      simp only [succ]
      have hk1_pos : k + 1 < cyc.support.tail.length := by rw [htail_len]; omega
      have heq : cyc.support[k + 2]'hk_plus_2_lt = cyc.support.tail[k + 1]'hk1_pos := by
        rw [List.getElem_tail]
      rw [heq]
      exact List.getElem_mem hk1_pos
    -- By argmax: pred.len ≤ m.len and succ.len ≤ m.len
    have hpred_le : pred.len ≤ m.len := hm_max pred hpred_in_tail
    have hsucc_le : succ.len ≤ m.len := hm_max succ hsucc_in_tail
    -- By ±1 property
    have hdiff_pred := cover_adj_length_diff pred m hadj_pred_m
    have hdiff_succ := cover_adj_length_diff m succ hadj_m_succ
    -- Combined: pred.len = m.len - 1 and succ.len = m.len - 1
    have hpred_len : m.len = pred.len + 1 := by
      rcases hdiff_pred with h | h <;> omega
    have hsucc_len : m.len = succ.len + 1 := by
      rcases hdiff_succ with h | h <;> omega
    -- By extension equality: pred = succ
    have hpred_eq_succ : pred = succ :=
      neighbors_of_local_max_eq hadj_pred_m hadj_m_succ hpred_len hsucc_len
    -- But pred and succ are at different positions in support.tail
    -- pred is at position k-1 (or tail.length-1 if k=0)
    -- succ is at position k+1
    have hsucc_pos : succ = cyc.support.tail[k + 1]'(by rw [htail_len]; omega) := by
      simp only [succ]
      rw [List.getElem_tail]
    by_cases hk_zero : k = 0
    · -- pred = v = tail[length - 1], succ = tail[1]
      have hpred_pos : pred = cyc.support.tail[cyc.support.tail.length - 1]'(by omega) := by
        simp only [pred, hk_zero]
        have hv : cyc.support[0] = v := by
          rw [← List.head_eq_getElem]
          exact SimpleGraph.Walk.head_support cyc
        have hv_last : cyc.support.tail[cyc.support.tail.length - 1]'(by omega) = v := by
          have h1 : cyc.support.tail.getLast h_tail_ne = v := by
            rw [List.getLast_tail, SimpleGraph.Walk.getLast_support]
          rw [← List.getLast_eq_getElem h_tail_ne]
          exact h1
        calc cyc.support[0] = v := hv
          _ = cyc.support.tail[cyc.support.tail.length - 1] := hv_last.symm
      have hsucc_pos_k0 : succ = cyc.support.tail[1]'(by rw [htail_len]; omega) := by
        simp only [succ, hk_zero]
        rw [List.getElem_tail]
      -- pred = tail[length - 1], succ = tail[1]
      -- If pred = succ, then indices length - 1 = 1, so length = 2
      -- But tail.length = cyc.length ≥ 3
      have h_elems_eq : cyc.support.tail[cyc.support.tail.length - 1]'(by omega) =
                        cyc.support.tail[1]'(by rw [htail_len]; omega) := by
        rw [← hpred_pos, ← hsucc_pos_k0, hpred_eq_succ]
      have h_idx_eq := List.Nodup.get_inj_iff h_nodup |>.mp h_elems_eq
      simp only [Fin.ext_iff] at h_idx_eq
      rw [htail_len] at h_idx_eq
      omega
    · -- pred = tail[k - 1], succ = tail[k + 1]
      have hpred_pos : pred = cyc.support.tail[k - 1]'(by omega) := by
        simp only [pred]
        rw [List.getElem_tail]; congr; omega
      -- If pred = succ, then k - 1 = k + 1, impossible
      have h_elems_eq : cyc.support.tail[k - 1]'(by omega) =
                        cyc.support.tail[k + 1]'(by rw [htail_len]; omega) := by
        rw [← hpred_pos, ← hsucc_pos, hpred_eq_succ]
      have h_idx_eq := List.Nodup.get_inj_iff h_nodup |>.mp h_elems_eq
      simp only [Fin.ext_iff] at h_idx_eq
      omega

set_option linter.unusedSectionVars false in
/-- The Universal Cover is acyclic. -/
theorem universal_cover_is_classical (G : DynamicGraph n) (root : Fin n) :
    (UniversalCover G root).IsAcyclic := by
  intro v cyc h_cycle
  have h_len := h_cycle.three_le_length
  have h_nodup := h_cycle.support_nodup
  have h_tail_ne : cyc.support.tail ≠ [] := by
    intro h
    have h_support := SimpleGraph.Walk.length_support cyc
    have h_tail_len : cyc.support.tail.length = cyc.support.length - 1 := @List.length_tail _ cyc.support
    rw [h] at h_tail_len
    simp only [List.length_nil] at h_tail_len
    omega
  have h_ne_nil : ¬cyc.Nil := h_cycle.not_nil
  obtain ⟨v1, hadj_v_v1, cyc', hcyc_eq⟩ := SimpleGraph.Walk.not_nil_iff.mp h_ne_nil
  have hdiff_v_v1 := cover_adj_length_diff v v1 hadj_v_v1
  let vlast := cyc.penultimate
  have hvlast_adj : (UniversalCover G root).Adj vlast v := cyc.adj_penultimate h_ne_nil
  have hdiff_vlast_v := cover_adj_length_diff vlast v hvlast_adj
  rcases hdiff_v_v1 with hv1_higher | hv1_lower <;>
  rcases hdiff_vlast_v with hvlast_higher | hvlast_lower
  · have h_cyc'_ne_nil : ¬cyc'.Nil := by
      intro hnil
      rw [hcyc_eq] at h_len
      simp only [SimpleGraph.Walk.length_cons] at h_len
      have := SimpleGraph.Walk.nil_iff_length_eq.mp hnil
      omega
    obtain ⟨v2, hadj_v1_v2, cyc'', hcyc'_eq⟩ := SimpleGraph.Walk.not_nil_iff.mp h_cyc'_ne_nil
    have hdiff_v1_v2 := cover_adj_length_diff v1 v2 hadj_v1_v2
    rcases hdiff_v1_v2 with hv2_higher | hv2_lower
    · have h_argmax_some : (cyc.support.tail.argmax History.len).isSome := by
        cases h : cyc.support.tail.argmax History.len with
        | none => simp only [List.argmax_eq_none] at h; exact absurd h h_tail_ne
        | some _ => rfl
      let m := (cyc.support.tail.argmax History.len).get h_argmax_some
      have hm_mem : m ∈ cyc.support.tail := List.argmax_mem (Option.get_mem h_argmax_some)
      have hm_max : ∀ x ∈ cyc.support.tail, x.len ≤ m.len := fun x hx =>
        List.le_of_mem_argmax hx (Option.get_mem h_argmax_some)
      exact cycle_max_contradiction cyc h_cycle
    · have hv_len_eq : v.len = v1.len - 1 := by omega
      have hv2_len_eq : v2.len = v1.len - 1 := by omega
      have hv_len : v1.len = v.len + 1 := hv1_higher.symm
      have hv2_len : v1.len = v2.len + 1 := hv2_lower.symm
      have hv_eq_v2 : v = v2 := neighbors_of_local_max_eq hadj_v_v1 hadj_v1_v2 hv_len hv2_len
      rw [hcyc_eq, hcyc'_eq] at h_nodup
      simp only [SimpleGraph.Walk.support_cons, List.tail_cons] at h_nodup
      rw [hcyc_eq, hcyc'_eq] at h_len
      simp only [SimpleGraph.Walk.length_cons] at h_len
      have h_cyc''_len : cyc''.length ≥ 1 := by omega
      have h_v_ne_v2 : v ≠ v2 := by
        intro heq
        have h_nodup_tail : cyc''.support.Nodup := by
          simp only [List.nodup_cons] at h_nodup
          exact h_nodup.2
        have h_start := SimpleGraph.Walk.start_mem_support cyc''
        have h_end := SimpleGraph.Walk.end_mem_support cyc''
        have h_support_len : cyc''.support.length = cyc''.length + 1 := SimpleGraph.Walk.length_support cyc''
        have h_support_ge2 : cyc''.support.length ≥ 2 := by omega
        have h_first : cyc''.support[0]'(by omega) = v2 := by
          rw [← List.head_eq_getElem]
          exact SimpleGraph.Walk.head_support cyc''
        have h_last : cyc''.support[cyc''.support.length - 1]'(by omega) = v := by
          have h_ne : cyc''.support ≠ [] := SimpleGraph.Walk.support_ne_nil cyc''
          rw [← List.getLast_eq_getElem h_ne, SimpleGraph.Walk.getLast_support]
        have h_idx_ne : (0 : ℕ) ≠ cyc''.support.length - 1 := by omega
        have h_elems_eq : cyc''.support[0]'(by omega) = cyc''.support[cyc''.support.length - 1]'(by omega) := by
          rw [h_first, h_last, heq]
        have h_idx_eq := List.Nodup.get_inj_iff h_nodup_tail |>.mp h_elems_eq
        simp only [Fin.ext_iff] at h_idx_eq
        exact h_idx_ne h_idx_eq
      exact h_v_ne_v2 hv_eq_v2
  · exact cycle_max_contradiction cyc h_cycle
  · have hv1_len : v.len = v1.len + 1 := hv1_lower.symm
    have hvlast_len : v.len = vlast.len + 1 := hvlast_higher.symm
    obtain ⟨e1, hv_ext_v1⟩ := cover_adj_extends_walk' hadj_v_v1 hv1_len
    obtain ⟨e2, hv_ext_vlast⟩ := cover_adj_extends_walk' hvlast_adj.symm hvlast_len
    have hv1_eq_vlast : v1 = vlast := History.eq_of_same_extension hv_ext_v1 hv_ext_vlast
    have h_ne : v1 ≠ vlast := by
      intro heq
      rw [hcyc_eq] at h_len h_nodup
      simp only [SimpleGraph.Walk.length_cons] at h_len
      simp only [SimpleGraph.Walk.support_cons, List.tail_cons] at h_nodup
      have h_cyc'_len : cyc'.length ≥ 2 := by omega
      have h_idx_ne : (0 : ℕ) ≠ cyc'.length - 1 := by omega
      have hv1_head : cyc'.support.head (SimpleGraph.Walk.support_ne_nil cyc') = v1 := by
        simp only [SimpleGraph.Walk.head_support]
      have hvlast_pos : vlast = cyc'.getVert (cyc'.length - 1) := by
        simp only [vlast, SimpleGraph.Walk.penultimate, hcyc_eq, SimpleGraph.Walk.length_cons]
        have hn : cyc'.length ≠ 0 := by omega
        rw [Nat.add_sub_cancel, SimpleGraph.Walk.getVert_cons _ _ hn]
      have h_support_len : cyc'.support.length = cyc'.length + 1 := SimpleGraph.Walk.length_support cyc'
      have h_idx_valid : cyc'.length - 1 < cyc'.support.length := by omega
      have hvlast_in_support : vlast = cyc'.support[cyc'.length - 1] := by
        rw [hvlast_pos, SimpleGraph.Walk.getVert_eq_support_getElem cyc' (by omega)]
      have h0_lt : 0 < cyc'.support.length := by omega
      have hv1_in_support : v1 = cyc'.support[0]'h0_lt := by
        have h := hv1_head.symm
        rw [List.head_eq_getElem] at h
        exact h
      have h_elems_eq : cyc'.support[0]'h0_lt = cyc'.support[cyc'.length - 1]'h_idx_valid := by
        calc cyc'.support[0] = v1 := hv1_in_support.symm
          _ = vlast := heq
          _ = cyc'.support[cyc'.length - 1] := hvlast_in_support
      have h_idx_eq := List.Nodup.get_inj_iff h_nodup |>.mp h_elems_eq
      simp only [Fin.ext_iff] at h_idx_eq
      exact h_idx_ne h_idx_eq
    exact h_ne hv1_eq_vlast
  · exact cycle_max_contradiction cyc h_cycle

/-! ## 3. The Resolution of Paradox -/

/-- Lift constraint field to universal cover. -/
noncomputable def lift_form (G : DynamicGraph n) (σ : ActiveForm G) (root : Fin n)
    (h_src h_dst : History G root) : ℝ :=
  -- In the Universal Cover, adjacency means one history extends the other by one edge.
  -- If adjacent with h_dst extending h_src: return σ(src.curr, dst.curr)
  -- If adjacent with h_src extending h_dst: return -σ(dst.curr, src.curr)
  -- Since this is a tree, we can simply use the walk lengths to determine direction.
  if h_dst.walk.length = h_src.walk.length + 1 then σ.val.val h_src.curr h_dst.curr
  else if h_src.walk.length = h_dst.walk.length + 1 then -(σ.val.val h_dst.curr h_src.curr)
  else 0

/-- Sum of σ values along a walk's edges. -/
noncomputable def walk_sum (G : DynamicGraph n) (σ : ActiveForm G) :
    ∀ {u v : Fin n}, (DynamicGraph.toSimpleGraph G).Walk u v → ℝ
  | _, _, .nil => 0
  | u, _, @SimpleGraph.Walk.cons _ _ _ v _ _hadj p => σ.val.val u v + walk_sum G σ p

/-- Potential = sum of constraints along history. -/
noncomputable def history_potential (G : DynamicGraph n) (σ : ActiveForm G) (root : Fin n)
    (h : History G root) : ℝ :=
  walk_sum G σ h.walk

set_option linter.unusedSectionVars false in
/-- walk_sum of an appended walk equals sum of both parts. -/
lemma walk_sum_append (G : DynamicGraph n) (σ : ActiveForm G) {u v w : Fin n}
    (p : (DynamicGraph.toSimpleGraph G).Walk u v) (q : (DynamicGraph.toSimpleGraph G).Walk v w) :
    walk_sum G σ (p.append q) = walk_sum G σ p + walk_sum G σ q := by
  induction p with
  | nil => simp [walk_sum]
  | cons h p' ih =>
    simp only [SimpleGraph.Walk.append, walk_sum, ih]
    ring

set_option linter.unusedSectionVars false in
/-- walk_sum of a concatenated walk equals original sum plus the new edge value. -/
lemma walk_sum_concat (G : DynamicGraph n) (σ : ActiveForm G) {u v w : Fin n}
    (p : (DynamicGraph.toSimpleGraph G).Walk u v) (hadj : (DynamicGraph.toSimpleGraph G).Adj v w) :
    walk_sum G σ (p.concat hadj) = walk_sum G σ p + σ.val.val v w := by
  unfold SimpleGraph.Walk.concat
  rw [walk_sum_append]
  simp [walk_sum]

set_option linter.unusedSectionVars false in
/-- Reversing a walk negates its sum (by skew-symmetry of σ). -/
lemma walk_sum_reverse (G : DynamicGraph n) (σ : ActiveForm G) {u v : Fin n}
    (p : (DynamicGraph.toSimpleGraph G).Walk u v) :
    walk_sum G σ p.reverse = -walk_sum G σ p := by
  induction p with
  | nil => simp [walk_sum]
  | cons hadj p' ih =>
    rw [SimpleGraph.Walk.reverse_cons, walk_sum_append, ih]
    simp only [walk_sum, add_zero]
    -- The goal involves σ.val v u = -σ.val u v (skew symmetry)
    rw [σ.val.skew]
    ring

set_option linter.unusedSectionVars false in
/-- Copying a walk preserves its sum. -/
lemma walk_sum_copy (G : DynamicGraph n) (σ : ActiveForm G) {u v u' v' : Fin n}
    (p : (DynamicGraph.toSimpleGraph G).Walk u v) (hu : u = u') (hv : v = v') :
    walk_sum G σ (p.copy hu hv) = walk_sum G σ p := by
  subst hu hv
  simp only [SimpleGraph.Walk.copy_rfl_rfl]

/-! ## 3a. The Holonomy Interpretation

Two histories reaching the same vertex may have different potentials.
Their difference is precisely the holonomy of σ around the loop they form.
-/

set_option linter.unusedSectionVars false in
/-- Potential difference between histories equals holonomy around their loop. -/
theorem history_potential_diff_is_holonomy (G : DynamicGraph n) (σ : ActiveForm G) (root : Fin n)
    (h1 h2 : History G root) (h_same : h1.curr = h2.curr) :
    history_potential G σ root h1 - history_potential G σ root h2 =
    walk_sum G σ (h1.walk.append (h2.walk.reverse.copy h_same.symm rfl)) := by
  unfold history_potential
  rw [walk_sum_append, walk_sum_copy, walk_sum_reverse]
  ring

/-- Every field becomes exact in the Universal Cover. -/
theorem paradox_dissolves_in_cover (G : DynamicGraph n) (σ : ActiveForm G) (root : Fin n) :
    ∃ (Φ : History G root → ℝ),
      ∀ (u v : History G root), (UniversalCover G root).Adj u v →
        lift_form G σ root u v = Φ v - Φ u := by
  use history_potential G σ root
  intro u v h_adj
  unfold UniversalCover at h_adj
  simp only [SimpleGraph.fromRel_adj, ne_eq] at h_adj
  obtain ⟨_, h_ext⟩ := h_adj
  have case_v_extends_u : ∀ hadj : (DynamicGraph.toSimpleGraph G).Adj u.curr v.curr,
      v.walk = u.walk.concat hadj →
      lift_form G σ root u v = history_potential G σ root v - history_potential G σ root u := by
    intro hadj hv_eq
    unfold lift_form history_potential
    have h_len : v.walk.length = u.walk.length + 1 := by
      rw [hv_eq, SimpleGraph.Walk.length_concat]
    simp only [h_len, ite_true]
    rw [hv_eq, walk_sum_concat]
    ring
  have case_u_extends_v : ∀ hadj : (DynamicGraph.toSimpleGraph G).Adj v.curr u.curr,
      u.walk = v.walk.concat hadj →
      lift_form G σ root u v = history_potential G σ root v - history_potential G σ root u := by
    intro hadj hu_eq
    unfold lift_form history_potential
    have h_len : u.walk.length = v.walk.length + 1 := by rw [hu_eq, SimpleGraph.Walk.length_concat]
    have h1 : v.walk.length ≠ u.walk.length + 1 := by omega
    rw [if_neg h1, if_pos h_len, hu_eq, walk_sum_concat]
    ring
  -- Apply to all 4 subcases (pairs are symmetric)
  rcases h_ext with (⟨hadj, heq⟩ | ⟨hadj, heq⟩) | (⟨hadj, heq⟩ | ⟨hadj, heq⟩)
  · exact case_v_extends_u hadj heq
  · exact case_u_extends_v hadj heq
  · exact case_u_extends_v hadj heq
  · exact case_v_extends_u hadj heq

/-! ## 4. The Walk-Based Stokes Theorem -/

set_option linter.unusedSectionVars false in
/-- Walk-based Stokes Theorem: walk_sum of a gradient equals the potential difference. -/
theorem walk_stokes (G : DynamicGraph n) (φ : C0 n) {u v : Fin n}
    (w : (DynamicGraph.toSimpleGraph G).Walk u v) :
    walk_sum G (d_G G φ) w = φ v - φ u := by
  induction w with
  | nil => simp [walk_sum]
  | cons hadj w' ih =>
    simp only [walk_sum]
    rw [ih]
    -- hadj : (DynamicGraph.toSimpleGraph G).Adj a b  ≡  (a, b) ∈ G.active_edges
    simp only [d_G, DynamicGraph.toSimpleGraph] at hadj ⊢
    simp only [hadj, if_true]
    ring

set_option linter.unusedSectionVars false in
/-- Corollary: walk_sum of a gradient around any closed walk is zero. -/
theorem exact_walk_closed (G : DynamicGraph n) (φ : C0 n) {v : Fin n}
    (w : (DynamicGraph.toSimpleGraph G).Walk v v) :
    walk_sum G (d_G G φ) w = 0 := by
  rw [walk_stokes]
  ring

set_option linter.unusedSectionVars false in
/-- walk_sum is additive in the form. -/
lemma walk_sum_add (G : DynamicGraph n) (σ τ : ActiveForm G) {u v : Fin n}
    (w : (DynamicGraph.toSimpleGraph G).Walk u v) :
    walk_sum G (σ + τ) w = walk_sum G σ w + walk_sum G τ w := by
  induction w with
  | nil => simp [walk_sum]
  | cons _ w' ih =>
    simp only [walk_sum]
    rw [ih]
    -- (σ + τ).val.val a b = σ.val.val a b + τ.val.val a b by definition
    simp only [add_comm, add_left_comm, add_assoc]; rfl

set_option linter.unusedSectionVars false in
/-- walk_sum around a closed walk equals walk_sum of the harmonic projection. -/
theorem walk_sum_factors_through_harmonic (G : DynamicGraph n) (σ : ActiveForm G) {v : Fin n}
    (w : (DynamicGraph.toSimpleGraph G).Walk v v) :
    ∃ (φ : C0 n) (γ : ActiveForm G),
      σ = d_G G φ + γ ∧
      γ ∈ Diaspora.Hodge.HarmonicSubspace G ∧
      walk_sum G σ w = walk_sum G γ w := by
  obtain ⟨φ, γ, h_decomp, h_harm, _⟩ := Diaspora.Hodge.hodge_decomposition_graph G σ
  refine ⟨φ, γ, h_decomp, h_harm, ?_⟩
  -- σ = d_G φ + γ, so walk_sum σ = walk_sum (d_G φ) + walk_sum γ = 0 + walk_sum γ
  rw [h_decomp, walk_sum_add, exact_walk_closed, zero_add]

/-! ## 4a. The Walk Detector for Paradox -/

set_option linter.unusedSectionVars false in
/-- Non-zero walk_sum implies unsatisfiability. -/
theorem walk_sum_implies_unsatisfiable
    (T : Theory n) (h_cons : LocallyConsistent T)
    {v : Fin n} (w : (DynamicGraph.toSimpleGraph (theory_graph T)).Walk v v)
    (h_nonzero : walk_sum (theory_graph T) (realize T) w ≠ 0) :
    ¬ Satisfiable T := by
  intro h_sat
  -- 1. Satisfiable implies exact
  have h_exact := (satisfiable_iff_exact_on_graph T h_cons).mp h_sat
  -- 2. Exact means realize T = d_G φ for some φ
  rw [ImGradient, LinearMap.mem_range] at h_exact
  obtain ⟨φ, h_eq⟩ := h_exact
  -- 3. walk_sum of d_G φ is zero on closed walks (by Stokes)
  have h_zero : walk_sum (theory_graph T) (d_G_linear (theory_graph T) φ) w = 0 :=
    exact_walk_closed (theory_graph T) φ w
  -- 4. But d_G φ = realize T, so walk_sum (realize T) should also be 0
  have h_walk_eq : walk_sum (theory_graph T) (realize T) w =
                   walk_sum (theory_graph T) (d_G_linear (theory_graph T) φ) w := by
    congr 1
    exact h_eq.symm
  -- 5. Contradiction: we assumed walk_sum ≠ 0
  rw [h_walk_eq, h_zero] at h_nonzero
  exact h_nonzero rfl

/-- If a theory is satisfiable, then every closed walk has zero walk_sum. -/
theorem satisfiable_implies_walk_sum_zero
    (T : Theory n) (h_cons : LocallyConsistent T) (h_sat : Satisfiable T)
    {v : Fin n} (w : (DynamicGraph.toSimpleGraph (theory_graph T)).Walk v v) :
    walk_sum (theory_graph T) (realize T) w = 0 := by
  by_contra h_nonzero
  exact walk_sum_implies_unsatisfiable T h_cons w h_nonzero h_sat

/-! ## 5. The Discrete Monodromy Theorem -/

/-- Exact forms have zero walk_sum on all closed walks. -/
theorem exact_implies_walk_sum_zero (G : DynamicGraph n) (σ : ActiveForm G)
    (h_exact : σ ∈ ImGradient G)
    {v : Fin n} (w : (DynamicGraph.toSimpleGraph G).Walk v v) :
    walk_sum G σ w = 0 := by
  rw [ImGradient, LinearMap.mem_range] at h_exact
  obtain ⟨φ, hφ⟩ := h_exact
  rw [← hφ]
  exact exact_walk_closed G φ w

omit [Fintype (Fin n)] [DecidableEq (Fin n)] in
/-- Scalar multiplication acts pointwise on ActiveForm values. -/
lemma smul_active_form_val (G : DynamicGraph n) (c : ℝ) (σ : ActiveForm G) (i j : Fin n) :
    (c • σ).val.val i j = c * σ.val.val i j := rfl

omit [Fintype (Fin n)] [DecidableEq (Fin n)] in
/-- Helper: walk_sum respects scalar multiplication. -/
lemma walk_sum_smul (G : DynamicGraph n) (c : ℝ) (σ : ActiveForm G) {u v : Fin n}
    (w : (DynamicGraph.toSimpleGraph G).Walk u v) :
    walk_sum G (c • σ) w = c * walk_sum G σ w := by
  induction w with
  | nil => simp [walk_sum]
  | cons h_adj w' ih =>
    simp only [walk_sum]
    rw [smul_active_form_val, ih]
    ring

/-- On an acyclic graph, harmonic forms vanish on all edges (every edge is a bridge). -/
lemma harmonic_zero_on_edges_acyclic
    (G : DynamicGraph n) (h_acyclic : (DynamicGraph.toSimpleGraph G).IsAcyclic)
    (γ : ActiveForm G) (h_harm : γ ∈ HarmonicSubspace G)
    {u v : Fin n} (h_adj : (DynamicGraph.toSimpleGraph G).Adj u v) :
    γ.val.val u v = 0 := by
  classical
  -- Setup: G' is the graph with edge (u,v) deleted
  let G' := (DynamicGraph.toSimpleGraph G).deleteEdges {s(u, v)}
  -- φ is the indicator: 1 on v's side, 0 on u's side
  let φ : C0 n := fun x => if G'.Reachable v x then 1 else 0
  -- Key property: (u, v) is a bridge since G is acyclic
  have h_bridge := SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp h_acyclic h_adj
  rw [SimpleGraph.isBridge_iff] at h_bridge
  have h_not_reach_uv : ¬ G'.Reachable u v := h_bridge.2
  have h_not_reach_vu : ¬ G'.Reachable v u := fun h => h_not_reach_uv h.symm
  -- φ(v) = 1, φ(u) = 0
  have h_φv : φ v = 1 := if_pos (SimpleGraph.Reachable.refl (G := G') (u := v))
  have h_φu : φ u = 0 := if_neg h_not_reach_vu
  -- Note: h_adj is SimpleGraph.Adj which is the same as membership in active_edges
  have h_adj_uv : (u, v) ∈ G.active_edges := h_adj
  have h_adj_vu : (v, u) ∈ G.active_edges := (G.symmetric u v).mp h_adj
  -- d_G(φ) is 1 on (u,v), 0 elsewhere (except -1 on (v,u))
  have h_d_uv : (d_G G φ).val.val u v = 1 := by
    unfold d_G
    simp only
    rw [if_pos h_adj_uv, h_φv, h_φu]
    ring
  have h_d_vu : (d_G G φ).val.val v u = -1 := by
    unfold d_G
    simp only
    rw [if_pos h_adj_vu, h_φu, h_φv]
    ring
  -- For other edges, d_G(φ) = 0 because both endpoints are on the same side
  have h_d_other : ∀ a b, (a, b) ∈ G.active_edges → (a, b) ≠ (u, v) → (a, b) ≠ (v, u) →
      (d_G G φ).val.val a b = 0 := by
    intro a b h_ab h_ne_uv h_ne_vu
    unfold d_G
    simp only
    rw [if_pos h_ab]
    -- Edge (a, b) is still in G' (we only deleted {u, v})
    have h_ab_in_G' : G'.Adj a b := by
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨h_ab, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro h_eq
      cases Sym2.eq_iff.mp h_eq with
      | inl h => exact h_ne_uv (Prod.ext h.1 h.2)
      | inr h => exact h_ne_vu (Prod.ext h.1 h.2)
    -- φ(a) = φ(b): if one is reachable from v, so is the other
    have h_eq : φ a = φ b := by
      by_cases h_va : G'.Reachable v a
      · have h_vb : G'.Reachable v b := h_va.trans ⟨SimpleGraph.Walk.cons h_ab_in_G' .nil⟩
        simp only [φ, h_va, h_vb, if_true]
      · by_cases h_vb : G'.Reachable v b
        · have h_va' : G'.Reachable v a := h_vb.trans ⟨SimpleGraph.Walk.cons h_ab_in_G'.symm .nil⟩
          exact absurd h_va' h_va
        · simp only [φ, h_va, h_vb, if_false]
    rw [h_eq]
    ring
  -- Now compute ⟨γ, d_G φ⟩
  -- γ ∈ HarmonicSubspace = (ImGradient)^⊥ means ⟨γ, d_G φ⟩ = 0 for all φ
  rw [HarmonicSubspace, Submodule.mem_orthogonal] at h_harm
  have h_in_im : d_G_linear G φ ∈ ImGradient G := ⟨φ, rfl⟩
  have h_orth := h_harm (d_G_linear G φ) h_in_im
  -- h_orth says ⟨d_G φ, γ⟩ = 0
  -- The inner product is Diaspora.Core.ActiveForm.inner which is (1/2) Σ σ(i,j) * τ(i,j)
  -- Compute: ⟨d_G φ, γ⟩ = (1/2) Σ d_G(φ)(i,j) * γ(i,j)
  --                     = (1/2) [1 * γ(u,v) + (-1) * γ(v,u)]
  --                     = (1/2) [γ(u,v) + γ(u,v)]  (by skew symmetry)
  --                     = γ(u,v)
  -- The `inner ℝ` on ActiveForm is defined as ActiveForm.inner
  change Diaspora.Core.ActiveForm.inner (d_G_linear G φ) γ = 0 at h_orth
  unfold Diaspora.Core.ActiveForm.inner inner_product_C1 at h_orth
  have h_skew : γ.val.val v u = -γ.val.val u v := γ.val.skew v u
  have h_u_ne_v : u ≠ v := h_adj.ne
  -- The sum reduces to just the (u,v) and (v,u) terms
  have h_sum : ∑ i, ∑ j, (d_G_linear G φ).val.val i j * γ.val.val i j = 2 * γ.val.val u v := by
    -- Every term in the sum is 0 except (u,v) and (v,u)
    have h_term_zero : ∀ i j, (i, j) ≠ (u, v) → (i, j) ≠ (v, u) →
        (d_G_linear G φ).val.val i j * γ.val.val i j = 0 := by
      intro i j h1 h2
      by_cases h_active : (i, j) ∈ G.active_edges
      · show (d_G G φ).val.val i j * γ.val.val i j = 0
        rw [h_d_other i j h_active h1 h2, zero_mul]
      · show (d_G G φ).val.val i j * γ.val.val i j = 0
        unfold d_G; simp only; rw [if_neg h_active, zero_mul]
    -- The only nonzero terms are (u,v) contributing γ(u,v) and (v,u) contributing -γ(v,u) = γ(u,v)
    have h_uv_term : (d_G_linear G φ).val.val u v * γ.val.val u v = γ.val.val u v := by
      show (d_G G φ).val.val u v * γ.val.val u v = _
      rw [h_d_uv]; ring
    have h_vu_term : (d_G_linear G φ).val.val v u * γ.val.val v u = γ.val.val u v := by
      show (d_G G φ).val.val v u * γ.val.val v u = _
      rw [h_d_vu, h_skew]; ring
    -- Compute the sum by case analysis using pairs
    -- Convert double sum to sum over pairs, then use the fact that only (u,v) and (v,u) are nonzero
    have h_ne : u ≠ v := h_adj.ne
    have h_eq : ∑ i, ∑ j, (d_G_linear G φ).val.val i j * γ.val.val i j =
                (d_G_linear G φ).val.val u v * γ.val.val u v +
                (d_G_linear G φ).val.val v u * γ.val.val v u := by
      let f : Fin n × Fin n → ℝ := fun p => (d_G_linear G φ).val.val p.1 p.2 * γ.val.val p.1 p.2
      -- Convert double sum to single sum over pairs
      -- Fintype.sum_prod_type says: ∑ x, f x = ∑ x, ∑ y, f (x, y)
      have h_double_to_pair : ∑ i, ∑ j, (d_G_linear G φ).val.val i j * γ.val.val i j =
          ∑ p : Fin n × Fin n, f p := (Fintype.sum_prod_type f).symm
      rw [h_double_to_pair]
      -- The set {(u,v), (v,u)} has the nonzero terms
      have h_pair_ne : (u, v) ≠ (v, u) := by simp [h_ne.symm]
      have h_in_univ : ({(u, v), (v, u)} : Finset (Fin n × Fin n)) ⊆ Finset.univ :=
        Finset.subset_univ _
      rw [← Finset.sum_sdiff h_in_univ]
      -- The sum over the complement is zero
      have h_rest_zero : ∑ p ∈ Finset.univ \ {(u, v), (v, u)}, f p = 0 := by
        apply Finset.sum_eq_zero; intro ⟨i, j⟩ hp
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
                   Finset.mem_singleton, not_or, true_and] at hp
        exact h_term_zero i j hp.1 hp.2
      rw [h_rest_zero, zero_add]
      -- The sum over {(u,v), (v,u)} is just the two terms
      rw [Finset.sum_insert (Finset.notMem_singleton.mpr h_pair_ne), Finset.sum_singleton]
    rw [h_eq, h_uv_term, h_vu_term]; ring
  -- h_orth says (1/2) * h_sum = 0, so h_sum = 0, so γ(u,v) = 0
  rw [h_sum] at h_orth
  linarith

/-- On an acyclic graph, a nonzero harmonic form is impossible. -/
lemma divergence_free_on_acyclic_implies_zero [NeZero n]
    (G : DynamicGraph n) (h_acyclic : (DynamicGraph.toSimpleGraph G).IsAcyclic)
    (γ : ActiveForm G) (h_harm : γ ∈ HarmonicSubspace G) :
    γ = 0 := by
  -- γ is zero on all edges by harmonic_zero_on_edges_acyclic
  ext i j
  by_cases h_adj : (DynamicGraph.toSimpleGraph G).Adj i j
  · exact harmonic_zero_on_edges_acyclic G h_acyclic γ h_harm h_adj
  · -- If (i,j) is not an edge, γ(i,j) = 0 by the ActiveForm constraint
    have h_not_active : (i, j) ∉ G.active_edges := h_adj
    exact γ.property i j h_not_active

/-- If G is acyclic (a forest), then dim(HarmonicSubspace G) = 0. -/
theorem acyclic_implies_classical [NeZero n] (G : DynamicGraph n)
    (h_acyclic : (DynamicGraph.toSimpleGraph G).IsAcyclic) :
    Diaspora.Logic.IsClassical G := by
  unfold Diaspora.Logic.IsClassical
  rw [finrank_zero_iff_forall_zero]
  intro ⟨γ, hγ⟩
  simp only [Submodule.mk_eq_zero]
  exact divergence_free_on_acyclic_implies_zero G h_acyclic γ hγ

/-- If walk_sum(σ, w) = 0 for all closed walks w, then σ is exact. -/
theorem walk_sum_zero_implies_exact [NeZero n] (G : DynamicGraph n) (σ : ActiveForm G)
    (h_zero : ∀ v : Fin n, ∀ w : (DynamicGraph.toSimpleGraph G).Walk v v, walk_sum G σ w = 0) :
    σ ∈ ImGradient G := by
  -- Step 1: Hodge decomposition
  obtain ⟨φ, γ, h_decomp, h_harm, _h_orth⟩ := Diaspora.Hodge.hodge_decomposition_graph G σ
  -- Step 2: Show γ = 0 using the walk_sum hypothesis
  suffices h_gamma_zero : γ = 0 by
    rw [h_gamma_zero, add_zero] at h_decomp
    rw [ImGradient, LinearMap.mem_range]
    exact ⟨φ, h_decomp.symm⟩
  -- walk_sum(γ) = 0 on all closed walks
  have h_gamma_walk_zero : ∀ v, ∀ w : (DynamicGraph.toSimpleGraph G).Walk v v, walk_sum G γ w = 0 := by
    intro v w
    have h_σ_zero := h_zero v w
    have h1 : walk_sum G σ w = walk_sum G (d_G G φ + γ) w := by rw [h_decomp]
    have h2 : walk_sum G (d_G G φ + γ) w = walk_sum G (d_G G φ) w + walk_sum G γ w := walk_sum_add G _ _ w
    have h3 : walk_sum G (d_G G φ) w = 0 := exact_walk_closed G φ w
    rw [h1, h2, h3, zero_add] at h_σ_zero
    exact h_σ_zero
  -- Key insight: walk_sum = 0 on all closed walks implies γ ∈ Im(d_G)
  -- Combined with γ ∈ HarmonicSubspace = (Im d_G)^⊥, this gives γ = 0
  -- Proof: define a potential via path integration (well-defined by path independence)
  -- Step 1: Path independence - for any two paths p, q from u to v,
  -- walk_sum(γ, p) = walk_sum(γ, q) because p · q⁻¹ is a closed walk
  have h_path_indep : ∀ u v, ∀ (p q : (DynamicGraph.toSimpleGraph G).Walk u v),
      walk_sum G γ p = walk_sum G γ q := by
    intro u v p q
    have h_loop := h_gamma_walk_zero u (p.append q.reverse)
    rw [walk_sum_append, walk_sum_reverse] at h_loop
    linarith
  -- Step 2: Define the potential φ(v) = walk_sum(γ, any path from fixed base to v)
  -- For connected components, we fix a base vertex per component
  -- For simplicity, we use Classical.choose to pick paths
  -- The potential is 0 for vertices not reachable from v_0
  -- Step 3: Show γ ∈ Im(d_G)
  -- For any edge (u, v), d_G(φ)(u,v) = φ(v) - φ(u) = walk_sum(path to v) - walk_sum(path to u)
  -- Using path (base → u) · (u,v), we get walk_sum(path to u) + γ(u,v) for path to v
  -- So d_G(φ)(u,v) = γ(u,v)
  have h_gamma_in_im : γ ∈ ImGradient G := by
    -- Construct the potential via path integration on each connected component
    classical
    -- For each vertex v, pick a canonical base in v's connected component
    -- Then φ(v) = walk_sum(γ, path from that base to v)
    -- The key is that within each component, path independence holds
    -- For simplicity, we use Finset.min' on each component's vertices
    -- Define: base(v) = minimum vertex in v's connected component (via Reachable)
    let component : Fin n → Finset (Fin n) := fun v =>
      Finset.filter (fun w => (DynamicGraph.toSimpleGraph G).Reachable v w) Finset.univ
    have h_v_in_comp : ∀ v, v ∈ component v := by
      intro v; simp [component]
    -- Base of component = minimum vertex in it
    let base : Fin n → Fin n := fun v => (component v).min' ⟨v, h_v_in_comp v⟩
    -- base(v) is in the same component as v
    have h_base_reach : ∀ v, (DynamicGraph.toSimpleGraph G).Reachable (base v) v := by
      intro v
      have h_base_in : base v ∈ component v := Finset.min'_mem _ _
      simp [component] at h_base_in
      exact h_base_in.symm
    -- All vertices in the same component have the same base
    have h_base_eq : ∀ u v, (DynamicGraph.toSimpleGraph G).Reachable u v → base u = base v := by
      intro u v h_uv
      -- component u = component v when u and v are reachable
      have h_comp_eq : component u = component v := by
        ext w; simp [component]
        constructor
        · intro h_uw; exact h_uv.symm.trans h_uw
        · intro h_vw; exact h_uv.trans h_vw
      simp only [base, h_comp_eq]
    -- For each v, pick a path from base(v) to v
    have h_path_exists : ∀ v, ∃ (path : (DynamicGraph.toSimpleGraph G).Walk (base v) v), True := by
      intro v; exact ⟨Classical.choice (h_base_reach v), trivial⟩
    -- Define the potential
    let φ : C0 n := fun v => walk_sum G γ (Classical.choose (h_path_exists v))
    -- Path independence within a component
    have h_φ_eq : ∀ v (path : (DynamicGraph.toSimpleGraph G).Walk (base v) v),
        φ v = walk_sum G γ path := by
      intro v path
      exact h_path_indep (base v) v _ path
    -- For adjacent vertices, base(u) = base(v)
    have h_adj_base_eq : ∀ u v, (DynamicGraph.toSimpleGraph G).Adj u v → base u = base v := by
      intro u v h_adj
      exact h_base_eq u v ⟨SimpleGraph.Walk.cons h_adj .nil⟩
    -- Show d_G(φ) = γ
    have h_eq : d_G G φ = γ := by
      ext u v
      by_cases h_adj : (u, v) ∈ G.active_edges
      · have h_adj' : (DynamicGraph.toSimpleGraph G).Adj u v := h_adj
        have h_same_base : base u = base v := h_adj_base_eq u v h_adj'
        -- Get path from base v to u (reachable since base u = base v)
        have h_reach_u : (DynamicGraph.toSimpleGraph G).Reachable (base v) u := by
          rw [← h_same_base]; exact h_base_reach u
        let path_to_u : (DynamicGraph.toSimpleGraph G).Walk (base v) u := Classical.choice h_reach_u
        let path_v := path_to_u.concat h_adj'
        -- φ(u) uses a path from base u, but by path independence, equals walk_sum of any path
        -- φ(v) uses path_v from base v
        simp only [d_G, if_pos h_adj]
        -- Key: φ(u) = walk_sum from base u to u, but h_φ_eq gives us a formula from base u
        -- We use path independence to relate walk_sum from base v to u with walk_sum from base u to u
        have h_φu : φ u = walk_sum G γ (Classical.choose (h_path_exists u)) := rfl
        have h_φv : φ v = walk_sum G γ path_v := h_φ_eq v path_v
        rw [h_φv]
        -- Now we need: walk_sum path_v - φ u = γ(u,v)
        -- walk_sum path_v = walk_sum path_to_u + γ(u,v)
        rw [walk_sum_concat]
        -- Need: walk_sum path_to_u + γ(u,v) - φ u = γ(u,v)
        -- i.e., walk_sum path_to_u = φ u
        suffices h_eq_u : walk_sum G γ path_to_u = φ u by linarith
        -- path_to_u is from base v to u, and base v = base u
        -- Classical.choose (h_path_exists u) is from base u to u
        -- By path independence (with base u = base v), these have the same walk_sum
        rw [h_φu]
        -- Cast path_to_u from Walk (base v) u to Walk (base u) u using .copy
        let path_from_base_u := path_to_u.copy h_same_base.symm rfl
        -- By path independence, all walks from base u to u have the same walk_sum
        have h_pi := h_path_indep (base u) u path_from_base_u (Classical.choose (h_path_exists u))
        -- walk_sum is preserved by .copy
        have h_copy_eq : walk_sum G γ path_to_u = walk_sum G γ path_from_base_u :=
          (walk_sum_copy G γ path_to_u h_same_base.symm rfl).symm
        rw [h_copy_eq, h_pi]
      · simp only [d_G, if_neg h_adj]
        exact (γ.property u v h_adj).symm
    rw [ImGradient, LinearMap.mem_range]
    use φ
    show d_G G φ = γ
    exact h_eq
  -- Step 4: γ ∈ Im(d_G) ∩ (Im d_G)^⊥ = {0}
  have h_orth : ∀ ψ ∈ ImGradient G, inner ℝ ψ γ = 0 := h_harm
  have h_inner_zero := h_orth γ h_gamma_in_im
  -- ⟨γ, γ⟩ = 0 implies γ = 0
  exact inner_self_eq_zero.mp h_inner_zero

/-- Discrete Monodromy: exactness ↔ zero walk_sum on all closed walks. -/
theorem monodromy_exact_iff [NeZero n] (G : DynamicGraph n) (σ : ActiveForm G) :
    σ ∈ ImGradient G ↔ (∀ v : Fin n, ∀ w : (DynamicGraph.toSimpleGraph G).Walk v v, walk_sum G σ w = 0) := by
  constructor
  · intro h_exact v w
    exact exact_implies_walk_sum_zero G σ h_exact w
  · intro h_zero
    exact walk_sum_zero_implies_exact G σ h_zero

/-- A theory is satisfiable iff its realization has zero walk_sum on all closed walks. -/
theorem satisfiability_iff_walk_sum_zero [NeZero n]
    (T : Theory n) (h_cons : LocallyConsistent T) :
    Satisfiable T ↔
    (∀ v : Fin n, ∀ w : (DynamicGraph.toSimpleGraph (theory_graph T)).Walk v v,
      walk_sum (theory_graph T) (realize T) w = 0) := by
  rw [satisfiable_iff_exact_on_graph T h_cons]
  exact monodromy_exact_iff (theory_graph T) (realize T)

/-! ## 6. Trees Cannot Support Paradox -/

/-- On an acyclic graph, every locally consistent theory is satisfiable. -/
theorem acyclic_implies_satisfiable [NeZero n]
    (T : Theory n) (h_cons : LocallyConsistent T)
    (h_acyclic : (DynamicGraph.toSimpleGraph (theory_graph T)).IsAcyclic) :
    Satisfiable T := by
  -- Step 1: Acyclic implies classical (dim H = 0)
  have h_classical := acyclic_implies_classical (theory_graph T) h_acyclic

  -- Step 2: Classical means every ActiveForm is exact
  have h_all_exact : ∀ σ : ActiveForm (theory_graph T), σ ∈ ImGradient (theory_graph T) :=
    Diaspora.Logic.classical_universe_admits_no_paradoxes (theory_graph T) h_classical

  -- Step 3: In particular, realize T is exact
  have h_exact := h_all_exact (realize T)

  -- Step 4: Apply the bridge theorem
  exact (satisfiable_iff_exact_on_graph T h_cons).mpr h_exact

/-- For theories on acyclic graphs, local consistency implies satisfiability. -/
theorem tree_satisfiability_decidable [NeZero n]
    (T : Theory n)
    (h_acyclic : (DynamicGraph.toSimpleGraph (theory_graph T)).IsAcyclic) :
    LocallyConsistent T → Satisfiable T :=
  fun h_cons => acyclic_implies_satisfiable T h_cons h_acyclic

end Diaspora.Logic.Universal
