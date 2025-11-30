import Diaspora.Logic.Foundations

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
    -- h2 extends h1 by one step (adjacency in G from h1.curr to h2.curr)
    (∃ (hadj : (DynamicGraph.toSimpleGraph G).Adj h1.curr h2.curr),
       h2.walk = h1.walk.concat hadj) ∨
    -- h1 extends h2 by one step (symmetry)
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
  -- hcurr : a.curr = b.curr
  -- hwalk : a.walk.copy ... hcurr = b.walk
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
/-- Core lemma: if two vertices both extend to the same History by adjacency,
    and both have len = that History's len - 1, they must be equal. -/
lemma neighbors_of_local_max_eq {G : DynamicGraph n} {root : Fin n}
    {m pred succ : History G root}
    (hadj_pred : (UniversalCover G root).Adj pred m)
    (hadj_succ : (UniversalCover G root).Adj m succ)
    (hpred_len : m.len = pred.len + 1)
    (hsucc_len : m.len = succ.len + 1) : pred = succ := by
  -- pred extends to m: m.walk = pred.walk.concat e1
  obtain ⟨e1, hm_ext_pred⟩ := cover_adj_extends_walk hadj_pred hpred_len
  -- succ also extends to m: m.walk = succ.walk.concat e2
  obtain ⟨e2, hm_ext_succ⟩ := cover_adj_extends_walk hadj_succ.symm hsucc_len
  exact History.eq_of_same_extension hm_ext_pred hm_ext_succ


/-- Core lemma: at the vertex with maximum len in a cycle, we derive a contradiction.
    The max vertex has both neighbors with len = max - 1 (by ±1 and maximality).
    Those neighbors are equal (by extension argument) but at different indices (nodup). -/
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

/-! ## 4. Physical Interpretation

**The Illusion of Mass**:
Mass is not a property of the particle. It is a property of the space it lives in.
1. In the Universal Cover (God's view), the particle is just a linear history of strain. Energy = 0.
2. In the Physical Graph (Observer's view), the history wraps onto itself.
3. The mismatch between "where I am" and "what I remember" is what we call Energy.

**ZFC is the Universal Cover**:
The "Classical Vacuum" (Foundations.lean) is effectively the Universal Cover of Reality.
We model ZFC as a tree of sets. That tree is simply the "unrolled" version of the
cyclic, messy, finite web of relations that makes up the physical world.
-/

end Diaspora.Logic.Universal
