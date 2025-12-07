/-
Cycle orientation and optimal alignment.

Reversing a cycle negates its harmonic form. When two cycles share edges,
they can orient to minimize combined energy by aligning oppositely on
shared edges (anti-ferromagnetic coupling).
-/
import Diaspora.Logic.Classicality.Orthogonality.Energy

namespace Diaspora.Logic

open Diaspora.Core Diaspora.Hodge

variable {n : ℕ} [Fintype (Fin n)]

/-- The reversed cycle: same vertices in opposite order. -/
def GeneralCycle.reverse {n : ℕ} (c : GeneralCycle n) : GeneralCycle n where
  verts := c.verts.reverse
  len_ge_3 := by simp only [List.length_reverse]; exact c.len_ge_3
  nodup := List.nodup_reverse.mpr c.nodup

/-- Reversed cycle has the same length. -/
theorem GeneralCycle.reverse_len {n : ℕ} (c : GeneralCycle n) : c.reverse.len = c.len := by
  unfold GeneralCycle.len GeneralCycle.reverse
  simp only [List.length_reverse]

/-- Reversing is involutive. -/
theorem GeneralCycle.reverse_reverse {n : ℕ} (c : GeneralCycle n) : c.reverse.reverse = c := by
  simp only [GeneralCycle.reverse, List.reverse_reverse]

/-- Helper: vertex of reversed cycle in terms of original. -/
lemma GeneralCycle.reverse_vertex {n : ℕ} (c : GeneralCycle n) (k : ℕ) (hk : k < c.verts.length) :
    c.reverse.vertex k = c.vertex (c.verts.length - 1 - k) := by
  unfold GeneralCycle.vertex GeneralCycle.reverse
  simp only [List.length_reverse]
  have h_len_pos : 0 < c.verts.length := Nat.lt_of_lt_of_le (by omega : 0 < 3) c.len_ge_3
  have h_idx : c.verts.length - 1 - k < c.verts.length := by omega
  have h_mod_k : k % c.verts.length = k := Nat.mod_eq_of_lt hk
  have h_mod_rev : (c.verts.length - 1 - k) % c.verts.length = c.verts.length - 1 - k :=
    Nat.mod_eq_of_lt h_idx
  simp only [h_mod_k, h_mod_rev]
  rw [List.get_reverse']

/-- Helper: vertex of reversed cycle for general k (uses mod internally). -/
lemma GeneralCycle.reverse_vertex_mod {n : ℕ} (c : GeneralCycle n) (k : ℕ) :
    c.reverse.vertex k = c.vertex (c.verts.length - 1 - k % c.verts.length) := by
  have h_len_pos : 0 < c.verts.length := Nat.lt_of_lt_of_le (by omega : 0 < 3) c.len_ge_3
  have hk_mod_lt : k % c.verts.length < c.verts.length := Nat.mod_lt k h_len_pos
  have h_idx : c.verts.length - 1 - k % c.verts.length < c.verts.length := by omega
  unfold GeneralCycle.vertex GeneralCycle.reverse
  simp only [List.length_reverse]
  have h_mod_mod : k % c.verts.length % c.verts.length = k % c.verts.length :=
    Nat.mod_eq_of_lt hk_mod_lt
  have h_idx_mod : (c.verts.length - 1 - k % c.verts.length) % c.verts.length =
      c.verts.length - 1 - k % c.verts.length := Nat.mod_eq_of_lt h_idx
  simp only [h_idx_mod]
  rw [List.get_reverse']

/-- Helper: nextVertex of reversed cycle for general k.
    c.reverse.nextVertex k = c.reverse.vertex (k + 1) = c.vertex (len - 1 - (k + 1) % len) -/
lemma GeneralCycle.reverse_nextVertex_eq {n : ℕ} (c : GeneralCycle n) (k : ℕ) :
    c.reverse.nextVertex k = c.vertex (c.verts.length - 1 - (k + 1) % c.verts.length) := by
  unfold GeneralCycle.nextVertex
  rw [c.reverse_vertex_mod]

/-- Key lemma: forward edge of c.reverse corresponds to backward edge of c.
    Specifically: (i, j) is forward in c.reverse ↔ (j, i) is forward in c. -/
lemma reverse_edge_iff {n : ℕ} (c : GeneralCycle n) (i j : Fin n) :
    (∃ k : Fin c.reverse.verts.length, c.reverse.vertex k.val = i ∧ c.reverse.nextVertex k.val = j) ↔
    (∃ k : Fin c.verts.length, c.vertex k.val = j ∧ c.nextVertex k.val = i) := by
  have h_len_eq : c.reverse.verts.length = c.verts.length := List.length_reverse
  have h_len_pos : 0 < c.verts.length := Nat.lt_of_lt_of_le (by omega : 0 < 3) c.len_ge_3
  have h_len_ge_3 := c.len_ge_3
  constructor
  · intro ⟨k, hk_v, hk_n⟩
    have hk_lt : k.val < c.verts.length := by rw [← h_len_eq]; exact k.isLt
    -- c.reverse.vertex k = c.vertex (len - 1 - k)
    rw [c.reverse_vertex k.val hk_lt] at hk_v
    -- c.reverse.nextVertex k = c.reverse.vertex (k + 1) = c.vertex (len - 1 - (k+1) % len)
    unfold GeneralCycle.nextVertex at hk_n
    rw [c.reverse_vertex_mod] at hk_n
    -- Now we need to find m in c such that c.vertex m = j and c.nextVertex m = i
    -- From hk_v: c.vertex (len - 1 - k) = i
    -- From hk_n: c.vertex (len - 1 - (k+1) % len) = j
    -- We need m with c.vertex m = j and c.vertex (m+1) = i
    -- Case split on whether k + 1 < len
    by_cases h_k_small : k.val + 1 < c.verts.length
    · -- k + 1 < len, so (k+1) % len = k + 1
      have h_mod_eq : (k.val + 1) % c.verts.length = k.val + 1 := Nat.mod_eq_of_lt h_k_small
      rw [h_mod_eq] at hk_n
      -- hk_n: c.vertex (len - 1 - (k + 1)) = j, i.e., c.vertex (len - 2 - k) = j
      -- Let m = len - 2 - k
      let m := c.verts.length - 2 - k.val
      have hm_lt : m < c.verts.length := by show c.verts.length - 2 - k.val < c.verts.length; omega
      use ⟨m, hm_lt⟩
      constructor
      · -- c.vertex m = j
        rw [← hk_n, ← show m = c.verts.length - 1 - (k.val + 1) from by omega]
      · -- c.nextVertex m = i
        rw [← hk_v, ← show m + 1 = c.verts.length - 1 - k.val from by omega]
        rfl
    · -- k + 1 ≥ len, which means k = len - 1 (since k < len)
      have h_k_eq : k.val = c.verts.length - 1 := by omega
      have h_mod_eq : (k.val + 1) % c.verts.length = 0 := by
        rw [h_k_eq]
        have : c.verts.length - 1 + 1 = c.verts.length := by omega
        rw [this, Nat.mod_self]
      rw [h_mod_eq] at hk_n
      -- hk_n: c.vertex (len - 1 - 0) = j, i.e., c.vertex (len - 1) = j
      simp only [Nat.sub_zero] at hk_n
      -- hk_v: c.vertex (len - 1 - k) = c.vertex 0 = i
      rw [h_k_eq] at hk_v
      simp only [Nat.sub_self] at hk_v
      -- Let m = len - 1
      let m := c.verts.length - 1
      have hm_lt : m < c.verts.length := by omega
      use ⟨m, hm_lt⟩
      constructor
      · -- c.vertex (len - 1) = j
        exact hk_n
      · -- c.nextVertex (len - 1) = c.vertex len = c.vertex 0 = i
        -- m + 1 = len, so (m + 1) % len = 0
        have hm1_mod : (m + 1) % c.verts.length = 0 := by
          show (c.verts.length - 1 + 1) % c.verts.length = 0
          have : c.verts.length - 1 + 1 = c.verts.length := by omega
          rw [this, Nat.mod_self]
        unfold GeneralCycle.nextVertex GeneralCycle.vertex
        simp only [hm1_mod]
        exact hk_v
  · intro ⟨k, hk_v, hk_n⟩
    -- k is in c with c.vertex k = j and c.nextVertex k = i
    -- Need to find k' in c.reverse with c.reverse.vertex k' = i and c.reverse.nextVertex k' = j
    have hk_lt : k.val < c.verts.length := k.isLt
    -- The formula: k' = len - 2 - k when k < len - 1, and k' = len - 1 when k = len - 1
    by_cases h_k_last : k.val = c.verts.length - 1
    · -- k = len - 1: the wrap-around edge (v_{len-1}, v_0)
      -- In c.reverse, this corresponds to edge (v_0, v_{len-1}) at position len - 1
      let k' := c.verts.length - 1
      have hk'_lt : k' < c.reverse.verts.length := by
        show c.verts.length - 1 < c.reverse.verts.length
        rw [h_len_eq]; omega
      use ⟨k', hk'_lt⟩
      constructor
      · -- c.reverse.vertex (len-1) = c.vertex (len-1-(len-1)) = c.vertex 0
        rw [c.reverse_vertex k' (by omega : k' < c.verts.length)]
        unfold GeneralCycle.nextVertex at hk_n
        rw [h_k_last] at hk_n
        -- hk_n: c.vertex len = c.vertex 0 = i (mod arithmetic)
        unfold GeneralCycle.vertex at hk_n ⊢
        -- Goal: c.verts.get ⟨(len - 1 - k') % len, _⟩ = i
        -- k' = len - 1, so len - 1 - k' = 0
        -- hk_n: c.verts.get ⟨len % len, _⟩ = i, i.e., c.verts.get ⟨0, _⟩ = i
        have h1 : (c.verts.length - 1 - k') % c.verts.length = 0 := by
          show (c.verts.length - 1 - (c.verts.length - 1)) % c.verts.length = 0
          simp only [Nat.sub_self, Nat.zero_mod]
        have h2 : (c.verts.length - 1 + 1) % c.verts.length = 0 := by
          have : c.verts.length - 1 + 1 = c.verts.length := by omega
          rw [this, Nat.mod_self]
        simp only [h1, h2] at hk_n ⊢
        exact hk_n
      · -- c.reverse.nextVertex (len-1) = c.reverse.vertex 0 = c.vertex (len-1) = j
        unfold GeneralCycle.nextVertex
        rw [c.reverse_vertex_mod]
        rw [h_k_last] at hk_v
        -- Goal: c.vertex (len - 1 - (k' + 1) % len) = j where k' = len - 1
        -- (k' + 1) % len = len % len = 0
        -- So: c.vertex (len - 1 - 0) = c.vertex (len - 1) = j
        have h_mod_0 : (k' + 1) % c.verts.length = 0 := by
          show (c.verts.length - 1 + 1) % c.verts.length = 0
          have : c.verts.length - 1 + 1 = c.verts.length := by omega
          rw [this, Nat.mod_self]
        simp only [h_mod_0, Nat.sub_zero]
        -- Now goal is c.vertex (len - 1) = j, which is hk_v
        exact hk_v
    · -- k < len - 1: use k' = len - 2 - k
      have hk_small : k.val < c.verts.length - 1 := by omega
      let k' := c.verts.length - 2 - k.val
      have hk'_lt : k' < c.reverse.verts.length := by
        show c.verts.length - 2 - k.val < c.reverse.verts.length
        rw [h_len_eq]; omega
      use ⟨k', hk'_lt⟩
      constructor
      · -- c.reverse.vertex k' = c.vertex (len-1-k') = c.vertex (k+1) = i
        rw [c.reverse_vertex k' (by show c.verts.length - 2 - k.val < c.verts.length; omega)]
        unfold GeneralCycle.nextVertex at hk_n
        -- Goal: c.vertex (len - 1 - k') = i where k' = len - 2 - k
        -- len - 1 - k' = len - 1 - (len - 2 - k) = k + 1
        have h_idx : c.verts.length - 1 - k' = k.val + 1 := by
          show c.verts.length - 1 - (c.verts.length - 2 - k.val) = k.val + 1; omega
        rw [h_idx]; exact hk_n
      · -- c.reverse.nextVertex k' = c.reverse.vertex (k'+1) = c.vertex (len-1-(k'+1)) = c.vertex k = j
        unfold GeneralCycle.nextVertex
        rw [c.reverse_vertex_mod]
        -- Goal: c.vertex (len - 1 - (k' + 1) % len) = j where k' = len - 2 - k
        -- k' + 1 = len - 1 - k, which is < len, so (k' + 1) % len = k' + 1
        -- len - 1 - (k' + 1) = len - 1 - (len - 1 - k) = k
        have h_k'_plus_1_lt : k' + 1 < c.verts.length := by
          show c.verts.length - 2 - k.val + 1 < c.verts.length; omega
        have h_mod : (k' + 1) % c.verts.length = k' + 1 := Nat.mod_eq_of_lt h_k'_plus_1_lt
        rw [h_mod]
        have h_idx : c.verts.length - 1 - (k' + 1) = k.val := by
          show c.verts.length - 1 - (c.verts.length - 2 - k.val + 1) = k.val; omega
        rw [h_idx]; exact hk_v

/-- Reversing a cycle negates its harmonic form.
    Forward edges of c.reverse are backward edges of c, so the form negates. -/
theorem reverse_negates_form {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c : GeneralCycle n) :
    ∀ i j : Fin n, (general_cycle_form c.reverse).val i j = -(general_cycle_form c).val i j := by
  intro i j
  unfold general_cycle_form
  simp only
  -- The key equivalences from reverse_edge_iff:
  -- (i,j) forward in c.reverse ↔ (j,i) forward in c
  -- (j,i) forward in c.reverse ↔ (i,j) forward in c
  have h_fwd : (∃ k : Fin c.reverse.verts.length, c.reverse.vertex k.val = i ∧ c.reverse.nextVertex k.val = j) ↔
               (∃ k : Fin c.verts.length, c.vertex k.val = j ∧ c.nextVertex k.val = i) := reverse_edge_iff c i j
  have h_bwd : (∃ k : Fin c.reverse.verts.length, c.reverse.vertex k.val = j ∧ c.reverse.nextVertex k.val = i) ↔
               (∃ k : Fin c.verts.length, c.vertex k.val = i ∧ c.nextVertex k.val = j) := reverse_edge_iff c j i
  -- Case analysis on the four conditions
  by_cases h_ij_rev : ∃ k : Fin c.reverse.verts.length, c.reverse.vertex k.val = i ∧ c.reverse.nextVertex k.val = j
  · -- (i,j) is forward in c.reverse, so (j,i) is forward in c
    simp only [h_ij_rev, ↓reduceIte]
    have h_ji_orig : ∃ k : Fin c.verts.length, c.vertex k.val = j ∧ c.nextVertex k.val = i := h_fwd.mp h_ij_rev
    -- Now we need to check if (j,i) is forward in c.reverse (i.e., if (i,j) is forward in c)
    by_cases h_ji_rev : ∃ k : Fin c.reverse.verts.length, c.reverse.vertex k.val = j ∧ c.reverse.nextVertex k.val = i
    · -- Both (i,j) and (j,i) are forward in c.reverse
      -- This means both (j,i) and (i,j) are forward in c - impossible for len ≥ 3
      have h_ij_orig : ∃ k : Fin c.verts.length, c.vertex k.val = i ∧ c.nextVertex k.val = j := h_bwd.mp h_ji_rev
      -- Contradiction: i→j and j→i are both forward edges
      exfalso
      obtain ⟨k1, hk1_v, hk1_n⟩ := h_ij_orig
      obtain ⟨k2, hk2_v, hk2_n⟩ := h_ji_orig
      -- k1: i → j, k2: j → i
      -- So vertex k1 = i = nextVertex k2, and vertex k2 = j = nextVertex k1
      -- This means k1 and k2 are "adjacent" and cycle back in 2 steps
      have h_len_ge_3 := c.len_ge_3
      have h_nodup := c.nodup
      have h_len_pos : 0 < c.verts.length := Nat.lt_of_lt_of_le (by omega : 0 < 3) h_len_ge_3
      -- From nodup: equal vertices means equal indices
      have hk1n_lt : (k1.val + 1) % c.verts.length < c.verts.length := Nat.mod_lt _ h_len_pos
      have hk2n_lt : (k2.val + 1) % c.verts.length < c.verts.length := Nat.mod_lt _ h_len_pos
      -- Unfold vertex in all hypotheses
      unfold GeneralCycle.nextVertex GeneralCycle.vertex at hk1_n hk2_n hk1_v hk2_v
      -- Now: hk1_n : c.verts.get ⟨(k1+1) % len, _⟩ = j
      --      hk2_v : c.verts.get ⟨k2 % len, _⟩ = j
      -- Since k2 < len, k2 % len = k2
      have hk2_mod : k2.val % c.verts.length = k2.val := Nat.mod_eq_of_lt k2.isLt
      have hk1_mod : k1.val % c.verts.length = k1.val := Nat.mod_eq_of_lt k1.isLt
      -- So: c.verts.get at (k1+1) % len = c.verts.get at k2
      have h1 : c.verts.get ⟨(k1.val + 1) % c.verts.length, hk1n_lt⟩ = c.verts.get k2 := by
        have heq1 : c.verts.get ⟨(k1.val + 1) % c.verts.length, hk1n_lt⟩ = j := hk1_n
        have heq2 : c.verts.get k2 = j := by
          have : c.verts.get k2 = c.verts.get ⟨k2.val % c.verts.length, Nat.mod_lt _ h_len_pos⟩ := by
            congr 1; simp only [hk2_mod]
          rw [this]; exact hk2_v
        rw [heq1, heq2]
      have hk1_next_eq_k2 : (k1.val + 1) % c.verts.length = k2.val := by
        have h_inj := h_nodup.get_inj_iff (i := ⟨(k1.val + 1) % c.verts.length, hk1n_lt⟩) (j := k2)
        have hfin := h_inj.mp h1
        exact congrArg Fin.val hfin
      -- Similarly for the other direction
      have h2 : c.verts.get ⟨(k2.val + 1) % c.verts.length, hk2n_lt⟩ = c.verts.get k1 := by
        have heq1 : c.verts.get ⟨(k2.val + 1) % c.verts.length, hk2n_lt⟩ = i := hk2_n
        have heq2 : c.verts.get k1 = i := by
          have : c.verts.get k1 = c.verts.get ⟨k1.val % c.verts.length, Nat.mod_lt _ h_len_pos⟩ := by
            congr 1; simp only [hk1_mod]
          rw [this]; exact hk1_v
        rw [heq1, heq2]
      have hk2_next_eq_k1 : (k2.val + 1) % c.verts.length = k1.val := by
        have h_inj := h_nodup.get_inj_iff (i := ⟨(k2.val + 1) % c.verts.length, hk2n_lt⟩) (j := k1)
        have hfin := h_inj.mp h2
        exact congrArg Fin.val hfin
      -- Now: (k1 + 1) % len = k2 and (k2 + 1) % len = k1
      -- So (k1 + 2) % len = ((k1 + 1) % len + 1) % len = (k2 + 1) % len = k1
      have hk1_lt : k1.val < c.verts.length := k1.isLt
      have h_1_lt_len : 1 < c.verts.length := by omega
      have h_1_mod : 1 % c.verts.length = 1 := Nat.mod_eq_of_lt h_1_lt_len
      have h_cycle : (k1.val + 2) % c.verts.length = k1.val := by
        calc (k1.val + 2) % c.verts.length
            = (k1.val + 1 + 1) % c.verts.length := by ring_nf
          _ = (((k1.val + 1) % c.verts.length) + (1 % c.verts.length)) % c.verts.length := by
              rw [Nat.add_mod]
          _ = ((k1.val + 1) % c.verts.length + 1) % c.verts.length := by rw [h_1_mod]
          _ = (k2.val + 1) % c.verts.length := by rw [hk1_next_eq_k2]
          _ = k1.val := hk2_next_eq_k1
      -- From h_cycle: (k1 + 2) % len = k1, with k1 < len
      -- If k1 + 2 < len, then k1 + 2 = k1, impossible
      -- If k1 + 2 ≥ len, then k1 + 2 - len = k1 (since k1 + 2 < 2*len), so len = 2
      -- But len ≥ 3, contradiction
      have hk1_2_lt_2len : k1.val + 2 < 2 * c.verts.length := by omega
      by_cases h : k1.val + 2 < c.verts.length
      · -- k1 + 2 < len, so (k1 + 2) % len = k1 + 2 = k1, impossible
        have := Nat.mod_eq_of_lt h
        omega
      · -- k1 + 2 ≥ len, so (k1 + 2) % len = k1 + 2 - len
        push_neg at h
        have h_mod : (k1.val + 2) % c.verts.length = k1.val + 2 - c.verts.length := by
          rw [Nat.mod_eq_sub_mod h]
          have : k1.val + 2 - c.verts.length < c.verts.length := by omega
          exact Nat.mod_eq_of_lt this
        rw [h_mod] at h_cycle
        -- k1 + 2 - len = k1, so len = 2
        have : c.verts.length = 2 := by omega
        omega
    · -- (i,j) forward in c.reverse, (j,i) not forward in c.reverse
      -- (j,i) forward in c, (i,j) not forward in c
      -- So γ(i,j) = -1/len (it's backward), and γ_rev(i,j) = 1/len
      -- Need: 1/len = -(-1/len) ✓
      have h_ij_not_orig : ¬∃ k : Fin c.verts.length, c.vertex k.val = i ∧ c.nextVertex k.val = j := by
        intro h; exact h_ji_rev (h_bwd.mpr h)
      simp only [h_ij_not_orig, ↓reduceIte, h_ji_orig, c.reverse_len]
      ring
  · -- (i,j) is NOT forward in c.reverse
    -- So (j,i) is NOT forward in c
    have h_ji_not_orig : ¬∃ k : Fin c.verts.length, c.vertex k.val = j ∧ c.nextVertex k.val = i := by
      intro h; exact h_ij_rev (h_fwd.mpr h)
    by_cases h_ji_rev : ∃ k : Fin c.reverse.verts.length, c.reverse.vertex k.val = j ∧ c.reverse.nextVertex k.val = i
    · -- (j,i) is forward in c.reverse, so (i,j) is forward in c
      have h_ij_orig : ∃ k : Fin c.verts.length, c.vertex k.val = i ∧ c.nextVertex k.val = j := h_bwd.mp h_ji_rev
      -- Goal has ite about c.reverse, use h_ij_rev (¬forward) and h_ji_rev (backward)
      simp only [h_ij_rev, h_ji_rev, ↓reduceIte, c.reverse_len]
      -- Now RHS: need to show -(1/len) = -(1/len) using h_ij_orig, h_ji_not_orig
      simp only [h_ij_orig, ↓reduceIte]
    · -- Neither direction is forward in c.reverse
      -- So neither direction is forward in c
      have h_ij_not_orig : ¬∃ k : Fin c.verts.length, c.vertex k.val = i ∧ c.nextVertex k.val = j := by
        intro h; exact h_ji_rev (h_bwd.mpr h)
      simp only [h_ij_rev, h_ji_rev, ↓reduceIte, h_ij_not_orig, h_ji_not_orig]
      ring

/-- Same-direction edges with c₂.reverse = opposite-direction edges with c₂.
    Key insight: forward (i,j) in c.reverse ↔ forward (j,i) in c -/
lemma sameDirectionEdges_reverse {n : ℕ} [DecidableEq (Fin n)] (c₁ c₂ : GeneralCycle n) :
    c₁.sameDirectionEdges c₂.reverse = c₁.oppositeDirectionEdges c₂ := by
  simp only [GeneralCycle.sameDirectionEdges, GeneralCycle.oppositeDirectionEdges]
  have h_len_eq : c₂.reverse.verts.length = c₂.verts.length := List.length_reverse
  have h_len_pos : 0 < c₂.verts.length := Nat.lt_of_lt_of_le (by omega : 0 < 3) c₂.len_ge_3
  have h_len_ge_3 := c₂.len_ge_3
  -- The bijection is k₂' = len - 1 - (k₂ + 1) % len, which is an involution
  -- This correctly maps k₂ = len-1 to len-1 (since (len)%len = 0)
  have h_fin_cast : ∀ k : Fin c₂.reverse.verts.length, k.val < c₂.verts.length := fun k => by
    rw [← h_len_eq]; exact k.isLt
  let bij : Fin c₂.reverse.verts.length → Fin c₂.verts.length := fun k =>
    ⟨c₂.verts.length - 1 - (k.val + 1) % c₂.verts.length, by
      have h := Nat.mod_lt (k.val + 1) h_len_pos
      omega⟩
  -- The inverse uses the same formula
  have bij_inv : ∀ k : Fin c₂.verts.length,
      (bij ⟨c₂.verts.length - 1 - (k.val + 1) % c₂.verts.length,
           by rw [h_len_eq]; have h := Nat.mod_lt (k.val + 1) h_len_pos; omega⟩).val = k.val := by
    intro k
    simp only [bij]
    have hk_lt : k.val < c₂.verts.length := k.isLt
    -- Need: len - 1 - ((len - 1 - (k+1)%len) + 1) % len = k
    have h_mod_bound : (k.val + 1) % c₂.verts.length ≤ c₂.verts.length - 1 := by
      have h := Nat.mod_lt (k.val + 1) h_len_pos; omega
    have h_bij_val : c₂.verts.length - 1 - (k.val + 1) % c₂.verts.length + 1 =
        c₂.verts.length - (k.val + 1) % c₂.verts.length := by omega
    rw [h_bij_val]
    by_cases hk_last : k.val = c₂.verts.length - 1
    · -- k = len - 1: (k+1)%len = 0, so bij k = len - 1
      have hk1 : (k.val + 1) % c₂.verts.length = 0 := by
        rw [hk_last, Nat.sub_add_cancel (by omega : 1 ≤ c₂.verts.length)]
        exact Nat.mod_self _
      -- Simplify: len - 1 - (len - (k+1)%len) % len = len - 1 - (len - 0) % len = len - 1 - 0 = len - 1
      rw [hk1, Nat.sub_zero, Nat.mod_self, Nat.sub_zero, hk_last]
    · -- k < len - 1: (k+1)%len = k+1
      have hk_lt' : k.val < c₂.verts.length - 1 := by
        cases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (by omega : k.val < c₂.verts.length - 1 + 1)) with
        | inl h => exact h
        | inr h => exact absurd h hk_last
      have hk1 : (k.val + 1) % c₂.verts.length = k.val + 1 := Nat.mod_eq_of_lt (by omega)
      rw [hk1]
      have h_inner : c₂.verts.length - (k.val + 1) < c₂.verts.length := by omega
      rw [Nat.mod_eq_of_lt h_inner]
      omega
  -- Now prove the cardinality equality by establishing a bijection
  apply Finset.card_bij (fun (p : Fin c₁.verts.length × Fin c₂.reverse.verts.length) _ =>
      (p.1, bij p.2))
  · -- Maps into target set
    intro ⟨k₁, k₂⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨h_v, h_n⟩ := hp
    have hk2_lt : k₂.val < c₂.verts.length := h_fin_cast k₂
    -- c₂.reverse.vertex k₂ = c₂.vertex (len - 1 - k₂ % len)
    have h_rev_v : c₂.reverse.vertex k₂.val = c₂.vertex (c₂.verts.length - 1 - k₂.val) := by
      rw [c₂.reverse_vertex_mod, Nat.mod_eq_of_lt hk2_lt]
    -- c₂.reverse.nextVertex k₂ = c₂.vertex (len - 1 - (k₂+1) % len)
    have h_rev_n : c₂.reverse.nextVertex k₂.val =
        c₂.vertex (c₂.verts.length - 1 - (k₂.val + 1) % c₂.verts.length) := c₂.reverse_nextVertex_eq k₂.val
    rw [h_rev_v] at h_v
    rw [h_rev_n] at h_n
    -- bij k₂ = len - 1 - (k₂ + 1) % len
    -- Target: c₁.vertex k₁ = c₂.nextVertex (bij k₂) and c₁.nextVertex k₁ = c₂.vertex (bij k₂)
    simp only [bij]
    -- c₂.nextVertex (len - 1 - (k₂+1)%len) = c₂.vertex ((len - 1 - (k₂+1)%len + 1) % len)
    --                                      = c₂.vertex ((len - (k₂+1)%len) % len)
    -- c₂.vertex (bij k₂) = c₂.vertex (len - 1 - (k₂+1)%len)
    have h_mod_bound : (k₂.val + 1) % c₂.verts.length ≤ c₂.verts.length - 1 := by
      have h := Nat.mod_lt (k₂.val + 1) h_len_pos; omega
    have h_bij_add : c₂.verts.length - 1 - (k₂.val + 1) % c₂.verts.length + 1 =
        c₂.verts.length - (k₂.val + 1) % c₂.verts.length := by omega
    have h_next : c₂.nextVertex (c₂.verts.length - 1 - (k₂.val + 1) % c₂.verts.length) =
        c₂.vertex (c₂.verts.length - 1 - k₂.val) := by
      -- nextVertex x = vertex (x + 1), and vertex a = vertex b when a % len = b % len
      unfold GeneralCycle.nextVertex GeneralCycle.vertex
      congr 1
      ext
      -- Goal: ((len - 1 - (k₂+1)%len) + 1) % len = (len - 1 - k₂) % len
      by_cases hk2_last : k₂.val = c₂.verts.length - 1
      · -- k₂ = len - 1: (k₂+1)%len = 0
        have hk1 : (k₂.val + 1) % c₂.verts.length = 0 := by
          rw [hk2_last, Nat.sub_add_cancel (by omega : 1 ≤ c₂.verts.length)]
          exact Nat.mod_self _
        rw [hk1, hk2_last]
        simp only [Nat.sub_zero, Nat.sub_self, Nat.zero_mod, Nat.sub_add_cancel (by omega : 1 ≤ c₂.verts.length)]
        exact Nat.mod_self _
      · -- k₂ < len - 1: (k₂+1)%len = k₂+1
        have hk2_lt' : k₂.val < c₂.verts.length - 1 := by omega
        have hk1 : (k₂.val + 1) % c₂.verts.length = k₂.val + 1 := Nat.mod_eq_of_lt (by omega)
        rw [hk1]
        have h_eq : c₂.verts.length - 1 - (k₂.val + 1) + 1 = c₂.verts.length - 1 - k₂.val := by omega
        rw [h_eq]
    constructor
    · rw [h_next, ← h_v]
    · rw [← h_n]
  · -- Injective
    intro ⟨k₁, k₂⟩ _ ⟨k₁', k₂'⟩ _ heq
    simp only [Prod.mk.injEq] at heq ⊢
    obtain ⟨hk1_eq, hk2_eq⟩ := heq
    constructor
    · exact hk1_eq
    · ext
      simp only [bij, Fin.mk.injEq] at hk2_eq
      have hk2_lt : k₂.val < c₂.verts.length := h_fin_cast k₂
      have hk2'_lt : k₂'.val < c₂.verts.length := h_fin_cast k₂'
      have h_mod_bound : (k₂.val + 1) % c₂.verts.length ≤ c₂.verts.length - 1 := by
        have h := Nat.mod_lt (k₂.val + 1) h_len_pos; omega
      have h_mod_bound' : (k₂'.val + 1) % c₂.verts.length ≤ c₂.verts.length - 1 := by
        have h := Nat.mod_lt (k₂'.val + 1) h_len_pos; omega
      -- From hk2_eq: len - 1 - (k₂+1)%len = len - 1 - (k₂'+1)%len
      -- So (k₂+1)%len = (k₂'+1)%len
      have h_mod_eq : (k₂.val + 1) % c₂.verts.length = (k₂'.val + 1) % c₂.verts.length := by omega
      -- Since both k₂, k₂' < len, and len ≥ 3:
      -- If k₂ < len - 1: (k₂+1)%len = k₂+1
      -- If k₂ = len - 1: (k₂+1)%len = 0
      by_cases hk2_last : k₂.val = c₂.verts.length - 1
      · by_cases hk2'_last : k₂'.val = c₂.verts.length - 1
        · omega
        · have hk1 : (k₂.val + 1) % c₂.verts.length = 0 := by
            rw [hk2_last, Nat.sub_add_cancel (by omega : 1 ≤ c₂.verts.length)]
            exact Nat.mod_self _
          have hk1' : (k₂'.val + 1) % c₂.verts.length = k₂'.val + 1 := by
            apply Nat.mod_eq_of_lt
            have : k₂'.val < c₂.verts.length - 1 := by
              cases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (by omega : k₂'.val < c₂.verts.length - 1 + 1)) with
              | inl h => exact h
              | inr h => exact absurd h hk2'_last
            omega
          rw [hk1, hk1'] at h_mod_eq
          omega
      · by_cases hk2'_last : k₂'.val = c₂.verts.length - 1
        · have hk1 : (k₂.val + 1) % c₂.verts.length = k₂.val + 1 := by
            apply Nat.mod_eq_of_lt
            have : k₂.val < c₂.verts.length - 1 := by
              cases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (by omega : k₂.val < c₂.verts.length - 1 + 1)) with
              | inl h => exact h
              | inr h => exact absurd h hk2_last
            omega
          have hk1' : (k₂'.val + 1) % c₂.verts.length = 0 := by
            rw [hk2'_last, Nat.sub_add_cancel (by omega : 1 ≤ c₂.verts.length)]
            exact Nat.mod_self _
          rw [hk1, hk1'] at h_mod_eq
          omega
        · have hk1 : (k₂.val + 1) % c₂.verts.length = k₂.val + 1 := by
            apply Nat.mod_eq_of_lt
            have : k₂.val < c₂.verts.length - 1 := by
              cases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (by omega : k₂.val < c₂.verts.length - 1 + 1)) with
              | inl h => exact h
              | inr h => exact absurd h hk2_last
            omega
          have hk1' : (k₂'.val + 1) % c₂.verts.length = k₂'.val + 1 := by
            apply Nat.mod_eq_of_lt
            have : k₂'.val < c₂.verts.length - 1 := by
              cases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (by omega : k₂'.val < c₂.verts.length - 1 + 1)) with
              | inl h => exact h
              | inr h => exact absurd h hk2'_last
            omega
          rw [hk1, hk1'] at h_mod_eq
          omega
  · -- Surjective
    intro ⟨k₁, k₂⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨h_v, h_n⟩ := hp
    have hk2_lt : k₂.val < c₂.verts.length := k₂.isLt
    have h_mod_bound : (k₂.val + 1) % c₂.verts.length ≤ c₂.verts.length - 1 := by
      have h := Nat.mod_lt (k₂.val + 1) h_len_pos; omega
    -- Preimage: k₂' = len - 1 - (k₂ + 1) % len (same formula, it's an involution)
    let k₂'_val := c₂.verts.length - 1 - (k₂.val + 1) % c₂.verts.length
    have hk2'_lt : k₂'_val < c₂.reverse.verts.length := by
      rw [h_len_eq]
      simp only [k₂'_val]
      omega
    use (k₁, ⟨k₂'_val, hk2'_lt⟩)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
    constructor
    · -- Show bij k₂' = k₂ (first goal after constructor)
      ext
      simp only [bij]
      exact bij_inv k₂
    · -- Show (k₁, k₂') is in source set (second goal after constructor)
      have h_k2'_val : k₂'_val = c₂.verts.length - 1 - (k₂.val + 1) % c₂.verts.length := rfl
      -- c₂.reverse.vertex k₂' = c₂.vertex (len - 1 - k₂')
      have hk2'_lt_orig : k₂'_val < c₂.verts.length := by rw [← h_len_eq]; exact hk2'_lt
      have h_rev_v : c₂.reverse.vertex k₂'_val = c₂.vertex (c₂.verts.length - 1 - k₂'_val) := by
        rw [c₂.reverse_vertex_mod, Nat.mod_eq_of_lt hk2'_lt_orig]
      -- c₂.reverse.nextVertex k₂' = c₂.vertex (len - 1 - (k₂' + 1) % len)
      have h_rev_n : c₂.reverse.nextVertex k₂'_val =
          c₂.vertex (c₂.verts.length - 1 - (k₂'_val + 1) % c₂.verts.length) :=
        c₂.reverse_nextVertex_eq k₂'_val
      -- Compute len - 1 - k₂' = len - 1 - (len - 1 - (k₂+1)%len) = (k₂+1)%len
      have h_comp1 : c₂.verts.length - 1 - k₂'_val = (k₂.val + 1) % c₂.verts.length := by
        simp only [k₂'_val]; omega
      -- c₂.vertex ((k₂+1)%len) = c₂.nextVertex k₂
      -- Since vertex takes mod internally, vertex ((k+1) % len) = vertex (k+1) = nextVertex k
      have h_next_eq : c₂.vertex ((k₂.val + 1) % c₂.verts.length) = c₂.nextVertex k₂.val := by
        unfold GeneralCycle.nextVertex GeneralCycle.vertex
        congr 1
        ext
        simp only [Nat.mod_mod]
      rw [h_comp1, h_next_eq] at h_rev_v
      -- Compute len - 1 - (k₂' + 1) % len
      have h_k2'_add : k₂'_val + 1 = c₂.verts.length - (k₂.val + 1) % c₂.verts.length := by
        simp only [k₂'_val]; omega
      have h_comp2 : c₂.verts.length - 1 - (k₂'_val + 1) % c₂.verts.length = k₂.val := by
        rw [h_k2'_add]
        by_cases hk2_last : k₂.val = c₂.verts.length - 1
        · have hk1 : (k₂.val + 1) % c₂.verts.length = 0 := by
            rw [hk2_last, Nat.sub_add_cancel (by omega : 1 ≤ c₂.verts.length)]
            exact Nat.mod_self _
          rw [hk1, Nat.sub_zero, Nat.mod_self, Nat.sub_zero, hk2_last]
        · have hk2_lt' : k₂.val < c₂.verts.length - 1 := by
            cases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (by omega : k₂.val < c₂.verts.length - 1 + 1)) with
            | inl h => exact h
            | inr h => exact absurd h hk2_last
          have hk1 : (k₂.val + 1) % c₂.verts.length = k₂.val + 1 := Nat.mod_eq_of_lt (by omega)
          rw [hk1]
          have h_inner : c₂.verts.length - (k₂.val + 1) < c₂.verts.length := by omega
          rw [Nat.mod_eq_of_lt h_inner]
          omega
      rw [h_comp2] at h_rev_n
      constructor
      · rw [h_rev_v, h_v]
      · rw [h_rev_n, h_n]

/-- Opposite-direction edges with c₂.reverse = same-direction edges with c₂. -/
lemma oppositeDirectionEdges_reverse {n : ℕ} [DecidableEq (Fin n)] (c₁ c₂ : GeneralCycle n) :
    c₁.oppositeDirectionEdges c₂.reverse = c₁.sameDirectionEdges c₂ := by
  simp only [GeneralCycle.oppositeDirectionEdges, GeneralCycle.sameDirectionEdges]
  have h_len_eq : c₂.reverse.verts.length = c₂.verts.length := List.length_reverse
  have h_len_pos : 0 < c₂.verts.length := Nat.lt_of_lt_of_le (by omega : 0 < 3) c₂.len_ge_3
  have h_len_ge_3 := c₂.len_ge_3
  have h_fin_cast : ∀ k : Fin c₂.reverse.verts.length, k.val < c₂.verts.length := fun k => by
    rw [← h_len_eq]; exact k.isLt
  -- Same bijection as sameDirectionEdges_reverse
  let bij : Fin c₂.reverse.verts.length → Fin c₂.verts.length := fun k =>
    ⟨c₂.verts.length - 1 - (k.val + 1) % c₂.verts.length, by
      have h := Nat.mod_lt (k.val + 1) h_len_pos
      omega⟩
  have bij_inv : ∀ k : Fin c₂.verts.length,
      (bij ⟨c₂.verts.length - 1 - (k.val + 1) % c₂.verts.length,
           by rw [h_len_eq]; have h := Nat.mod_lt (k.val + 1) h_len_pos; omega⟩).val = k.val := by
    intro k
    simp only [bij]
    have hk_lt : k.val < c₂.verts.length := k.isLt
    have h_mod_bound : (k.val + 1) % c₂.verts.length ≤ c₂.verts.length - 1 := by
      have h := Nat.mod_lt (k.val + 1) h_len_pos; omega
    have h_bij_val : c₂.verts.length - 1 - (k.val + 1) % c₂.verts.length + 1 =
        c₂.verts.length - (k.val + 1) % c₂.verts.length := by omega
    rw [h_bij_val]
    by_cases hk_last : k.val = c₂.verts.length - 1
    · have hk1 : (k.val + 1) % c₂.verts.length = 0 := by
        rw [hk_last, Nat.sub_add_cancel (by omega : 1 ≤ c₂.verts.length)]
        exact Nat.mod_self _
      simp only [hk1, Nat.sub_zero]
      have h_mod : c₂.verts.length % c₂.verts.length = 0 := Nat.mod_self _
      simp only [h_mod, Nat.sub_zero, hk_last]
    · have hk_lt' : k.val < c₂.verts.length - 1 := by omega
      have hk1 : (k.val + 1) % c₂.verts.length = k.val + 1 := Nat.mod_eq_of_lt (by omega)
      simp only [hk1]
      have h_inner : c₂.verts.length - (k.val + 1) < c₂.verts.length := by omega
      rw [Nat.mod_eq_of_lt h_inner]
      omega
  apply Finset.card_bij (fun p _ => (p.1, bij p.2))
  · -- Maps to target
    intro ⟨k₁, k₂⟩ hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
    obtain ⟨h_v, h_n⟩ := hmem
    have hk2_lt : k₂.val < c₂.verts.length := h_fin_cast k₂
    have h_rev_v : c₂.reverse.vertex k₂.val = c₂.vertex (c₂.verts.length - 1 - k₂.val) :=
      c₂.reverse_vertex k₂.val hk2_lt
    have h_rev_n : c₂.reverse.nextVertex k₂.val =
        c₂.vertex (c₂.verts.length - 1 - (k₂.val + 1) % c₂.verts.length) :=
      c₂.reverse_nextVertex_eq k₂.val
    rw [h_rev_n] at h_v
    rw [h_rev_v] at h_n
    simp only [bij]
    have h_mod_bound : (k₂.val + 1) % c₂.verts.length ≤ c₂.verts.length - 1 := by
      have h := Nat.mod_lt (k₂.val + 1) h_len_pos; omega
    -- c₂.nextVertex (bij k₂) = c₂.vertex ((bij k₂ + 1) % len) = c₂.vertex (len - 1 - k₂)
    have h_next : c₂.nextVertex (c₂.verts.length - 1 - (k₂.val + 1) % c₂.verts.length) =
        c₂.vertex (c₂.verts.length - 1 - k₂.val) := by
      unfold GeneralCycle.nextVertex GeneralCycle.vertex
      congr 1
      ext
      by_cases hk2_last : k₂.val = c₂.verts.length - 1
      · have hk1 : (k₂.val + 1) % c₂.verts.length = 0 := by
          rw [hk2_last, Nat.sub_add_cancel (by omega : 1 ≤ c₂.verts.length)]
          exact Nat.mod_self _
        rw [hk1, hk2_last]
        simp only [Nat.sub_zero, Nat.sub_self, Nat.zero_mod, Nat.sub_add_cancel (by omega : 1 ≤ c₂.verts.length)]
        exact Nat.mod_self _
      · have hk2_lt' : k₂.val < c₂.verts.length - 1 := by omega
        have hk1 : (k₂.val + 1) % c₂.verts.length = k₂.val + 1 := Nat.mod_eq_of_lt (by omega)
        rw [hk1]
        have h_eq : c₂.verts.length - 1 - (k₂.val + 1) + 1 = c₂.verts.length - 1 - k₂.val := by omega
        rw [h_eq]
    constructor
    · rw [← h_v]
    · rw [h_next, ← h_n]
  · -- Injective
    intro ⟨k₁, k₂⟩ _ ⟨k₁', k₂'⟩ _ heq
    simp only [Prod.mk.injEq] at heq ⊢
    obtain ⟨hk1_eq, hk2_eq⟩ := heq
    constructor
    · exact hk1_eq
    · ext
      simp only [bij, Fin.mk.injEq] at hk2_eq
      have hk2_lt : k₂.val < c₂.verts.length := h_fin_cast k₂
      have hk2'_lt : k₂'.val < c₂.verts.length := h_fin_cast k₂'
      have h_mod_bound : (k₂.val + 1) % c₂.verts.length ≤ c₂.verts.length - 1 := by
        have h := Nat.mod_lt (k₂.val + 1) h_len_pos; omega
      have h_mod_bound' : (k₂'.val + 1) % c₂.verts.length ≤ c₂.verts.length - 1 := by
        have h := Nat.mod_lt (k₂'.val + 1) h_len_pos; omega
      have h_mod_eq : (k₂.val + 1) % c₂.verts.length = (k₂'.val + 1) % c₂.verts.length := by omega
      by_cases hk2_last : k₂.val = c₂.verts.length - 1
      · by_cases hk2'_last : k₂'.val = c₂.verts.length - 1
        · omega
        · have hk1 : (k₂.val + 1) % c₂.verts.length = 0 := by
            rw [hk2_last, Nat.sub_add_cancel (by omega : 1 ≤ c₂.verts.length)]
            exact Nat.mod_self _
          have hk1' : (k₂'.val + 1) % c₂.verts.length = k₂'.val + 1 := by
            apply Nat.mod_eq_of_lt; omega
          rw [hk1, hk1'] at h_mod_eq
          omega
      · by_cases hk2'_last : k₂'.val = c₂.verts.length - 1
        · have hk1' : (k₂'.val + 1) % c₂.verts.length = 0 := by
            rw [hk2'_last, Nat.sub_add_cancel (by omega : 1 ≤ c₂.verts.length)]
            exact Nat.mod_self _
          have hk1 : (k₂.val + 1) % c₂.verts.length = k₂.val + 1 := by
            apply Nat.mod_eq_of_lt; omega
          rw [hk1, hk1'] at h_mod_eq
          omega
        · have hk1 : (k₂.val + 1) % c₂.verts.length = k₂.val + 1 := by
            apply Nat.mod_eq_of_lt; omega
          have hk1' : (k₂'.val + 1) % c₂.verts.length = k₂'.val + 1 := by
            apply Nat.mod_eq_of_lt; omega
          rw [hk1, hk1'] at h_mod_eq
          omega
  · -- Surjective
    intro ⟨k₁, k₂⟩ hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    obtain ⟨h_v, h_n⟩ := hmem
    have hk2_lt : k₂.val < c₂.verts.length := k₂.isLt
    let k₂' : Fin c₂.reverse.verts.length :=
      ⟨c₂.verts.length - 1 - (k₂.val + 1) % c₂.verts.length, by
        rw [h_len_eq]; have h := Nat.mod_lt (k₂.val + 1) h_len_pos; omega⟩
    refine ⟨(k₁, k₂'), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h_k2'_lt : k₂'.val < c₂.verts.length := by
        simp only [k₂']; have h := Nat.mod_lt (k₂.val + 1) h_len_pos; omega
      have h_rev_v : c₂.reverse.vertex k₂'.val = c₂.vertex (c₂.verts.length - 1 - k₂'.val) :=
        c₂.reverse_vertex k₂'.val h_k2'_lt
      have h_rev_n : c₂.reverse.nextVertex k₂'.val =
          c₂.vertex (c₂.verts.length - 1 - (k₂'.val + 1) % c₂.verts.length) :=
        c₂.reverse_nextVertex_eq k₂'.val
      simp only [k₂'] at h_rev_v h_rev_n
      have h_mod_bound : (k₂.val + 1) % c₂.verts.length ≤ c₂.verts.length - 1 := by
        have h := Nat.mod_lt (k₂.val + 1) h_len_pos; omega
      have h_comp1 : c₂.verts.length - 1 - (c₂.verts.length - 1 - (k₂.val + 1) % c₂.verts.length) =
          (k₂.val + 1) % c₂.verts.length := by omega
      have h_comp2 : c₂.verts.length - 1 -
          ((c₂.verts.length - 1 - (k₂.val + 1) % c₂.verts.length) + 1) % c₂.verts.length =
          k₂.val := by
        have h_bij_val : c₂.verts.length - 1 - (k₂.val + 1) % c₂.verts.length + 1 =
            c₂.verts.length - (k₂.val + 1) % c₂.verts.length := by omega
        rw [h_bij_val]
        by_cases hk2_last : k₂.val = c₂.verts.length - 1
        · have hk1 : (k₂.val + 1) % c₂.verts.length = 0 := by
            rw [hk2_last, Nat.sub_add_cancel (by omega : 1 ≤ c₂.verts.length)]
            exact Nat.mod_self _
          simp only [hk1, Nat.sub_zero]
          have h_mod : c₂.verts.length % c₂.verts.length = 0 := Nat.mod_self _
          simp only [h_mod, Nat.sub_zero, hk2_last]
        · have hk2_lt' : k₂.val < c₂.verts.length - 1 := by
            cases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (by omega : k₂.val < c₂.verts.length - 1 + 1)) with
            | inl h => exact h
            | inr h => exact absurd h hk2_last
          have hk1 : (k₂.val + 1) % c₂.verts.length = k₂.val + 1 := Nat.mod_eq_of_lt (by omega)
          simp only [hk1]
          have h_inner : c₂.verts.length - (k₂.val + 1) < c₂.verts.length := by omega
          rw [Nat.mod_eq_of_lt h_inner]
          omega
      rw [h_comp1] at h_rev_v
      rw [h_comp2] at h_rev_n
      -- After rewrites:
      -- h_rev_n: c₂.reverse.nextVertex k₂'.val = c₂.vertex k₂
      -- h_rev_v: c₂.reverse.vertex k₂'.val = c₂.vertex ((k₂+1)%len)
      -- Goal: c₁.vertex k₁ = c₂.reverse.nextVertex k₂' AND c₁.nextVertex k₁ = c₂.reverse.vertex k₂'
      simp only [k₂'] at h_rev_v h_rev_n ⊢
      constructor
      · -- c₁.vertex k₁ = c₂.reverse.nextVertex k₂'
        rw [h_v, ← h_rev_n]
      · -- c₁.nextVertex k₁ = c₂.reverse.vertex k₂'
        rw [h_n, h_rev_v]
        -- Goal: c₂.nextVertex k₂ = c₂.vertex ((k₂+1)%len)
        unfold GeneralCycle.nextVertex GeneralCycle.vertex
        congr 1
        ext
        exact (Nat.mod_mod _ _).symm
    · simp only [Prod.mk.injEq]
      exact ⟨trivial, Fin.ext (bij_inv k₂)⟩

/-- Reversing flips the sign of signedOverlap.
    Same-direction edges become opposite-direction when one cycle is reversed. -/
theorem reverse_flips_overlap {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n) :
    c₁.signedOverlap c₂.reverse = -c₁.signedOverlap c₂ := by
  unfold GeneralCycle.signedOverlap
  rw [sameDirectionEdges_reverse, oppositeDirectionEdges_reverse]
  ring

/-- Opposite orientation minimizes energy when cycles share edges.
    This is the anti-ferromagnetic coupling: overlapping cycles prefer opposite orientation. -/
theorem opposite_orientation_minimizes {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_overlap_pos : c₁.signedOverlap c₂ > 0) :
    norm_sq (cycle_sum c₁ c₂.reverse) < norm_sq (cycle_sum c₁ c₂) := by
  have h_rev := reverse_flips_overlap c₁ c₂
  have h_neg : c₁.signedOverlap c₂.reverse < 0 := by
    rw [h_rev]; exact Int.neg_neg_of_pos h_overlap_pos
  rw [combined_cycle_energy_formula, combined_cycle_energy_formula, c₂.reverse_len]
  have h_len1 : (0 : ℝ) < c₁.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₁.len_ge_3)
  have h_len2 : (0 : ℝ) < c₂.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₂.len_ge_3)
  have h_prod_pos : (0 : ℝ) < c₁.len * c₂.len := mul_pos h_len1 h_len2
  rw [h_rev]
  simp only [Int.cast_neg]
  have h_overlap_real_pos : (c₁.signedOverlap c₂ : ℝ) > 0 := Int.cast_pos.mpr h_overlap_pos
  have h_diff : 2 * (-(c₁.signedOverlap c₂ : ℝ)) / (c₁.len * c₂.len) <
                2 * (c₁.signedOverlap c₂ : ℝ) / (c₁.len * c₂.len) := by
    apply div_lt_div_of_pos_right _ h_prod_pos
    linarith
  linarith

end Diaspora.Logic
