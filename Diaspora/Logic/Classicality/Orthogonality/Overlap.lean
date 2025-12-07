/-
Overlapping cycles: definitions and basic properties for edge overlap counting.
-/
import Diaspora.Logic.Classicality.Orthogonality.Disjoint

namespace Diaspora.Logic

open Diaspora.Core Diaspora.Hodge

variable {n : ℕ} [Fintype (Fin n)]

/-! ## Overlapping Cycles: General Inner Product -/

/-- Count of directed edges where both cycles traverse in the same direction.
    An edge (i,j) counts if it's in c₁.edges AND in c₂.edges. -/
def GeneralCycle.sameDirectionEdges {n : ℕ} [DecidableEq (Fin n)] (c₁ c₂ : GeneralCycle n) : ℕ :=
  (Finset.univ.filter fun (p : Fin c₁.verts.length × Fin c₂.verts.length) =>
    c₁.vertex p.1.val = c₂.vertex p.2.val ∧
    c₁.nextVertex p.1.val = c₂.nextVertex p.2.val).card

/-- Count of directed edges where cycles traverse in opposite directions.
    An edge counts if (i,j) is in c₁.edges AND (j,i) is in c₂.edges. -/
def GeneralCycle.oppositeDirectionEdges {n : ℕ} [DecidableEq (Fin n)] (c₁ c₂ : GeneralCycle n) : ℕ :=
  (Finset.univ.filter fun (p : Fin c₁.verts.length × Fin c₂.verts.length) =>
    c₁.vertex p.1.val = c₂.nextVertex p.2.val ∧
    c₁.nextVertex p.1.val = c₂.vertex p.2.val).card

/-- Signed edge overlap: same-direction minus opposite-direction shared edges. -/
def GeneralCycle.signedOverlap {n : ℕ} [DecidableEq (Fin n)] (c₁ c₂ : GeneralCycle n) : ℤ :=
  (c₁.sameDirectionEdges c₂ : ℤ) - (c₁.oppositeDirectionEdges c₂ : ℤ)

/-- sameDirectionEdges is symmetric. -/
theorem sameDirectionEdges_symm {n : ℕ} [DecidableEq (Fin n)] (c₁ c₂ : GeneralCycle n) :
    c₁.sameDirectionEdges c₂ = c₂.sameDirectionEdges c₁ := by
  unfold GeneralCycle.sameDirectionEdges
  apply Finset.card_bij (fun (p : Fin c₁.verts.length × Fin c₂.verts.length) _ => (p.2, p.1))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.1.symm, hp.2.symm⟩
  · intro p₁ _ p₂ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 h.1
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact ⟨(q.2, q.1), ⟨hq.1.symm, hq.2.symm⟩, rfl⟩

/-- oppositeDirectionEdges is symmetric. -/
theorem oppositeDirectionEdges_symm {n : ℕ} [DecidableEq (Fin n)] (c₁ c₂ : GeneralCycle n) :
    c₁.oppositeDirectionEdges c₂ = c₂.oppositeDirectionEdges c₁ := by
  unfold GeneralCycle.oppositeDirectionEdges
  apply Finset.card_bij (fun (p : Fin c₁.verts.length × Fin c₂.verts.length) _ => (p.2, p.1))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.2.symm, hp.1.symm⟩
  · intro p₁ _ p₂ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 h.1
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact ⟨(q.2, q.1), ⟨hq.2.symm, hq.1.symm⟩, rfl⟩

/-- The signed overlap is symmetric. -/
theorem signedOverlap_symm {n : ℕ} [DecidableEq (Fin n)] (c₁ c₂ : GeneralCycle n) :
    c₁.signedOverlap c₂ = c₂.signedOverlap c₁ := by
  unfold GeneralCycle.signedOverlap
  rw [sameDirectionEdges_symm, oppositeDirectionEdges_symm]

/-- A cycle's sameDirectionEdges with itself equals its length. -/
theorem sameDirectionEdges_self {n : ℕ} [DecidableEq (Fin n)] (c : GeneralCycle n) :
    c.sameDirectionEdges c = c.len := by
  unfold GeneralCycle.sameDirectionEdges
  -- The matching pairs are exactly (k, k) for k in Fin c.len
  have h_eq_diag : (Finset.univ.filter fun (p : Fin c.verts.length × Fin c.verts.length) =>
      c.vertex p.1.val = c.vertex p.2.val ∧
      c.nextVertex p.1.val = c.nextVertex p.2.val) =
      Finset.univ.image (fun k : Fin c.verts.length => (k, k)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro ⟨h1, _⟩
      use p.1
      -- p.1 = p.2 because vertices are distinct
      have h_nodup := c.nodup
      unfold GeneralCycle.vertex at h1
      have h_inj := h_nodup.get_inj_iff.mp h1
      simp only [Fin.ext_iff, Nat.mod_eq_of_lt p.1.isLt, Nat.mod_eq_of_lt p.2.isLt] at h_inj
      exact Prod.ext rfl (Fin.ext h_inj)
    · intro ⟨k, hk⟩
      rw [← hk]
      simp
  rw [h_eq_diag, Finset.card_image_of_injective]
  · simp only [Finset.card_fin, GeneralCycle.len]
  · intro a b hab
    simp only [Prod.mk.injEq] at hab
    exact hab.1

/-- A cycle's oppositeDirectionEdges with itself is zero. -/
theorem oppositeDirectionEdges_self {n : ℕ} [DecidableEq (Fin n)] (c : GeneralCycle n) :
    c.oppositeDirectionEdges c = 0 := by
  unfold GeneralCycle.oppositeDirectionEdges
  rw [Finset.card_eq_zero]
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
  intro h1 h2
  -- This would mean vertex p.1 = nextVertex p.2 and nextVertex p.1 = vertex p.2
  -- Which means (p.1, p.2) are adjacent in both directions - impossible in a simple cycle of length ≥ 3
  have h_len := c.len_ge_3
  have h_nodup := c.nodup
  unfold GeneralCycle.nextVertex GeneralCycle.vertex at h1 h2
  have h_idx1 := h_nodup.get_inj_iff.mp h1
  have h_idx2 := h_nodup.get_inj_iff.mp h2
  simp only [Fin.ext_iff] at h_idx1 h_idx2
  have h_p1_mod : p.1.val = (p.2.val + 1) % c.verts.length := by
    rw [Nat.mod_eq_of_lt p.1.isLt] at h_idx1
    exact h_idx1
  have h_p2_mod : p.2.val = (p.1.val + 1) % c.verts.length := by
    rw [Nat.mod_eq_of_lt p.2.isLt] at h_idx2
    exact h_idx2.symm
  -- Substituting: p.2 = (p.1 + 1) % len = ((p.2 + 1) % len + 1) % len
  -- This means (p.2 + 2) % len = p.2, contradiction for len ≥ 3
  have h_len_pos : 0 < c.verts.length := by omega
  have h_cycle : (p.2.val + 2) % c.verts.length = p.2.val := by
    have h1_mod : 1 % c.verts.length = 1 := Nat.mod_eq_of_lt (by omega : 1 < c.verts.length)
    calc (p.2.val + 2) % c.verts.length
        = ((p.2.val + 1) + 1) % c.verts.length := by ring_nf
      _ = ((p.2.val + 1) % c.verts.length + 1) % c.verts.length := by
          rw [Nat.add_mod (p.2.val + 1) 1, h1_mod]
      _ = (p.1.val + 1) % c.verts.length := by rw [← h_p1_mod]
      _ = p.2.val := h_p2_mod.symm
  have h_two_lt : 2 < c.verts.length := by omega
  cases Nat.lt_or_ge (p.2.val + 2) c.verts.length with
  | inl h_small =>
    rw [Nat.mod_eq_of_lt h_small] at h_cycle
    omega
  | inr h_big =>
    have h_sub_lt : p.2.val + 2 - c.verts.length < c.verts.length := by
      have : p.2.val < c.verts.length := p.2.isLt
      omega
    rw [Nat.mod_eq_sub_mod h_big, Nat.mod_eq_of_lt h_sub_lt] at h_cycle
    omega

/-- A cycle's overlap with itself equals its length (all edges same direction). -/
theorem signedOverlap_self {n : ℕ} [DecidableEq (Fin n)] (c : GeneralCycle n) :
    c.signedOverlap c = c.len := by
  unfold GeneralCycle.signedOverlap
  rw [sameDirectionEdges_self, oppositeDirectionEdges_self]
  simp

/-- Edge-disjoint cycles have zero sameDirectionEdges. -/
theorem edge_disjoint_sameDirectionEdges_zero {n : ℕ} [DecidableEq (Fin n)] (c₁ c₂ : GeneralCycle n)
    (h : GeneralCycle.EdgeDisjoint c₁ c₂) :
    c₁.sameDirectionEdges c₂ = 0 := by
  unfold GeneralCycle.sameDirectionEdges
  rw [Finset.card_eq_zero]
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
  intro h1 h2
  have h_edge : (c₁.vertex p.1.val, c₁.nextVertex p.1.val) ∈ c₁.edges := ⟨p.1, rfl, rfl⟩
  have h_in_c2 : (c₁.vertex p.1.val, c₁.nextVertex p.1.val) ∈ c₂.edges := by
    use p.2
    exact ⟨h1.symm, h2.symm⟩
  exact (h _ _ h_edge).1 h_in_c2

/-- Edge-disjoint cycles have zero oppositeDirectionEdges. -/
theorem edge_disjoint_oppositeDirectionEdges_zero {n : ℕ} [DecidableEq (Fin n)] (c₁ c₂ : GeneralCycle n)
    (h : GeneralCycle.EdgeDisjoint c₁ c₂) :
    c₁.oppositeDirectionEdges c₂ = 0 := by
  unfold GeneralCycle.oppositeDirectionEdges
  rw [Finset.card_eq_zero]
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
  intro h1 h2
  have h_edge : (c₁.vertex p.1.val, c₁.nextVertex p.1.val) ∈ c₁.edges := ⟨p.1, rfl, rfl⟩
  have h_in_c2 : (c₁.nextVertex p.1.val, c₁.vertex p.1.val) ∈ c₂.edges := by
    use p.2
    exact ⟨h2.symm, h1.symm⟩
  exact (h _ _ h_edge).2 h_in_c2

/-- Edge-disjoint cycles have zero signed overlap. -/
theorem edge_disjoint_signedOverlap_zero {n : ℕ} [DecidableEq (Fin n)] (c₁ c₂ : GeneralCycle n)
    (h : GeneralCycle.EdgeDisjoint c₁ c₂) :
    c₁.signedOverlap c₂ = 0 := by
  unfold GeneralCycle.signedOverlap
  rw [edge_disjoint_sameDirectionEdges_zero c₁ c₂ h, edge_disjoint_oppositeDirectionEdges_zero c₁ c₂ h]
  simp

/-! ## Helper lemmas for the inner product formula -/

/-- The γ value at a forward edge of c is 1/len. -/
lemma cycle_form_forward_edge {n : ℕ} [Fintype (Fin n)] [NeZero n] (c : GeneralCycle n)
    (k : Fin c.verts.length) :
    (general_cycle_form c).val (c.vertex k.val) (c.nextVertex k.val) = 1 / c.len := by
  unfold general_cycle_form
  have h_ex : ∃ k' : Fin c.verts.length, c.vertex k'.val = c.vertex k.val ∧
              c.nextVertex k'.val = c.nextVertex k.val := ⟨k, rfl, rfl⟩
  simp only [h_ex, ↓reduceIte]

/-- The γ value at a reverse edge of c is -1/len. -/
lemma cycle_form_reverse_edge {n : ℕ} [Fintype (Fin n)] [NeZero n] (c : GeneralCycle n)
    (k : Fin c.verts.length) :
    (general_cycle_form c).val (c.nextVertex k.val) (c.vertex k.val) = -(1 / c.len) := by
  have h := (general_cycle_form c).skew (c.vertex k.val) (c.nextVertex k.val)
  rw [cycle_form_forward_edge] at h
  linarith

/-- c₂.nodup ensures at most one same-direction match per k₁. -/
lemma unique_same_direction_match {n : ℕ} [DecidableEq (Fin n)] (c₁ c₂ : GeneralCycle n)
    (k₁ : Fin c₁.verts.length) (k₂ k₂' : Fin c₂.verts.length)
    (h : c₁.vertex k₁.val = c₂.vertex k₂.val ∧ c₁.nextVertex k₁.val = c₂.nextVertex k₂.val)
    (h' : c₁.vertex k₁.val = c₂.vertex k₂'.val ∧ c₁.nextVertex k₁.val = c₂.nextVertex k₂'.val) :
    k₂ = k₂' := by
  have h_nodup := c₂.nodup
  have h_len_pos : 0 < c₂.verts.length := Nat.lt_of_lt_of_le (by omega) c₂.len_ge_3
  unfold GeneralCycle.vertex at h h'
  have h_eq : c₂.verts.get ⟨k₂.val % c₂.verts.length, Nat.mod_lt _ h_len_pos⟩ =
              c₂.verts.get ⟨k₂'.val % c₂.verts.length, Nat.mod_lt _ h_len_pos⟩ := by
    rw [← h.1, ← h'.1]
  have h_inj := h_nodup.get_inj_iff.mp h_eq
  simp only [Fin.ext_iff, Nat.mod_eq_of_lt k₂.isLt, Nat.mod_eq_of_lt k₂'.isLt] at h_inj
  exact Fin.ext h_inj

/-- c₂.nodup ensures at most one opposite-direction match per k₁. -/
lemma unique_opposite_direction_match {n : ℕ} [DecidableEq (Fin n)] (c₁ c₂ : GeneralCycle n)
    (k₁ : Fin c₁.verts.length) (k₂ k₂' : Fin c₂.verts.length)
    (h : c₁.vertex k₁.val = c₂.nextVertex k₂.val ∧ c₁.nextVertex k₁.val = c₂.vertex k₂.val)
    (h' : c₁.vertex k₁.val = c₂.nextVertex k₂'.val ∧ c₁.nextVertex k₁.val = c₂.vertex k₂'.val) :
    k₂ = k₂' := by
  have h_nodup := c₂.nodup
  have h_len_pos : 0 < c₂.verts.length := Nat.lt_of_lt_of_le (by omega) c₂.len_ge_3
  unfold GeneralCycle.vertex at h h'
  have h_eq : c₂.verts.get ⟨k₂.val % c₂.verts.length, Nat.mod_lt _ h_len_pos⟩ =
              c₂.verts.get ⟨k₂'.val % c₂.verts.length, Nat.mod_lt _ h_len_pos⟩ := by
    rw [← h.2, ← h'.2]
  have h_inj := h_nodup.get_inj_iff.mp h_eq
  simp only [Fin.ext_iff, Nat.mod_eq_of_lt k₂.isLt, Nat.mod_eq_of_lt k₂'.isLt] at h_inj
  exact Fin.ext h_inj

end Diaspora.Logic
