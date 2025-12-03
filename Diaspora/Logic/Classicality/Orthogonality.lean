/-
Orthogonality of disjoint cycles.

Vertex-disjoint and edge-disjoint cycles have orthogonal harmonic forms.
-/
import Diaspora.Logic.Classicality.Cycles

namespace Diaspora.Logic

open Diaspora.Core Diaspora.Hodge

variable {n : ℕ} [Fintype (Fin n)]

/-! ## Orthogonality of Disjoint Cycles -/

/-- Two GeneralCycles are vertex-disjoint if they share no vertices. -/
def GeneralCycle.VertexDisjoint {n : ℕ} (c₁ c₂ : GeneralCycle n) : Prop :=
  ∀ v : Fin n, v ∈ c₁.verts → v ∉ c₂.verts

/-- If cycles are vertex-disjoint, cycle forms are supported on disjoint edge sets. -/
lemma disjoint_cycles_disjoint_support {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_disjoint : GeneralCycle.VertexDisjoint c₁ c₂) :
    ∀ i j, (general_cycle_form c₁).val i j ≠ 0 →
           (general_cycle_form c₂).val i j = 0 := by
  intro i j h_c1_nonzero
  unfold general_cycle_form at h_c1_nonzero ⊢
  simp only at h_c1_nonzero ⊢
  -- If c₁ has nonzero value on (i,j), then i or j is in c₁.verts
  split_ifs at h_c1_nonzero with h1 h2
  · -- Forward edge of c₁: i is in c₁
    obtain ⟨k, hk⟩ := h1
    have h_i_in_c1 : i ∈ c₁.verts := by
      rw [← hk.1]
      unfold GeneralCycle.vertex
      exact List.get_mem c₁.verts _
    have h_i_not_in_c2 : i ∉ c₂.verts := h_disjoint i h_i_in_c1
    have h_j_in_c1 : j ∈ c₁.verts := by
      rw [← hk.2]
      unfold GeneralCycle.nextVertex GeneralCycle.vertex
      exact List.get_mem c₁.verts _
    have h_j_not_in_c2 : j ∉ c₂.verts := h_disjoint j h_j_in_c1
    -- Now show c₂ form is 0 on (i,j) since neither i nor j is in c₂
    split_ifs with h3 h4
    · exfalso
      obtain ⟨k2, hk2⟩ := h3
      apply h_i_not_in_c2
      rw [← hk2.1]
      unfold GeneralCycle.vertex
      exact List.get_mem c₂.verts _
    · exfalso
      obtain ⟨k2, hk2⟩ := h4
      apply h_j_not_in_c2
      rw [← hk2.1]
      unfold GeneralCycle.vertex
      exact List.get_mem c₂.verts _
    · rfl
  · -- Reverse edge of c₁: j and i are in c₁
    obtain ⟨k, hk⟩ := h2
    have h_j_in_c1 : j ∈ c₁.verts := by
      rw [← hk.1]
      unfold GeneralCycle.vertex
      exact List.get_mem c₁.verts _
    have h_j_not_in_c2 : j ∉ c₂.verts := h_disjoint j h_j_in_c1
    have h_i_in_c1 : i ∈ c₁.verts := by
      rw [← hk.2]
      unfold GeneralCycle.nextVertex GeneralCycle.vertex
      exact List.get_mem c₁.verts _
    have h_i_not_in_c2 : i ∉ c₂.verts := h_disjoint i h_i_in_c1
    split_ifs with h3 h4
    · exfalso
      obtain ⟨k2, hk2⟩ := h3
      apply h_i_not_in_c2
      rw [← hk2.1]
      unfold GeneralCycle.vertex
      exact List.get_mem c₂.verts _
    · exfalso
      obtain ⟨k2, hk2⟩ := h4
      apply h_j_not_in_c2
      rw [← hk2.1]
      unfold GeneralCycle.vertex
      exact List.get_mem c₂.verts _
    · rfl
  · -- c₁ form is 0 at (i,j), contradiction
    exfalso
    exact h_c1_nonzero rfl

/-- **Independence of Topological Defects**:
    Disjoint cycles have orthogonal harmonic forms.

    Physical interpretation: topological defects localized in different regions
    of the graph do not interact energetically. Their contributions to the
    total energy are additive (Pythagorean).
-/
theorem disjoint_cycles_orthogonal {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_disjoint : GeneralCycle.VertexDisjoint c₁ c₂) :
    inner_product_C1 (general_cycle_form c₁) (general_cycle_form c₂) = 0 := by
  unfold inner_product_C1
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases h : (general_cycle_form c₁).val i j = 0
  · simp [h]
  · have h2 := disjoint_cycles_disjoint_support c₁ c₂ h_disjoint i j h
    simp [h2]

/-- Corollary: The energy of two disjoint cycles is additive. -/
theorem disjoint_cycles_energy_additive {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_disjoint : GeneralCycle.VertexDisjoint c₁ c₂) :
    let σ_sum : C1 n := {
      val := fun i j => (general_cycle_form c₁).val i j + (general_cycle_form c₂).val i j,
      skew := by intro i j; rw [(general_cycle_form c₁).skew, (general_cycle_form c₂).skew]; ring
    }
    norm_sq σ_sum = norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) := by
  intro σ_sum
  have h_orth := disjoint_cycles_orthogonal c₁ c₂ h_disjoint
  unfold norm_sq inner_product_C1 at h_orth ⊢
  have h_expand : ∀ i j, σ_sum.val i j * σ_sum.val i j =
      (general_cycle_form c₁).val i j * (general_cycle_form c₁).val i j +
      2 * (general_cycle_form c₁).val i j * (general_cycle_form c₂).val i j +
      (general_cycle_form c₂).val i j * (general_cycle_form c₂).val i j := by
    intro i j; ring
  have h_sum_expand : ∑ i, ∑ j, σ_sum.val i j * σ_sum.val i j =
      ∑ i, ∑ j, (general_cycle_form c₁).val i j * (general_cycle_form c₁).val i j +
      2 * ∑ i, ∑ j, (general_cycle_form c₁).val i j * (general_cycle_form c₂).val i j +
      ∑ i, ∑ j, (general_cycle_form c₂).val i j * (general_cycle_form c₂).val i j := by
    simp_rw [h_expand, Finset.sum_add_distrib]
    congr 1; congr 1
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
    ring
  have h_cross_zero : ∑ i, ∑ j, (general_cycle_form c₁).val i j * (general_cycle_form c₂).val i j = 0 := by
    have := h_orth
    simp only [one_div, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or] at this
    exact this
  rw [h_sum_expand, h_cross_zero]
  ring

/-! ## Edge-Disjoint Cycles: Stronger Orthogonality -/

/-- The set of directed edges of a GeneralCycle. An edge (i, j) is in the cycle if
    there exists k such that vertex k = i and nextVertex k = j. -/
def GeneralCycle.edges {n : ℕ} (c : GeneralCycle n) : Set (Fin n × Fin n) :=
  { e | ∃ k : Fin c.verts.length, c.vertex k.val = e.1 ∧ c.nextVertex k.val = e.2 }

/-- Two GeneralCycles are edge-disjoint if they share no edges (in either direction). -/
def GeneralCycle.EdgeDisjoint {n : ℕ} (c₁ c₂ : GeneralCycle n) : Prop :=
  ∀ i j : Fin n, (i, j) ∈ c₁.edges → (i, j) ∉ c₂.edges ∧ (j, i) ∉ c₂.edges

/-- Edge-disjoint cycles have disjoint support for their cycle forms. -/
lemma edge_disjoint_cycles_disjoint_support {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_disjoint : GeneralCycle.EdgeDisjoint c₁ c₂) :
    ∀ i j, (general_cycle_form c₁).val i j ≠ 0 →
           (general_cycle_form c₂).val i j = 0 := by
  intro i j h_c1_nonzero
  unfold general_cycle_form at h_c1_nonzero ⊢
  simp only at h_c1_nonzero ⊢
  split_ifs at h_c1_nonzero with h1 h2
  · -- Forward edge of c₁: (i, j) is an edge of c₁
    have h_edge : (i, j) ∈ c₁.edges := h1
    have ⟨h_not_fwd, h_not_rev⟩ := h_disjoint i j h_edge
    -- c₂ has no forward edge (i,j)
    have h_no_c2_fwd : ¬∃ k : Fin c₂.verts.length, c₂.vertex k.val = i ∧ c₂.nextVertex k.val = j := h_not_fwd
    -- c₂ has no forward edge (j,i), so (i,j) is not a reverse edge of c₂
    have h_no_c2_rev : ¬∃ k : Fin c₂.verts.length, c₂.vertex k.val = j ∧ c₂.nextVertex k.val = i := h_not_rev
    simp only [h_no_c2_fwd, h_no_c2_rev, ↓reduceIte]
  · -- Reverse edge of c₁: (j, i) is an edge of c₁
    have h_edge : (j, i) ∈ c₁.edges := h2
    have ⟨h_not_fwd, h_not_rev⟩ := h_disjoint j i h_edge
    -- c₂ has no forward edge (j,i)
    have h_no_c2_rev : ¬∃ k : Fin c₂.verts.length, c₂.vertex k.val = j ∧ c₂.nextVertex k.val = i := h_not_fwd
    -- c₂ has no forward edge (i,j)
    have h_no_c2_fwd : ¬∃ k : Fin c₂.verts.length, c₂.vertex k.val = i ∧ c₂.nextVertex k.val = j := h_not_rev
    simp only [h_no_c2_fwd, h_no_c2_rev, ↓reduceIte]
  · -- c₁ form is 0 at (i,j), contradiction
    exfalso
    exact h_c1_nonzero rfl

/-- **Generalized Independence of Topological Defects**:
    Edge-disjoint cycles have orthogonal harmonic forms.

    This generalizes disjoint_cycles_orthogonal: cycles that share vertices
    but no edges still produce independent harmonic modes. What matters for
    orthogonality is edge-disjointness, not vertex-disjointness.

    Physical interpretation: Topological defects on different "channels" (edges)
    don't interact, even if they share junction points (vertices).
-/
theorem edge_disjoint_cycles_orthogonal {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_disjoint : GeneralCycle.EdgeDisjoint c₁ c₂) :
    inner_product_C1 (general_cycle_form c₁) (general_cycle_form c₂) = 0 := by
  unfold inner_product_C1
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases h : (general_cycle_form c₁).val i j = 0
  · simp [h]
  · have h2 := edge_disjoint_cycles_disjoint_support c₁ c₂ h_disjoint i j h
    simp [h2]

/-- Vertex-disjoint implies edge-disjoint: sharing no vertices means sharing no edges. -/
theorem vertex_disjoint_implies_edge_disjoint {n : ℕ}
    (c₁ c₂ : GeneralCycle n)
    (h_vert : GeneralCycle.VertexDisjoint c₁ c₂) :
    GeneralCycle.EdgeDisjoint c₁ c₂ := by
  intro i j h_edge
  unfold GeneralCycle.edges at h_edge
  simp only [Set.mem_setOf_eq] at h_edge
  obtain ⟨k, hk_i, hk_j⟩ := h_edge
  have h_i_in_c1 : i ∈ c₁.verts := by
    rw [← hk_i]
    unfold GeneralCycle.vertex
    exact List.get_mem c₁.verts _
  have h_i_not_in_c2 : i ∉ c₂.verts := h_vert i h_i_in_c1
  constructor
  · -- (i, j) not an edge of c₂
    intro h_c2
    simp only [GeneralCycle.edges, Set.mem_setOf_eq] at h_c2
    obtain ⟨k2, hk2_i, _⟩ := h_c2
    apply h_i_not_in_c2
    rw [← hk2_i]
    unfold GeneralCycle.vertex
    exact List.get_mem c₂.verts _
  · -- (j, i) not an edge of c₂
    intro h_c2
    simp only [GeneralCycle.edges, Set.mem_setOf_eq] at h_c2
    obtain ⟨k2, _, hk2_i⟩ := h_c2
    apply h_i_not_in_c2
    rw [← hk2_i]
    unfold GeneralCycle.nextVertex GeneralCycle.vertex
    exact List.get_mem c₂.verts _

/-- Corollary: Energy additivity for edge-disjoint cycles. -/
theorem edge_disjoint_cycles_energy_additive {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_disjoint : GeneralCycle.EdgeDisjoint c₁ c₂) :
    let σ_sum : C1 n := {
      val := fun i j => (general_cycle_form c₁).val i j + (general_cycle_form c₂).val i j,
      skew := by intro i j; rw [(general_cycle_form c₁).skew, (general_cycle_form c₂).skew]; ring
    }
    norm_sq σ_sum = norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) := by
  intro σ_sum
  have h_orth := edge_disjoint_cycles_orthogonal c₁ c₂ h_disjoint
  unfold norm_sq inner_product_C1 at h_orth ⊢
  have h_expand : ∀ i j, σ_sum.val i j * σ_sum.val i j =
      (general_cycle_form c₁).val i j * (general_cycle_form c₁).val i j +
      2 * (general_cycle_form c₁).val i j * (general_cycle_form c₂).val i j +
      (general_cycle_form c₂).val i j * (general_cycle_form c₂).val i j := by
    intro i j; ring
  have h_sum_expand : ∑ i, ∑ j, σ_sum.val i j * σ_sum.val i j =
      ∑ i, ∑ j, (general_cycle_form c₁).val i j * (general_cycle_form c₁).val i j +
      2 * ∑ i, ∑ j, (general_cycle_form c₁).val i j * (general_cycle_form c₂).val i j +
      ∑ i, ∑ j, (general_cycle_form c₂).val i j * (general_cycle_form c₂).val i j := by
    simp_rw [h_expand, Finset.sum_add_distrib]
    congr 1; congr 1
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
    ring
  have h_cross_zero : ∑ i, ∑ j, (general_cycle_form c₁).val i j * (general_cycle_form c₂).val i j = 0 := by
    have := h_orth
    simp only [one_div, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or] at this
    exact this
  rw [h_sum_expand, h_cross_zero]
  ring

end Diaspora.Logic
