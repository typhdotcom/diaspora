import Diaspora.Core.Calculus
import Diaspora.Hodge.Decomposition
import Diaspora.Hodge.Twist
import Mathlib.Order.WellFounded
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace Diaspora.Logic

open Diaspora.Core Diaspora.Hodge

variable {n : ℕ} [Fintype (Fin n)]

section Definitions

/--
Convert a DynamicGraph to a SimpleGraph (forgetting orientation, keeping adjacency).
-/
def DynamicGraph.toSimpleGraph (G : DynamicGraph n) : SimpleGraph (Fin n) where
  Adj := fun i j => (i, j) ∈ G.active_edges
  symm := fun i j h => (G.symmetric i j).mp h
  loopless := fun i h => G.no_loops i h

/-- A 'Classical' universe is one where the Harmonic subspace is empty. -/
def IsClassical (G : DynamicGraph n) : Prop :=
  Module.finrank ℝ (HarmonicSubspace G) = 0

/-- Membership defined by Gradient Flow: child lies at lower potential than parent. -/
def IsMember (G : DynamicGraph n) (ϕ : C0 n) (child parent : Fin n) : Prop :=
  (parent, child) ∈ G.active_edges ∧ (ϕ parent > ϕ child)

/-- A potential is 'Faithful' if it orients every active edge (no ties). -/
def IsFaithfulPotential (G : DynamicGraph n) (ϕ : C0 n) : Prop :=
  ∀ i j, (i, j) ∈ G.active_edges → ϕ i ≠ ϕ j

end Definitions

section Theorems


/--
A SimpleCycle on n nodes embeds into a graph G if all its edges are active.
-/
def cycleEmbeddedIn (cycle : SimpleCycle n) (G : DynamicGraph n) : Prop :=
  ∀ i : Fin n, (i, cycle.next i) ∈ G.active_edges

/--
When a cycle is embedded in G, its Dehn twist vanishes outside G's active edges.
-/
lemma dehn_twist_supported_on_embedded [NeZero n] (cycle : SimpleCycle n)
    (G : DynamicGraph n) (h_embedded : cycleEmbeddedIn cycle G) :
    ∀ i j, (i, j) ∉ G.active_edges → (dehn_twist cycle).val i j = 0 := by
  intro i j h_not_active
  unfold dehn_twist
  simp only
  split_ifs with h1 h2
  · exfalso
    apply h_not_active
    rw [h1.1]
    exact h_embedded i
  · exfalso
    apply h_not_active
    have h_rev : (j, i) ∈ G.active_edges := by rw [h2.1]; exact h_embedded j
    exact (G.symmetric j i).mp h_rev
  · rfl

/--
Lift dehn_twist to ActiveForm G when the cycle is embedded.
-/
noncomputable def dehn_twist_active [NeZero n] (cycle : SimpleCycle n)
    (G : DynamicGraph n) (h_embedded : cycleEmbeddedIn cycle G) : ActiveForm G :=
  ⟨dehn_twist cycle, dehn_twist_supported_on_embedded cycle G h_embedded⟩

/-- Cycles create harmonic forms with positive energy. -/
lemma cycle_creates_mass [NeZero n] (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3) :
  IsHarmonic (dehn_twist cycle) ∧ norm_sq (dehn_twist cycle) > 0 := by
  constructor
  · exact dehn_twist_is_harmonic cycle h_n_ge_3
  · rw [dehn_twist_energy cycle h_n_ge_3]
    have h : (n : ℝ) > 0 := by positivity
    positivity

/-- A cycle creates non-zero harmonic energy. Energy = 1/n. -/
theorem matter_is_paradox [NeZero n] (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3) :
  ∃ (γ : C1 n), IsHarmonic γ ∧ norm_sq γ = 1 / n := by
  use dehn_twist cycle
  exact ⟨dehn_twist_is_harmonic cycle h_n_ge_3, dehn_twist_energy cycle h_n_ge_3⟩

/-- The Dehn twist, when embedded in G, lives in the HarmonicSubspace. -/
lemma dehn_twist_in_harmonic [DecidableEq (Fin n)] [NeZero n]
    (G : DynamicGraph n) (cycle : SimpleCycle n)
    (h_embedded : cycleEmbeddedIn cycle G) (h_n_ge_3 : n ≥ 3) :
    dehn_twist_active cycle G h_embedded ∈ HarmonicSubspace G := by
  rw [HarmonicSubspace, Submodule.mem_orthogonal]
  intro σ hσ
  obtain ⟨φ, hφ⟩ := LinearMap.mem_range.mp hσ
  rw [← hφ]
  have h_harm : IsHarmonic (dehn_twist cycle) := dehn_twist_is_harmonic cycle h_n_ge_3
  show Diaspora.Core.ActiveForm.inner (d_G_linear G φ) (dehn_twist_active cycle G h_embedded) = 0
  unfold Diaspora.Core.ActiveForm.inner
  have h_dehn_val : (dehn_twist_active cycle G h_embedded).val = dehn_twist cycle := rfl
  rw [h_dehn_val]
  have h_eq : inner_product_C1 (d_G_linear G φ).val (dehn_twist cycle) =
              inner_product_C1 (d0 φ) (dehn_twist cycle) := by
    unfold inner_product_C1
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h_cycle_edge : (dehn_twist cycle).val i j = 0
    · simp [h_cycle_edge]
    · have h_on_cycle : j = cycle.next i ∨ i = cycle.next j := by
        unfold dehn_twist at h_cycle_edge
        simp only at h_cycle_edge
        by_contra h_neg
        push_neg at h_neg
        have h1 : ¬(j = cycle.next i ∧ i ≠ cycle.next j) := by tauto
        have h2 : ¬(i = cycle.next j ∧ j ≠ cycle.next i) := by tauto
        simp [h1, h2] at h_cycle_edge
      have h_active : (i, j) ∈ G.active_edges := by
        cases h_on_cycle with
        | inl h => rw [h]; exact h_embedded i
        | inr h =>
          have h_ji : (j, cycle.next j) ∈ G.active_edges := h_embedded j
          rw [← h] at h_ji
          exact (G.symmetric j i).mp h_ji
      have h_d_G : (d_G_linear G φ).val.val i j = (d0 φ).val i j := by
        show (d_G G φ).val.val i j = (d0 φ).val i j
        unfold d_G d0
        simp only [h_active, ↓reduceIte]
      rw [h_d_G]
  rw [h_eq]
  rw [divergence_is_adjoint]
  have h_div_zero : divergence (dehn_twist cycle) = fun _ => 0 := by
    rw [← IsHarmonic_iff_divergence_zero]
    exact h_harm
  simp [h_div_zero]

/-- The lifted Dehn twist is nonzero (has positive norm). -/
lemma dehn_twist_active_ne_zero [DecidableEq (Fin n)] [NeZero n]
    (G : DynamicGraph n) (cycle : SimpleCycle n)
    (h_embedded : cycleEmbeddedIn cycle G) (h_n_ge_3 : n ≥ 3) :
    dehn_twist_active cycle G h_embedded ≠ 0 := by
  intro h_zero
  have h_pos := (cycle_creates_mass cycle h_n_ge_3).2
  have h_val : (dehn_twist_active cycle G h_embedded).val = dehn_twist cycle := rfl
  have h_norm : norm_sq (dehn_twist cycle) > 0 := h_pos
  have h_val_zero : (0 : ActiveForm G).val = ⟨fun _ _ => 0, by intro i j; ring⟩ := rfl
  rw [h_zero] at h_val
  simp only [h_val_zero] at h_val
  have h_dehn_zero : dehn_twist cycle = ⟨fun _ _ => 0, by intro i j; ring⟩ := h_val.symm
  unfold norm_sq inner_product_C1 at h_norm
  rw [h_dehn_zero] at h_norm
  simp at h_norm

/-- Cycles are incompatible with classicality: embedded cycle ⟹ dim(H) > 0. -/
theorem cycle_implies_nonclassical [DecidableEq (Fin n)] [NeZero n]
    (G : DynamicGraph n) (cycle : SimpleCycle n)
    (h_embedded : cycleEmbeddedIn cycle G) (h_n_ge_3 : n ≥ 3) :
    ¬ IsClassical G := by
  intro h_classical
  unfold IsClassical at h_classical
  have h_all_zero := finrank_zero_iff_forall_zero.mp h_classical
  have h_in := dehn_twist_in_harmonic G cycle h_embedded h_n_ge_3
  have h_ne := dehn_twist_active_ne_zero G cycle h_embedded h_n_ge_3
  have h_zero := h_all_zero ⟨dehn_twist_active cycle G h_embedded, h_in⟩
  simp only [Submodule.mk_eq_zero] at h_zero
  exact h_ne h_zero

/-- IsMember is well-founded for any potential on a finite graph. -/
theorem isMember_wellFounded (G : DynamicGraph n) (ϕ : C0 n) :
    WellFounded (IsMember G ϕ) := by
  let gtPot : Fin n → Fin n → Prop := fun child parent => ϕ parent > ϕ child
  have h_sub : Subrelation (IsMember G ϕ) gtPot := @fun x y h => h.2
  have h_trans : IsTrans (Fin n) gtPot := ⟨fun _ _ _ hab hbc => lt_trans hab hbc⟩
  have h_irrefl : IsIrrefl (Fin n) gtPot := ⟨fun _ h => lt_irrefl _ h⟩
  have h_wf : WellFounded gtPot := @Finite.wellFounded_of_trans_of_irrefl _ _ _ h_trans h_irrefl
  exact Subrelation.wf h_sub h_wf

/-- Weak version: zero potential makes IsMember empty. See `classical_universe_admits_rank`. -/
theorem zfc_is_the_vacuum_weak [DecidableEq (Fin n)]
    (G : DynamicGraph n) (_h_class : IsClassical G) :
    ∃ (ϕ : C0 n), WellFounded (IsMember G ϕ) := by
  use fun _ => 0
  exact isMember_wellFounded G _

/-- Russell loops create mass: embedded cycle ⟹ finrank H ≥ 1. -/
theorem russell_loop_creates_mass [DecidableEq (Fin n)] [NeZero n]
    (G : DynamicGraph n) (cycle : SimpleCycle n)
    (h_embedded : cycleEmbeddedIn cycle G) (h_n_ge_3 : n ≥ 3) :
    Module.finrank ℝ (HarmonicSubspace G) ≥ 1 := by
  have h_in := dehn_twist_in_harmonic G cycle h_embedded h_n_ge_3
  have h_ne := dehn_twist_active_ne_zero G cycle h_embedded h_n_ge_3
  haveI : Nontrivial (HarmonicSubspace G) :=
    ⟨⟨0, Submodule.zero_mem _⟩, ⟨dehn_twist_active cycle G h_embedded, h_in⟩,
     by simp only [ne_eq, Subtype.mk.injEq]; exact fun h => h_ne h.symm⟩
  exact Nat.one_le_iff_ne_zero.mpr (Module.finrank_pos.ne')

end Theorems

section GeneralCycles

/-! ## General Cycles (k ≤ n vertices) -/

/--
A GeneralCycle is a cycle on k distinct vertices within Fin n.
It's represented by a list of vertices where each is adjacent to the next (mod k).
-/
structure GeneralCycle (n : ℕ) where
  /-- The vertices forming the cycle, in order -/
  verts : List (Fin n)
  /-- At least 3 vertices (minimal cycle) -/
  len_ge_3 : verts.length ≥ 3
  /-- All vertices are distinct -/
  nodup : verts.Nodup

/-- Length of the cycle -/
def GeneralCycle.len {n : ℕ} (c : GeneralCycle n) : ℕ := c.verts.length

/-- Get vertex at position i (mod length) -/
def GeneralCycle.vertex {n : ℕ} (c : GeneralCycle n) (i : ℕ) : Fin n :=
  c.verts.get ⟨i % c.verts.length, Nat.mod_lt i (Nat.lt_of_lt_of_le (by omega : 0 < 3) c.len_ge_3)⟩

/-- Next vertex in the cycle -/
def GeneralCycle.nextVertex {n : ℕ} (c : GeneralCycle n) (i : ℕ) : Fin n :=
  c.vertex (i + 1)

/-- A GeneralCycle is embedded in G if all consecutive edges are active -/
def generalCycleEmbeddedIn {n : ℕ} (c : GeneralCycle n) (G : DynamicGraph n) : Prop :=
  ∀ i : Fin c.verts.length, (c.vertex i.val, c.nextVertex i.val) ∈ G.active_edges

/-- Cycle form: 1/k on forward edges, -1/k on reverse, 0 elsewhere. -/
noncomputable def general_cycle_form {n : ℕ} [NeZero n] (c : GeneralCycle n) : C1 n where
  val := fun i j =>
    -- Check if (i,j) is a forward edge of the cycle
    if ∃ k : Fin c.verts.length, c.vertex k.val = i ∧ c.nextVertex k.val = j
    then 1 / c.len
    -- Check if (j,i) is a forward edge (so (i,j) is reverse)
    else if ∃ k : Fin c.verts.length, c.vertex k.val = j ∧ c.nextVertex k.val = i
    then -(1 / c.len)
    else 0
  skew := by
    intro i j
    split_ifs with h1 h2 h3
    · obtain ⟨k1, hk1⟩ := h1
      obtain ⟨k2, hk2⟩ := h2
      exfalso
      have h_len_ge_3 := c.len_ge_3
      have h_len_pos : 0 < c.verts.length := Nat.lt_of_lt_of_le (by omega : 0 < 3) h_len_ge_3
      have h_next_eq : c.nextVertex k1.val = c.vertex k2.val := by rw [hk1.2, hk2.1]
      have h_prev_eq : c.nextVertex k2.val = c.vertex k1.val := by rw [hk2.2, hk1.1]
      unfold GeneralCycle.nextVertex GeneralCycle.vertex at h_next_eq h_prev_eq
      have h_k2_lt : k2.val < c.verts.length := k2.isLt
      have h_k1_lt : k1.val < c.verts.length := k1.isLt
      have h_idx1 : (k1.val + 1) % c.verts.length = k2.val := by
        have := c.nodup.get_inj_iff.mp h_next_eq
        simp only [Fin.ext_iff, Nat.mod_eq_of_lt h_k2_lt] at this
        exact this
      have h_idx2 : (k2.val + 1) % c.verts.length = k1.val := by
        have := c.nodup.get_inj_iff.mp h_prev_eq
        simp only [Fin.ext_iff, Nat.mod_eq_of_lt h_k1_lt] at this
        exact this
      have h_cycle : (k1.val + 2) % c.verts.length = k1.val := by
        have h1_mod : 1 % c.verts.length = 1 := Nat.mod_eq_of_lt (by omega : 1 < c.verts.length)
        have h1 : (k1.val + 2) % c.verts.length = (k2.val + 1) % c.verts.length := by
          conv_lhs => rw [show k1.val + 2 = (k1.val + 1) + 1 from rfl, Nat.add_mod, h_idx1, h1_mod]
        rw [h1, h_idx2]
      cases Nat.lt_or_ge (k1.val + 2) c.verts.length with
      | inl h_small =>
        have := Nat.mod_eq_of_lt h_small
        omega
      | inr h_big =>
        have h_diff_lt : k1.val + 2 - c.verts.length < c.verts.length := by omega
        have h_mod_sub := Nat.mod_eq_sub_mod h_big
        rw [h_mod_sub, Nat.mod_eq_of_lt h_diff_lt] at h_cycle
        omega
    · ring
    · ring
    · ring

/-- The general cycle form is divergence-free. -/
lemma general_cycle_form_harmonic {n : ℕ} [Fintype (Fin n)] [NeZero n] (c : GeneralCycle n) :
    IsHarmonic (general_cycle_form c) := by
  rw [IsHarmonic_iff_divergence_zero]
  funext v
  unfold divergence general_cycle_form
  simp only
  rw [neg_eq_zero]
  by_cases h_in : v ∈ c.verts
  · obtain ⟨idx, hidx⟩ := List.mem_iff_get.mp h_in
    have h_v_eq : c.vertex idx.val = v := by
      unfold GeneralCycle.vertex
      simp only [Nat.mod_eq_of_lt idx.isLt, hidx]
    have h_len_ge_3 := c.len_ge_3
    have h_len_pos : 0 < c.verts.length := Nat.lt_of_lt_of_le (by omega : 0 < 3) h_len_ge_3
    have h_idx_lt : idx.val < c.verts.length := idx.isLt
    have h_prev_idx_val : (idx.val + c.verts.length - 1) % c.verts.length =
        if idx.val = 0 then c.verts.length - 1 else idx.val - 1 := by
      split_ifs with h0
      · simp [h0]
      · have h_ge : idx.val + c.verts.length - 1 ≥ c.verts.length := by
          have : idx.val ≥ 1 := Nat.one_le_iff_ne_zero.mpr h0
          omega
        have h_lt : idx.val + c.verts.length - 1 - c.verts.length < c.verts.length := by omega
        rw [Nat.mod_eq_sub_mod h_ge, Nat.mod_eq_of_lt h_lt]
        omega
    have h_unique_fwd : ∀ k : Fin c.verts.length, c.vertex k.val = v → k = idx := by
      intro k hk
      have := c.nodup.get_inj_iff.mp (by rw [hk, ← h_v_eq] : c.vertex k.val = c.vertex idx.val)
      ext
      simp only [Fin.ext_iff, Nat.mod_eq_of_lt k.isLt, Nat.mod_eq_of_lt idx.isLt] at this
      exact this
    trans (1 / c.len + (-(1 / c.len)))
    · have h_len_ne_zero : (c.len : ℝ) ≠ 0 := by
        simp only [GeneralCycle.len]
        exact Nat.cast_ne_zero.mpr (by omega)
      let x_next := c.nextVertex idx.val
      let prev_idx : Fin c.verts.length := ⟨(idx.val + c.verts.length - 1) % c.verts.length,
        Nat.mod_lt _ h_len_pos⟩
      let x_prev := c.vertex prev_idx.val
      have h_x_next_term : (if ∃ k : Fin c.verts.length, c.vertex k.val = v ∧ c.nextVertex k.val = x_next
                           then (1 : ℝ) / c.len
                           else if ∃ k : Fin c.verts.length, c.vertex k.val = x_next ∧ c.nextVertex k.val = v
                           then -(1 / c.len) else 0) = 1 / c.len := by
        have h_fwd : ∃ k : Fin c.verts.length, c.vertex k.val = v ∧ c.nextVertex k.val = x_next := ⟨idx, h_v_eq, rfl⟩
        simp only [h_fwd, ↓reduceIte]
      have h_prev_next : c.nextVertex prev_idx.val = v := by
        unfold GeneralCycle.nextVertex GeneralCycle.vertex
        have h_mod : (prev_idx.val + 1) % c.verts.length = idx.val := by
          simp only [prev_idx]
          -- Case split on whether idx = 0
          cases Nat.eq_zero_or_pos idx.val with
          | inl h0 =>
            -- idx = 0: prev_idx = len - 1, and (len - 1 + 1) % len = 0 = idx
            rw [h0]
            simp only [zero_add]
            rw [Nat.mod_eq_of_lt (Nat.sub_lt h_len_pos (by omega)), Nat.sub_add_cancel (by omega : 1 ≤ c.verts.length)]
            exact Nat.mod_self _
          | inr h_pos =>
            -- idx > 0: (idx + len - 1) % len = idx - 1, and (idx - 1 + 1) % len = idx
            have h_ge : idx.val + c.verts.length - 1 ≥ c.verts.length := by omega
            have h_sub_lt : idx.val + c.verts.length - 1 - c.verts.length < c.verts.length := by omega
            rw [Nat.mod_eq_sub_mod h_ge, Nat.mod_eq_of_lt h_sub_lt]
            have h_simp : idx.val + c.verts.length - 1 - c.verts.length + 1 = idx.val := by omega
            rw [h_simp, Nat.mod_eq_of_lt h_idx_lt]
        simp only [h_mod, hidx]
      have h_x_prev_term : (if ∃ k : Fin c.verts.length, c.vertex k.val = v ∧ c.nextVertex k.val = x_prev
                           then (1 : ℝ) / c.len
                           else if ∃ k : Fin c.verts.length, c.vertex k.val = x_prev ∧ c.nextVertex k.val = v
                           then -(1 / c.len) else 0) = -(1 / c.len) := by
        have h_no_fwd : ¬∃ k : Fin c.verts.length, c.vertex k.val = v ∧ c.nextVertex k.val = x_prev := by
          intro ⟨k, hk⟩
          have h_k_eq_idx := h_unique_fwd k hk.1
          have h_eq : c.nextVertex k.val = x_prev := hk.2
          rw [h_k_eq_idx] at h_eq
          unfold GeneralCycle.nextVertex GeneralCycle.vertex at h_eq
          have h_indices := c.nodup.get_inj_iff.mp h_eq
          simp only [Fin.ext_iff, prev_idx] at h_indices
          cases Nat.eq_zero_or_pos idx.val with
          | inl h0 =>
            rw [h0] at h_indices
            simp only [zero_add] at h_indices
            have h1_lt : 1 < c.verts.length := by omega
            have h_prev_lt : c.verts.length - 1 < c.verts.length := Nat.sub_lt h_len_pos (by omega)
            rw [Nat.mod_eq_of_lt h1_lt, Nat.mod_eq_of_lt h_prev_lt, Nat.mod_eq_of_lt h_prev_lt] at h_indices
            omega
          | inr h_pos =>
            -- idx > 0: (idx + 1) % len = (idx + len - 1) % len (from h_indices)
            -- But (idx + 1) % len = idx + 1 (if idx + 1 < len) or 0 (if idx + 1 = len)
            -- And (idx + len - 1) % len = idx - 1 (since idx > 0)
            have h_ge : idx.val + c.verts.length - 1 ≥ c.verts.length := by omega
            have h_sub_lt : idx.val + c.verts.length - 1 - c.verts.length < c.verts.length := by omega
            have h_mod_prev : (idx.val + c.verts.length - 1) % c.verts.length =
                              idx.val + c.verts.length - 1 - c.verts.length := by
              rw [Nat.mod_eq_sub_mod h_ge, Nat.mod_eq_of_lt h_sub_lt]
            have h_simp : idx.val + c.verts.length - 1 - c.verts.length = idx.val - 1 := by omega
            rw [h_mod_prev, h_simp] at h_indices
            have h_prev_lt : idx.val - 1 < c.verts.length := by omega
            rw [Nat.mod_eq_of_lt h_prev_lt] at h_indices
            cases Nat.lt_or_ge (idx.val + 1) c.verts.length with
            | inl h_small =>
              rw [Nat.mod_eq_of_lt h_small] at h_indices
              omega
            | inr h_big =>
              have h_idx_max : idx.val = c.verts.length - 1 := by omega
              rw [h_idx_max] at h_indices
              simp only [Nat.sub_add_cancel (by omega : 1 ≤ c.verts.length), Nat.mod_self] at h_indices
              omega
        have h_rev : ∃ k : Fin c.verts.length, c.vertex k.val = x_prev ∧ c.nextVertex k.val = v := ⟨prev_idx, rfl, h_prev_next⟩
        simp only [h_no_fwd, ↓reduceIte, h_rev]
      have h_ne : x_next ≠ x_prev := by
        intro h_eq
        simp only [x_next, x_prev] at h_eq
        unfold GeneralCycle.nextVertex GeneralCycle.vertex at h_eq
        have h_indices := c.nodup.get_inj_iff.mp h_eq
        simp only [Fin.ext_iff, prev_idx] at h_indices
        cases Nat.eq_zero_or_pos idx.val with
        | inl h0 =>
          rw [h0] at h_indices
          simp only [zero_add] at h_indices
          have h1_lt : 1 < c.verts.length := by omega
          have h_prev_lt : c.verts.length - 1 < c.verts.length := Nat.sub_lt h_len_pos (by omega)
          rw [Nat.mod_eq_of_lt h1_lt] at h_indices
          simp only [Nat.mod_mod] at h_indices
          rw [Nat.mod_eq_of_lt h_prev_lt] at h_indices
          omega
        | inr h_pos =>
          have h_ge : idx.val + c.verts.length - 1 ≥ c.verts.length := by omega
          have h_sub_lt : idx.val + c.verts.length - 1 - c.verts.length < c.verts.length := by omega
          have h_mod_prev : (idx.val + c.verts.length - 1) % c.verts.length =
                            idx.val + c.verts.length - 1 - c.verts.length := by
            rw [Nat.mod_eq_sub_mod h_ge, Nat.mod_eq_of_lt h_sub_lt]
          have h_simp : idx.val + c.verts.length - 1 - c.verts.length = idx.val - 1 := by omega
          rw [h_mod_prev, h_simp] at h_indices
          have h_prev_lt : idx.val - 1 < c.verts.length := by omega
          rw [Nat.mod_eq_of_lt h_prev_lt] at h_indices
          cases Nat.lt_or_ge (idx.val + 1) c.verts.length with
          | inl h_small => rw [Nat.mod_eq_of_lt h_small] at h_indices; omega
          | inr h_big =>
            have h_idx_max : idx.val = c.verts.length - 1 := by omega
            rw [h_idx_max] at h_indices
            simp only [Nat.sub_add_cancel (by omega : 1 ≤ c.verts.length), Nat.mod_self] at h_indices
            omega
      -- All other x contribute 0
      have h_other_zero : ∀ x, x ≠ x_next → x ≠ x_prev →
          (if ∃ k : Fin c.verts.length, c.vertex k.val = v ∧ c.nextVertex k.val = x
           then (1 : ℝ) / c.len
           else if ∃ k : Fin c.verts.length, c.vertex k.val = x ∧ c.nextVertex k.val = v
           then -(1 / c.len) else 0) = 0 := by
        intro x hx_ne_next hx_ne_prev
        have h_no_fwd : ¬∃ k : Fin c.verts.length, c.vertex k.val = v ∧ c.nextVertex k.val = x := by
          intro ⟨k, hk⟩
          have h_k_eq := h_unique_fwd k hk.1
          rw [h_k_eq] at hk
          exact hx_ne_next hk.2.symm
        have h_no_rev : ¬∃ k : Fin c.verts.length, c.vertex k.val = x ∧ c.nextVertex k.val = v := by
          intro ⟨k, hk⟩
          have h1 : c.nextVertex k.val = c.vertex idx.val := by rw [hk.2, h_v_eq]
          unfold GeneralCycle.nextVertex GeneralCycle.vertex at h1
          have h2 := c.nodup.get_inj_iff.mp h1
          simp only [Fin.ext_iff, Nat.mod_eq_of_lt h_idx_lt] at h2
          have h3 : k.val = prev_idx.val := by
            simp only [prev_idx]
            cases Nat.eq_zero_or_pos idx.val with
            | inl h0 =>
              rw [h0] at h2
              have hk_lt := k.isLt
              have hk_plus_1_mod : (k.val + 1) % c.verts.length = 0 := h2
              cases Nat.lt_or_ge (k.val + 1) c.verts.length with
              | inl h_small =>
                rw [Nat.mod_eq_of_lt h_small] at hk_plus_1_mod
                omega
              | inr h_big =>
                have hk_max : k.val = c.verts.length - 1 := by omega
                rw [h0]
                simp only [zero_add]
                rw [hk_max]
                exact (Nat.mod_eq_of_lt (Nat.sub_lt h_len_pos (by omega))).symm
            | inr h_pos =>
              cases Nat.lt_or_ge (k.val + 1) c.verts.length with
              | inl h_k_small =>
                have hk_eq : k.val + 1 = idx.val := by
                  rw [Nat.mod_eq_of_lt h_k_small] at h2; exact h2
                have hk_val : k.val = idx.val - 1 := by omega
                have h_prev_simp : (idx.val + c.verts.length - 1) % c.verts.length = idx.val - 1 := by
                  have h_ge : idx.val + c.verts.length - 1 ≥ c.verts.length := by omega
                  rw [Nat.mod_eq_sub_mod h_ge]
                  have h_eq : idx.val + c.verts.length - 1 - c.verts.length = idx.val - 1 := by omega
                  rw [h_eq]
                  exact Nat.mod_eq_of_lt (by omega)
                rw [hk_val, h_prev_simp]
              | inr h_k_big =>
                have hk_max : k.val = c.verts.length - 1 := by omega
                have h_mod_zero : (k.val + 1) % c.verts.length = 0 := by
                  rw [hk_max, Nat.sub_add_cancel (by omega : 1 ≤ c.verts.length), Nat.mod_self]
                rw [h_mod_zero] at h2
                omega
          have h4 : x = c.vertex prev_idx.val := by rw [← h3]; exact hk.1.symm
          exact hx_ne_prev h4
        simp only [h_no_fwd, h_no_rev, ↓reduceIte]
      -- Rewrite sum using the three cases
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x_next)]
      rw [h_x_next_term]
      congr 1
      rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h_ne.symm, Finset.mem_univ x_prev⟩)]
      rw [h_x_prev_term]
      have h_sum_zero : ∑ x ∈ (Finset.univ.erase x_next).erase x_prev,
          (if ∃ k : Fin c.verts.length, c.vertex k.val = v ∧ c.nextVertex k.val = x
           then (1 : ℝ) / c.len
           else if ∃ k : Fin c.verts.length, c.vertex k.val = x ∧ c.nextVertex k.val = v
           then -(1 / c.len) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        simp only [Finset.mem_erase] at hx
        exact h_other_zero x hx.2.1 hx.1
      rw [h_sum_zero, add_zero]
    · ring
  · apply Finset.sum_eq_zero
    intro x _
    have h_no_fwd : ¬∃ k : Fin c.verts.length, c.vertex k.val = v ∧ c.nextVertex k.val = x := by
      intro ⟨k, hk⟩
      apply h_in
      rw [← hk.1]
      unfold GeneralCycle.vertex
      exact List.get_mem c.verts _
    have h_no_rev : ¬∃ k : Fin c.verts.length, c.vertex k.val = x ∧ c.nextVertex k.val = v := by
      intro ⟨k, hk⟩
      apply h_in
      rw [← hk.2]
      unfold GeneralCycle.nextVertex GeneralCycle.vertex
      exact List.get_mem c.verts _
    simp only [h_no_fwd, h_no_rev, ↓reduceIte]

/-- The general cycle form has positive energy. -/
lemma general_cycle_form_positive_energy {n : ℕ} [Fintype (Fin n)] [NeZero n] (c : GeneralCycle n) :
    norm_sq (general_cycle_form c) > 0 := by
  unfold norm_sq inner_product_C1 general_cycle_form
  have h_len_ge_3 := c.len_ge_3
  have h_len_pos : (0 : ℝ) < c.len := by simp only [GeneralCycle.len]; positivity
  have h_sq_pos : (1 / c.len : ℝ)^2 > 0 := by positivity
  apply mul_pos (by norm_num : (1:ℝ)/2 > 0)
  apply Finset.sum_pos'
  · intro i _
    apply Finset.sum_nonneg
    intro j _
    apply mul_self_nonneg
  · use c.vertex 0, Finset.mem_univ _
    apply Finset.sum_pos'
    · intro j _
      apply mul_self_nonneg
    · have h_0_lt : 0 < c.verts.length := Nat.lt_of_lt_of_le (by omega : 0 < 3) h_len_ge_3
      use c.nextVertex 0, Finset.mem_univ _
      simp only
      have h_fwd : ∃ k : Fin c.verts.length, c.vertex k.val = c.vertex 0 ∧ c.nextVertex k.val = c.nextVertex 0 := by
        use ⟨0, h_0_lt⟩
      simp only [h_fwd, ↓reduceIte]
      have : (1 / ↑c.len) * (1 / ↑c.len) = (1 / c.len : ℝ)^2 := by ring
      rw [this]
      exact h_sq_pos

/-- Any cycle embedded in G creates nonzero harmonic form. -/
theorem general_cycle_creates_mass {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (G : DynamicGraph n) (c : GeneralCycle n)
    (h_embedded : generalCycleEmbeddedIn c G) :
    Module.finrank ℝ (HarmonicSubspace G) ≥ 1 := by
  have h_supported : ∀ i j, (i, j) ∉ G.active_edges → (general_cycle_form c).val i j = 0 := by
    intro i j h_not_active
    unfold general_cycle_form
    simp only
    split_ifs with h1 h2
    · exfalso
      obtain ⟨k, hk⟩ := h1
      apply h_not_active
      rw [← hk.1, ← hk.2]
      exact h_embedded ⟨k.val, k.isLt⟩
    · exfalso
      obtain ⟨k, hk⟩ := h2
      apply h_not_active
      have h_fwd : (c.vertex k.val, c.nextVertex k.val) ∈ G.active_edges := h_embedded ⟨k.val, k.isLt⟩
      rw [← hk.1, ← hk.2]
      exact (G.symmetric _ _).mp h_fwd
    · rfl
  let γ : ActiveForm G := ⟨general_cycle_form c, h_supported⟩
  have h_γ_ne : γ ≠ 0 := by
    intro h_zero
    have h_pos := general_cycle_form_positive_energy c
    have h_val : γ.val = general_cycle_form c := rfl
    rw [h_zero] at h_val
    have h_eq_zero : general_cycle_form c = ⟨fun _ _ => 0, by intro i j; ring⟩ := by
      ext i j
      have : (0 : ActiveForm G).val.val i j = 0 := rfl
      rw [← h_val]
      exact this
    unfold norm_sq inner_product_C1 at h_pos
    rw [h_eq_zero] at h_pos
    simp at h_pos
  have h_in_harm : γ ∈ HarmonicSubspace G := by
    rw [HarmonicSubspace, Submodule.mem_orthogonal]
    intro σ hσ
    obtain ⟨φ, hφ⟩ := LinearMap.mem_range.mp hσ
    rw [← hφ]
    have h_harm : IsHarmonic (general_cycle_form c) := general_cycle_form_harmonic c
    show Diaspora.Core.ActiveForm.inner (d_G_linear G φ) γ = 0
    unfold Diaspora.Core.ActiveForm.inner
    have h_eq : inner_product_C1 (d_G_linear G φ).val (general_cycle_form c) =
                inner_product_C1 (d0 φ) (general_cycle_form c) := by
      unfold inner_product_C1
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases h_cycle : (general_cycle_form c).val i j = 0
      · simp [h_cycle]
      · have h_active : (i, j) ∈ G.active_edges := by
          by_contra h_not
          exact h_cycle (h_supported i j h_not)
        show (d_G_linear G φ).val.val i j * _ = (d0 φ).val i j * _
        unfold d_G_linear d_G d0
        simp only [LinearMap.coe_mk, AddHom.coe_mk, h_active, ↓reduceIte]
    rw [h_eq]
    rw [divergence_is_adjoint]
    have h_div_zero : divergence (general_cycle_form c) = fun _ => 0 := by
      rw [← IsHarmonic_iff_divergence_zero]
      exact h_harm
    simp [h_div_zero]
  haveI : Nontrivial (HarmonicSubspace G) :=
    ⟨⟨0, Submodule.zero_mem _⟩, ⟨γ, h_in_harm⟩, by simp only [ne_eq, Subtype.mk.injEq]; exact fun h => h_γ_ne h.symm⟩
  exact Nat.one_le_iff_ne_zero.mpr Module.finrank_pos.ne'

/-- Construct a GeneralCycle from an IsCycle walk. -/
noncomputable def GeneralCycle.ofIsCycle {n : ℕ} {G : DynamicGraph n} {v : Fin n}
    (w : (DynamicGraph.toSimpleGraph G).Walk v v) (h_cycle : w.IsCycle) : GeneralCycle n where
  verts := w.support.dropLast
  len_ge_3 := by
    rw [List.length_dropLast, SimpleGraph.Walk.length_support]
    have h := h_cycle.three_le_length
    omega
  nodup := by
    have h_tail_nodup := h_cycle.support_nodup
    have h_support_eq : w.support = v :: w.support.tail := w.support_eq_cons
    have h_len_ge_3 := h_cycle.three_le_length
    have h_tail_ne_nil : w.support.tail ≠ [] := by
      intro h
      have h_len := SimpleGraph.Walk.length_support w
      rw [h_support_eq, h] at h_len
      simp only [List.length_cons, List.length_nil] at h_len
      omega
    -- dropLast support = v :: dropLast (tail)
    have h_dropLast_eq : w.support.dropLast = v :: w.support.tail.dropLast := by
      conv_lhs => rw [h_support_eq]
      exact List.dropLast_cons_of_ne_nil h_tail_ne_nil
    rw [h_dropLast_eq, List.nodup_cons]
    refine ⟨?_, h_tail_nodup.sublist (List.dropLast_sublist _)⟩
    intro h_mem
    have h_last_support : w.support.getLast (SimpleGraph.Walk.support_ne_nil w) = v :=
      SimpleGraph.Walk.getLast_support w
    have h_last_tail : w.support.tail.getLast h_tail_ne_nil = v := by
      have h1 : (v :: w.support.tail).getLast (List.cons_ne_nil _ _) = w.support.tail.getLast h_tail_ne_nil :=
        List.getLast_cons h_tail_ne_nil
      have h2 : w.support.getLast (SimpleGraph.Walk.support_ne_nil w) =
                (v :: w.support.tail).getLast (List.cons_ne_nil _ _) := by
        congr 1
      rw [← h2, h_last_support] at h1
      exact h1.symm
    have h_decomp : w.support.tail = w.support.tail.dropLast ++ [v] := by
      conv_lhs => rw [← List.dropLast_append_getLast h_tail_ne_nil, h_last_tail]
    have : ¬w.support.tail.Nodup := by
      rw [h_decomp, List.nodup_append]
      push_neg
      intro _ _
      exact ⟨v, h_mem, v, List.mem_singleton_self v, rfl⟩
    exact this h_tail_nodup

/-- The GeneralCycle from an IsCycle walk is embedded in G. -/
lemma GeneralCycle.ofIsCycle_embedded {n : ℕ} {G : DynamicGraph n} {v : Fin n}
    (w : (DynamicGraph.toSimpleGraph G).Walk v v) (h_cycle : w.IsCycle) :
    generalCycleEmbeddedIn (GeneralCycle.ofIsCycle w h_cycle) G := by
  intro ⟨i, hi⟩
  let c := GeneralCycle.ofIsCycle w h_cycle
  have h_len : c.verts.length = w.length := by
    simp only [c, GeneralCycle.ofIsCycle, List.length_dropLast, SimpleGraph.Walk.length_support]
    omega
  have hi' : i < w.length := by rw [← h_len]; exact hi
  have h_len_pos : 0 < w.length := Nat.lt_of_lt_of_le (by omega : 0 < 3) h_cycle.three_le_length
  have h_mod_i : i % c.verts.length = i := Nat.mod_eq_of_lt hi
  have h_vertex_eq : c.vertex i = w.getVert i := by
    unfold GeneralCycle.vertex
    simp only [c, GeneralCycle.ofIsCycle, List.get_eq_getElem]
    have hi_drop : i < w.support.dropLast.length := by
      simp only [List.length_dropLast, SimpleGraph.Walk.length_support]; omega
    have h_mod_drop : i % w.support.dropLast.length = i := Nat.mod_eq_of_lt hi_drop
    simp only [h_mod_drop, List.getElem_dropLast, ← SimpleGraph.Walk.getVert_eq_support_getElem w (by omega : i ≤ w.length)]
  by_cases h_wrap : i + 1 < w.length
  · have h_next : (i + 1) % c.verts.length = i + 1 := by rw [h_len]; exact Nat.mod_eq_of_lt h_wrap
    have h_next_eq : c.nextVertex i = w.getVert (i + 1) := by
      unfold GeneralCycle.nextVertex GeneralCycle.vertex
      simp only [c, GeneralCycle.ofIsCycle, List.get_eq_getElem]
      have hi1_drop : i + 1 < w.support.dropLast.length := by
        simp only [List.length_dropLast, SimpleGraph.Walk.length_support]; omega
      have h_mod_drop : (i + 1) % w.support.dropLast.length = i + 1 := Nat.mod_eq_of_lt hi1_drop
      simp only [h_mod_drop, List.getElem_dropLast, ← SimpleGraph.Walk.getVert_eq_support_getElem w (by omega : i + 1 ≤ w.length)]
    rw [h_vertex_eq, h_next_eq]
    exact SimpleGraph.Walk.adj_getVert_succ w hi'
  · have h_i_eq : i = w.length - 1 := by omega
    have h_next : (i + 1) % c.verts.length = 0 := by
      rw [h_len, h_i_eq, Nat.sub_add_cancel (by omega : 1 ≤ w.length), Nat.mod_self]
    have h_next_eq : c.nextVertex i = v := by
      unfold GeneralCycle.nextVertex GeneralCycle.vertex
      simp only [c, GeneralCycle.ofIsCycle, List.get_eq_getElem]
      -- The index is (i + 1) % w.support.dropLast.length, which equals 0
      have h_mod_drop : (i + 1) % w.support.dropLast.length = 0 := by
        simp only [List.length_dropLast, SimpleGraph.Walk.length_support]
        have h1 : w.length + 1 - 1 = w.length := Nat.add_sub_cancel w.length 1
        rw [h1]
        have h2 : i + 1 = w.length := by omega
        rw [h2, Nat.mod_self]
      simp only [h_mod_drop, List.getElem_dropLast]
      have h2 : w.support[0]'(by rw [SimpleGraph.Walk.length_support]; omega) = v := by
        have := SimpleGraph.Walk.head_support w
        simp only [List.head_eq_getElem] at this
        exact this
      exact h2
    rw [h_vertex_eq, h_next_eq, h_i_eq]
    have h_adj := SimpleGraph.Walk.adj_getVert_succ w (by omega : w.length - 1 < w.length)
    simp only [Nat.sub_add_cancel (by omega : 1 ≤ w.length)] at h_adj
    rw [SimpleGraph.Walk.getVert_length w] at h_adj
    exact h_adj

/-- If G.toSimpleGraph has a cycle, then ¬IsClassical G. -/
theorem cycle_walk_implies_nonclassical {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (G : DynamicGraph n) {v : Fin n}
    (w : (DynamicGraph.toSimpleGraph G).Walk v v) (h_cycle : w.IsCycle) :
    ¬ IsClassical G := by
  let c := GeneralCycle.ofIsCycle w h_cycle
  have h_embedded := GeneralCycle.ofIsCycle_embedded w h_cycle
  have h_mass := general_cycle_creates_mass G c h_embedded
  intro h_class
  unfold IsClassical at h_class
  omega

set_option linter.unusedSectionVars false in
/-- Classical universes have no cycles: dim(H) = 0 ⟹ acyclic. -/
theorem classical_implies_acyclic [DecidableEq (Fin n)] [NeZero n]
    (G : DynamicGraph n) (h_class : IsClassical G) :
    (DynamicGraph.toSimpleGraph G).IsAcyclic := by
  intro v w h_cycle
  exact cycle_walk_implies_nonclassical G w h_cycle h_class

/-- Canonical height: distance from vertex 0. -/
noncomputable def canonical_height [NeZero n] (G : DynamicGraph n) : C0 n :=
  fun v => (DynamicGraph.toSimpleGraph G).dist ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ v

set_option linter.unusedSectionVars false in
/-- In a tree, adjacent vertices have distances differing by 1. -/
lemma tree_adjacent_dist_diff [NeZero n] {G : SimpleGraph (Fin n)}
    (h_acyclic : G.IsAcyclic) (h_conn : G.Connected)
    {u v : Fin n} (h_adj : G.Adj u v) (r : Fin n) :
    G.dist r u + 1 = G.dist r v ∨ G.dist r v + 1 = G.dist r u := by
  have h_diff := h_conn.diff_dist_adj (u := r) h_adj
  have h_ne : G.dist r u ≠ G.dist r v := by
    intro h_eq
    have h_u_ne_v : u ≠ v := h_adj.ne
    obtain ⟨p_ru, hp_ru⟩ := (h_conn r u).exists_walk_length_eq_dist
    obtain ⟨p_rv, hp_rv⟩ := (h_conn r v).exists_walk_length_eq_dist
    by_cases hv_on : v ∈ p_ru.support
    · have h_spec := p_ru.take_spec hv_on
      have h_len_add : (p_ru.takeUntil v hv_on).length + (p_ru.dropUntil v hv_on).length = p_ru.length := by
        calc (p_ru.takeUntil v hv_on).length + (p_ru.dropUntil v hv_on).length
            = ((p_ru.takeUntil v hv_on).append (p_ru.dropUntil v hv_on)).length := by
                rw [SimpleGraph.Walk.length_append]
          _ = p_ru.length := by rw [h_spec]
      have h_dist_rv : G.dist r v ≤ (p_ru.takeUntil v hv_on).length := SimpleGraph.dist_le _
      have h_dist_vu : G.dist v u ≤ (p_ru.dropUntil v hv_on).length := SimpleGraph.dist_le _
      have hadj_dist : G.dist v u = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h_adj.symm
      have h_tri := h_conn.dist_triangle (u := r) (v := v) (w := u)
      omega
    · let w_ruv := p_ru.append (SimpleGraph.Walk.cons h_adj SimpleGraph.Walk.nil)
      have h_len : w_ruv.length = G.dist r u + 1 := by
        simp [w_ruv, hp_ru]
      have h_le := SimpleGraph.dist_le w_ruv
      by_cases hu_on : u ∈ p_rv.support
      · have h_spec := p_rv.take_spec hu_on
        have h_len_add : (p_rv.takeUntil u hu_on).length + (p_rv.dropUntil u hu_on).length = p_rv.length := by
          calc (p_rv.takeUntil u hu_on).length + (p_rv.dropUntil u hu_on).length
              = ((p_rv.takeUntil u hu_on).append (p_rv.dropUntil u hu_on)).length := by
                  rw [SimpleGraph.Walk.length_append]
            _ = p_rv.length := by rw [h_spec]
        have h_dist_ru : G.dist r u ≤ (p_rv.takeUntil u hu_on).length := SimpleGraph.dist_le _
        have h_dist_uv : G.dist u v ≤ (p_rv.dropUntil u hu_on).length := SimpleGraph.dist_le _
        have hadj_dist : G.dist u v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h_adj
        have h_tri := h_conn.dist_triangle (u := r) (v := u) (w := v)
        omega
      · have hp_ru_path : p_ru.IsPath := p_ru.isPath_of_length_eq_dist hp_ru
        have hp_rv_path : p_rv.IsPath := p_rv.isPath_of_length_eq_dist hp_rv
        let w_ruv := p_ru.concat h_adj
        have hw_path : w_ruv.IsPath := by
          rw [SimpleGraph.Walk.concat_isPath_iff]
          exact ⟨hp_ru_path, hv_on⟩
        let path1 : G.Path r v := ⟨p_rv, hp_rv_path⟩
        let path2 : G.Path r v := ⟨w_ruv, hw_path⟩
        have h_uniq := h_acyclic.path_unique path1 path2
        have h_len1 : p_rv.length = G.dist r v := hp_rv
        have h_len2 : w_ruv.length = G.dist r u + 1 := by simp [w_ruv, hp_ru]
        have h_walks_eq : p_rv = w_ruv := congrArg Subtype.val h_uniq
        have h_lens_eq : p_rv.length = w_ruv.length := congrArg SimpleGraph.Walk.length h_walks_eq
        omega
  omega

/-- Classical connected universes admit intrinsic hierarchy via graph distance. -/
theorem classical_universe_admits_intrinsic_hierarchy [NeZero n] [DecidableEq (Fin n)]
    (G : DynamicGraph n) (h_class : IsClassical G)
    (h_conn : (DynamicGraph.toSimpleGraph G).Connected) :
    IsFaithfulPotential G (canonical_height G) ∧ WellFounded (IsMember G (canonical_height G)) := by
  have h_acyclic := classical_implies_acyclic G h_class
  constructor
  · intro i j h_edge
    unfold canonical_height
    simp only [ne_eq, Nat.cast_inj]
    have h_adj : (DynamicGraph.toSimpleGraph G).Adj i j := h_edge
    have h_diff := tree_adjacent_dist_diff h_acyclic h_conn h_adj ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    omega
  · exact isMember_wellFounded G _

/-- Extrinsic version using vertex indices. -/
theorem classical_universe_admits_rank [NeZero n] (G : DynamicGraph n) (_h_class : IsClassical G) :
    ∃ (ϕ : C0 n), IsFaithfulPotential G ϕ ∧ WellFounded (IsMember G ϕ) := by
  use fun v => v.val
  constructor
  · intro i j h_edge
    have h_ne : i ≠ j := fun h_eq => G.no_loops i (h_eq ▸ h_edge)
    simp only [ne_eq, Nat.cast_inj]
    exact Fin.val_ne_of_ne h_ne
  · exact isMember_wellFounded G _

/-- Classical universes admit no paradoxes: every ActiveForm is exact. -/
theorem classical_universe_admits_no_paradoxes [DecidableEq (Fin n)]
    (G : DynamicGraph n) (h_class : IsClassical G) :
    ∀ σ : ActiveForm G, σ ∈ ImGradient G := by
  intro σ
  have h_decomp := hodge_decomposition_graph G σ
  obtain ⟨ϕ, γ, h_eq, h_harm, _⟩ := h_decomp
  have h_zero : γ = 0 := by
    have h_all_zero := finrank_zero_iff_forall_zero.mp h_class
    exact Subtype.ext_iff.mp (h_all_zero ⟨γ, h_harm⟩)
  rw [h_zero, add_zero] at h_eq
  rw [ImGradient, LinearMap.mem_range]
  exact ⟨ϕ, h_eq.symm⟩

end GeneralCycles

end Diaspora.Logic
