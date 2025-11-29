/-
# Phase Fields

Discrete calculus over finite cyclic groups (ZMod k).

In the real-valued theory, winding numbers emerge as holonomies that happen
to be integers. In the phase field theory, winding is enforced by the type
system: you can't partially have a winding.
-/

import Diaspora.Hodge.Harmonic
import Mathlib.Data.ZMod.Basic

open BigOperators Diaspora.Hodge

namespace Diaspora.Core

/-! ## Geodesic Distance -/

/-- Geodesic distance on ZMod k: shortest path on the cycle.
    dist(0, k-1) = 1, not k-1. -/
def geodesic_dist {k : ℕ} [NeZero k] (a b : ZMod k) : ℕ :=
  let diff := (a - b).val
  min diff (k - diff)

/-- Geodesic distance from a to 0 equals distance from -a to 0. -/
lemma geodesic_dist_neg {k : ℕ} [NeZero k] (a : ZMod k) :
    geodesic_dist (-a) 0 = geodesic_dist a 0 := by
  unfold geodesic_dist
  simp only [sub_zero]
  by_cases h : a = 0
  · simp [h]
  · rw [ZMod.neg_val, if_neg h]
    have h_lt : a.val < k := a.val_lt
    rw [Nat.sub_sub_self (Nat.le_of_lt h_lt), min_comm]

/-! ## Phase Cochains -/

/-- Phase 0-cochain: values in ZMod k (finite cyclic group) -/
abbrev PC0 (n k : ℕ) := Fin n → ZMod k

/-- Phase 1-cochain: skew-symmetric function with values in ZMod k -/
structure PC1 (n k : ℕ) where
  val : Fin n → Fin n → ZMod k
  skew : ∀ i j, val i j = -val j i

/-! ## Phase Coboundary -/

/-- Phase coboundary operator: pd0(ϕ) i j = ϕ j - ϕ i in ZMod k -/
def pd0 {n k : ℕ} (ϕ : PC0 n k) : PC1 n k := {
  val := fun i j => ϕ j - ϕ i
  skew := by intro i j; ring
}

/-- A phase 1-cochain is exact if it's in the image of pd0 -/
def PC1.IsExact {n k : ℕ} (σ : PC1 n k) : Prop :=
  ∃ ϕ : PC0 n k, σ = pd0 ϕ

/-! ## Phase Winding (Holonomy) -/

/-- Phase winding: evaluation of phase 1-cochain on a 1-chain.
    Since coefficients are integers and values are in ZMod k, the result is in ZMod k. -/
noncomputable def phase_winding {n k : ℕ} [NeZero k] [Fintype (Fin n)]
    (σ : PC1 n k) (c : Chain1 n) : ZMod k :=
  ∑ i : Fin n, ∑ j : Fin n,
    if c.coeff i j > 0 then (c.coeff i j).toNat • σ.val i j else 0

/-- Simpler winding for simple cycles: just sum along the cycle direction -/
noncomputable def phase_winding_simple {n k : ℕ} [Fintype (Fin n)]
    (σ : PC1 n k) (cycle : SimpleCycle n) : ZMod k :=
  ∑ i : Fin n, σ.val i (cycle.next i)

/-! ## Basic Properties -/

/-- Zero phase 1-cochain -/
def PC1.zero (n k : ℕ) : PC1 n k := {
  val := fun _ _ => 0
  skew := by intro i j; ring
}

/-- Addition of phase 1-cochains -/
def PC1.add {n k : ℕ} (σ τ : PC1 n k) : PC1 n k := {
  val := fun i j => σ.val i j + τ.val i j
  skew := by intro i j; rw [σ.skew, τ.skew]; ring
}

/-- Negation of phase 1-cochains -/
def PC1.neg {n k : ℕ} (σ : PC1 n k) : PC1 n k where
  val := fun i j => -σ.val i j
  skew i j := by rw [σ.skew]

instance {n k : ℕ} : Zero (PC1 n k) := ⟨PC1.zero n k⟩
instance {n k : ℕ} : Add (PC1 n k) := ⟨PC1.add⟩
instance {n k : ℕ} : Neg (PC1 n k) := ⟨PC1.neg⟩

/-! ## Phase Stokes Theorem -/

/-- Key lemma: For exact forms, the telescoping sum around a cycle vanishes.
    This is the phase-field Stokes theorem. -/
lemma phase_exact_telescope {n k : ℕ} [Fintype (Fin n)]
    (ϕ : PC0 n k) (cycle : SimpleCycle n) :
    ∑ i : Fin n, (pd0 ϕ).val i (cycle.next i) = 0 := by
  unfold pd0
  simp only
  have h_split : ∑ i : Fin n, (ϕ (cycle.next i) - ϕ i) =
                 ∑ i : Fin n, ϕ (cycle.next i) - ∑ i : Fin n, ϕ i :=
    Finset.sum_sub_distrib (s := Finset.univ) (f := fun i => ϕ (cycle.next i)) (g := ϕ)
  rw [h_split]
  let e : Fin n ≃ Fin n := Equiv.ofBijective cycle.next
    (Finite.injective_iff_bijective.mp cycle.next_injective)
  have h_sum : ∑ i : Fin n, ϕ (cycle.next i) = ∑ i : Fin n, ϕ i := by
    have : ∑ i : Fin n, ϕ (e i) = ∑ i : Fin n, ϕ i := Equiv.sum_comp e ϕ
    convert this using 2
  rw [h_sum]
  exact sub_self _

/-- Phase Stokes theorem: exact forms have zero winding on simple cycles -/
theorem phase_exact_vanishes_on_simple_cycles {n k : ℕ} [Fintype (Fin n)]
    (ϕ : PC0 n k) (cycle : SimpleCycle n) :
    phase_winding_simple (pd0 ϕ) cycle = 0 := by
  unfold phase_winding_simple
  exact phase_exact_telescope ϕ cycle

/-! ## Topological Invariance of Winding -/

/-- Two phase 1-cochains differ by an exact form -/
def DiffersByExact {n k : ℕ} (σ τ : PC1 n k) : Prop :=
  ∃ ϕ : PC0 n k, ∀ i j, σ.val i j = τ.val i j + (pd0 ϕ).val i j

/-- Winding number is a topological invariant: adding an exact form doesn't change it -/
theorem winding_number_is_topological_invariant {n k : ℕ} [Fintype (Fin n)]
    (σ : PC1 n k) (ϕ : PC0 n k) (cycle : SimpleCycle n) :
    phase_winding_simple (PC1.add σ (pd0 ϕ)) cycle = phase_winding_simple σ cycle := by
  unfold phase_winding_simple PC1.add
  simp only
  rw [show ∑ i, (σ.val i (cycle.next i) + (pd0 ϕ).val i (cycle.next i)) =
          ∑ i, σ.val i (cycle.next i) + ∑ i, (pd0 ϕ).val i (cycle.next i)
      from Finset.sum_add_distrib]
  rw [phase_exact_telescope ϕ cycle]
  ring

/-- Corollary: forms differing by exact terms have the same winding -/
theorem winding_depends_only_on_cohomology_class {n k : ℕ} [Fintype (Fin n)]
    (σ τ : PC1 n k) (cycle : SimpleCycle n)
    (h : DiffersByExact σ τ) :
    phase_winding_simple σ cycle = phase_winding_simple τ cycle := by
  obtain ⟨ϕ, h_diff⟩ := h
  unfold phase_winding_simple
  have h_eq : ∀ i, σ.val i (cycle.next i) = τ.val i (cycle.next i) + (pd0 ϕ).val i (cycle.next i) :=
    fun i => h_diff i (cycle.next i)
  simp_rw [h_eq]
  have h_split : ∑ i, (τ.val i (cycle.next i) + (pd0 ϕ).val i (cycle.next i)) =
                 ∑ i, τ.val i (cycle.next i) + ∑ i, (pd0 ϕ).val i (cycle.next i) :=
    Finset.sum_add_distrib (s := Finset.univ)
  rw [h_split]
  rw [phase_exact_telescope ϕ cycle]
  ring

end Diaspora.Core
