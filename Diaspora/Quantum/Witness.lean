/-
# The Local Witness Theorem

Parallel transport along a cycle recovers the global harmonic form magnitude.
-/

import Diaspora.Quantum.Measurement
import Diaspora.Hodge.Harmonic
import Diaspora.Logic.Universal
import Diaspora.Logic.WalkHolonomy
import Diaspora.Hodge.Twist
import Mathlib.Analysis.SpecialFunctions.Complex.Log

open Complex Diaspora.Core Diaspora.Hodge Diaspora.Logic

namespace Diaspora.Quantum

open Diaspora.Logic.Universal Diaspora.Logic.WalkHolonomy

/-! ## 1. The Rigorous Walker -/

/--
The phase shift measured by an observer walking along a path `w`.
Defined as the complex exponential of the accumulated potential drops (`walk_sum`).
-/
noncomputable def measure_phase_shift {n : ℕ} (G : DynamicGraph n) (σ : ActiveForm G)
    {u v : Fin n} (w : (DynamicGraph.toSimpleGraph G).Walk u v) : ℂ :=
  cexp (I * (walk_sum G σ w : ℂ))

/-! ## 2. The Equivalence Theorem -/

/--
**The Witness Theorem**:
A local observer walking around a cycle can determine the global energy of a topological defect.

This version uses the rigorous `walk_sum` and `canonical_cycle_walk`.
The proof relies on `walk_sum_factors_through_harmonic` (Stokes' theorem for walks)
to show that exact fluctuations `d0 ϕ` are invisible to the observer.
-/
theorem local_holonomy_predicts_global_energy {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (G : DynamicGraph n)
    (cycle : SimpleCycle n)
    (h_embedded : cycleEmbeddedIn cycle G)
    (σ : ActiveForm G)
    (γ : ActiveForm G)
    (h_decomp : ∃ ϕ, σ = d_G G ϕ + γ)
    (h_harm : IsHarmonic γ.val)
    (h_support : SupportedOnCycle cycle γ.val)
    (h_n_ge_3 : n ≥ 3)
    (v : Fin n)
    (Z : ℂ) (h_measure : Z = measure_phase_shift G σ (canonical_cycle_walk cycle G h_embedded v))
    (h_branch : -Real.pi < holonomy γ.val cycle.toChain1 ∧ holonomy γ.val cycle.toChain1 ≤ Real.pi) :
    norm_sq γ.val = (Complex.log Z / I).re ^ 2 / (Fintype.card (Fin n)) := by
  -- 1. Simplify the measurement using Stokes' Theorem for walks
  have h_Z_pure : Z = cexp (I * (walk_sum G γ (canonical_cycle_walk cycle G h_embedded v) : ℂ)) := by
    rw [h_measure, measure_phase_shift]
    obtain ⟨ϕ, h_eq⟩ := h_decomp
    rw [h_eq]
    -- walk_sum (dφ + γ) = walk_sum γ because dφ vanishes on closed loops
    rw [walk_sum_add, exact_walk_closed, zero_add]

  -- 2. Convert walk_sum to algebraic sum using WalkHolonomy
  have h_walk_eq_sum : walk_sum G γ (canonical_cycle_walk cycle G h_embedded v) =
      ∑ i ∈ Finset.range n, γ.val.val (cycle.next^[i] v) (cycle.next^[i + 1] v) := by
    apply walk_holonomy_eq_sum

  -- 3. Relate algebraic sum to standard Holonomy
  -- Since γ is harmonic on a simple cycle, it is constant k on edges.
  haveI : Inhabited (Fin n) := ⟨v⟩
  obtain ⟨k, h_const⟩ := harmonic_constant_on_simple_cycle cycle γ.val h_harm h_support
  
  -- Calculate the holonomy value from Harmonic.lean
  have h_hol_val : holonomy γ.val cycle.toChain1 = (Fintype.card (Fin n)) * k :=
    holonomy_of_constant_harmonic cycle γ.val k h_const

  -- Calculate the walk sum value
  have h_walk_val : walk_sum G γ (canonical_cycle_walk cycle G h_embedded v) = (Fintype.card (Fin n)) * k := by
    rw [h_walk_eq_sum]
    -- The sum has n terms, each equal to k
    trans ∑ i ∈ Finset.range n, k
    · apply Finset.sum_congr rfl
      intro i _
      simp only [Function.iterate_succ_apply']
      exact h_const (cycle.next^[i] v)
    · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have h_inst : ‹Fintype (Fin n)› = Fin.fintype n := Subsingleton.elim _ _
      simp only [h_inst, Fintype.card_fin]

  -- 4. Connect holonomy to energy
  -- Explicitly calculate energy = n * k^2 (since private lemmas are unavailable)
  have h_energy : norm_sq γ.val = (holonomy γ.val cycle.toChain1)^2 / (Fintype.card (Fin n)) := by
    unfold norm_sq inner_product_C1
    have h_sum_sq : ∑ i, ∑ j, γ.val.val i j * γ.val.val i j = 2 * (Fintype.card (Fin n)) * k^2 := by
      -- Each inner sum equals 2 * k^2
      have h_inner : ∀ i : Fin n, ∑ j, γ.val.val i j * γ.val.val i j = 2 * k^2 := by
        intro i
        -- For each node, exactly two neighbors (next, prev) have non-zero val
        let next := cycle.next i
        let prev := cycle.prev i
        have h_ne : next ≠ prev := (prev_ne_next_of_n_ge_3 cycle h_n_ge_3 i).symm
        -- Helper: γ is 0 everywhere except next/prev
        have h_support_i : ∀ j, j ≠ next → j ≠ prev → γ.val.val i j = 0 := by
          intro j hn hp; apply h_support; intro h_eq; rw [h_eq] at hn; contradiction
        rw [Finset.sum_eq_add_sum_diff_singleton (i:=next) (h:=Finset.mem_univ _)]
        rw [Finset.sum_eq_add_sum_diff_singleton (i:=prev)]
        · -- Terms are k^2 and (-k)^2
          rw [h_const i] -- next
          have h_prev_val : γ.val.val i prev = -k := by
             rw [γ.val.skew]; simp only [neg_eq_iff_eq_neg, neg_neg]
             rw [← cycle.next_prev (i := i)]; exact h_const prev
          rw [h_prev_val]
          -- Remaining terms are 0
          have h_rest : ∑ x ∈ (Finset.univ \ {next}) \ {prev}, γ.val.val i x * γ.val.val i x = 0 := by
               apply Finset.sum_eq_zero
               intro x hx; simp at hx; rw [h_support_i x hx.1 hx.2]; ring
          rw [h_rest, add_zero]
          ring
        · simp [h_ne.symm]
      -- Now sum over all i
      simp only [h_inner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have h_inst : ‹Fintype (Fin n)› = Fin.fintype n := Subsingleton.elim _ _
      simp only [h_inst, Fintype.card_fin]
      ring

    rw [h_sum_sq, h_hol_val]
    field_simp

  -- 5. Combine results: (log Z / I) recovers the holonomy
  have h_Z_val : Z = cexp (I * ↑(holonomy γ.val cycle.toChain1)) := by
    rw [h_Z_pure, h_walk_val, h_hol_val]
    
  have h_log_re : (Complex.log Z / I).re = holonomy γ.val cycle.toChain1 := by
    rw [h_Z_val]
    rw [Complex.log_exp]
    · field_simp [I_ne_zero]; simp
    · simp only [mul_im, I_im, I_re, ofReal_im, ofReal_re]; ring_nf; exact h_branch.1
    · simp only [mul_im, I_im, I_re, ofReal_im, ofReal_re]; ring_nf; exact h_branch.2

  rw [h_energy, h_log_re]

end Diaspora.Quantum
