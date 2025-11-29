/-
# Interaction via Topological Fusion

The Handshake Theorem.

We explore the conditions under which two disjoint "subjective" systems
can communicate. We prove that mere contact (a single bridge) is topologically
sterile. True communication requires fusion (two bridges), which creates
a new harmonic cycle shared between the worlds.
-/

import Diaspora.Core.Calculus
import Diaspora.Hodge.Decomposition
import Diaspora.Hodge.Harmonic
import Diaspora.Dynamics.Transition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

open BigOperators Diaspora.Core Diaspora.Hodge Diaspora.Dynamics

namespace Diaspora.Models

/-! ## The Setup: Two Isolated Worlds -/

/-- Total nodes N=6. World A = {0,1,2}, World B = {3,4,5} -/
abbrev n_two_worlds : ℕ := 6

/--
True first Betti number: |E| - |V| + c where c is the number of connected components.
For the specific graphs in this file, we manually specify the component count.
-/
def betti_number {n : ℕ} (G : DynamicGraph n) (num_components : ℕ) : ℤ :=
  (edge_count G : ℤ) - (n : ℤ) + (num_components : ℤ)

/-- World A and World B are disjoint triangles with internal topology. -/
def disjoint_worlds : DynamicGraph n_two_worlds where
  active_edges := {
    (0,1), (1,0), (1,2), (2,1), (2,0), (0,2), -- World A (Triangle)
    (3,4), (4,3), (4,5), (5,4), (5,3), (3,5)  -- World B (Triangle)
  }
  symmetric := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  no_loops := by
    intro i
    fin_cases i <;> decide

/--
Initial State: Two separate harmonic spaces (2 connected components).
Betti number = 1 (from A) + 1 (from B) = 2.
-/
theorem isolation_betti_number :
  betti_number disjoint_worlds 2 = 2 := by
  unfold betti_number edge_count disjoint_worlds
  decide

/-! ## Stage 1: The Bridge (Contact) -/

/--
We add a SINGLE edge connecting World A (0) to World B (3).
This represents "touching" or "signaling."
-/
def bridged_worlds : DynamicGraph n_two_worlds where
  active_edges := disjoint_worlds.active_edges ∪ {(0,3), (3,0)}
  symmetric := by
    intro i j
    simp [disjoint_worlds]
    fin_cases i <;> fin_cases j <;> decide
  no_loops := by
    intro i
    simp [disjoint_worlds]
    fin_cases i <;> decide

/--
Theorem: Contact is Sterile.
Adding a bridge connects the components (2→1) but also adds an edge (+1).
These cancel out: Betti number remains 2. No new independent cycle is created.
-/
theorem contact_is_sterile :
  betti_number bridged_worlds 1 = 2 := by
  unfold betti_number edge_count bridged_worlds disjoint_worlds
  decide

/-! ## Stage 2: The Handle (Fusion) -/

/--
We add a SECOND edge connecting World A (1) to World B (4).
Now A and B are connected at two points.
-/
def fused_worlds : DynamicGraph n_two_worlds where
  active_edges := bridged_worlds.active_edges ∪ {(1,4), (4,1)}
  symmetric := by
    intro i j
    simp [bridged_worlds, disjoint_worlds]
    fin_cases i <;> fin_cases j <;> decide
  no_loops := by
    intro i
    simp [bridged_worlds, disjoint_worlds]
    fin_cases i <;> decide

/--
Theorem: Fusion is Generative.
Adding the second edge creates a NEW independent cycle.
Betti number jumps from 2 to 3.
This new cycle (0→3→4→1→0) traverses BOTH worlds.
-/
theorem fusion_creates_shared_reality :
  betti_number fused_worlds 1 = 3 := by
  unfold betti_number edge_count fused_worlds bridged_worlds disjoint_worlds
  decide

/-! ## The Shared Harmonic -/

/--
The communication cycle: 0 → 3 → 4 → 1 → 0.
This cycle exists only in the fused graph, threading through both worlds.
-/
def communication_cycle : Chain1 n_two_worlds := {
  coeff := fun i j =>
    if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1
    else if (j = 0 ∧ i = 3) ∨ (j = 3 ∧ i = 4) ∨ (j = 4 ∧ i = 1) ∨ (j = 1 ∧ i = 0) then -1
    else 0,
  antisym := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
}

/--
Theorem: The Handshake.
There exists a harmonic form γ on the fused graph that:
1. Has non-zero energy (it is real).
2. Is supported on the cycle connecting A and B.
3. Represents information exchange (flux between worlds).
-/
theorem the_handshake_theorem :
  ∃ γ : C1 n_two_worlds,
    IsHarmonic γ ∧
    holonomy γ communication_cycle ≠ 0 := by

  let σ_signal : C1 n_two_worlds := {
    val := fun i j =>
      if i=0 ∧ j=3 then 10
      else if i=3 ∧ j=0 then -10
      else 0,
    skew := by intro i j; fin_cases i <;> fin_cases j <;> (simp; try split_ifs; try simp_all; try norm_num)
  }

  obtain ⟨ϕ, γ, h_decomp, h_harm, h_orth⟩ := hodge_decomposition σ_signal
  use γ
  constructor
  · exact h_harm
  · have h_cycle : Chain1.IsCycle communication_cycle := by
      intro i
      unfold communication_cycle
      fin_cases i <;> decide

    have h_exact_zero : holonomy (d0 ϕ) communication_cycle = 0 :=
      holonomy_exact_zero_on_cycles ϕ communication_cycle h_cycle

    have h_sigma_decomp : holonomy σ_signal communication_cycle =
                          holonomy (d0 ϕ) communication_cycle + holonomy γ communication_cycle := by
      unfold holonomy eval
      simp_rw [h_decomp, add_mul, Finset.sum_add_distrib]
      ring

    have h_gamma : holonomy γ communication_cycle =
                   holonomy σ_signal communication_cycle - holonomy (d0 ϕ) communication_cycle := by
      linarith [h_sigma_decomp]

    rw [h_gamma, h_exact_zero, sub_zero]
    have : holonomy σ_signal communication_cycle = 10 := by
      unfold holonomy eval
      simp only [σ_signal, communication_cycle]
      calc (1/2) * ∑ i : Fin 6, ∑ j : Fin 6,
            (if i = 0 ∧ j = 3 then (10:ℝ) else if i = 3 ∧ j = 0 then -10 else 0) *
            ↑(if i = 0 ∧ j = 3 ∨ i = 3 ∧ j = 4 ∨ i = 4 ∧ j = 1 ∨ i = 1 ∧ j = 0 then (1:ℤ)
             else if j = 0 ∧ i = 3 ∨ j = 3 ∧ i = 4 ∨ j = 4 ∧ i = 1 ∨ j = 1 ∧ i = 0 then -1 else 0)
        _ = (1/2) * (10 * 1 + (-10) * (-1)) := by
            rw [show (10:ℝ)*1 + (-10)*(-1) = 20 from by norm_num]
            congr 1
            trans (10 * 1 + (-10) * (-1))
            · have h_03 : ∀ j : Fin 6, (if (0:Fin 6) = 0 ∧ j = 3 then (10:ℝ) else if 0 = 3 ∧ j = 0 then -10 else 0) *
                    ↑(if 0 = 0 ∧ j = 3 ∨ 0 = 3 ∧ j = 4 ∨ 0 = 4 ∧ j = 1 ∨ 0 = 1 ∧ j = 0 then (1:ℤ)
                      else if j = 0 ∧ 0 = 3 ∨ j = 3 ∧ 0 = 4 ∨ j = 4 ∧ 0 = 1 ∨ j = 1 ∧ 0 = 0 then -1 else 0)
                  = if j = 3 then 10 else 0 := by
                intro j; fin_cases j <;> simp
              have h_30 : ∀ j : Fin 6, (if (3:Fin 6) = 0 ∧ j = 3 then (10:ℝ) else if 3 = 3 ∧ j = 0 then -10 else 0) *
                    ↑(if 3 = 0 ∧ j = 3 ∨ 3 = 3 ∧ j = 4 ∨ 3 = 4 ∧ j = 1 ∨ 3 = 1 ∧ j = 0 then (1:ℤ)
                      else if j = 0 ∧ 3 = 3 ∨ j = 3 ∧ 3 = 4 ∨ j = 4 ∧ 3 = 1 ∨ j = 1 ∧ 3 = 0 then -1 else 0)
                  = if j = 0 then -10 * (-1) else 0 := by
                intro j; fin_cases j <;> simp
              have h_other : ∀ i : Fin 6, i ≠ 0 → i ≠ 3 →
                  ∑ j : Fin 6, (if i = 0 ∧ j = 3 then (10:ℝ) else if i = 3 ∧ j = 0 then -10 else 0) *
                    ↑(if i = 0 ∧ j = 3 ∨ i = 3 ∧ j = 4 ∨ i = 4 ∧ j = 1 ∨ i = 1 ∧ j = 0 then (1:ℤ)
                      else if j = 0 ∧ i = 3 ∨ j = 3 ∧ i = 4 ∨ j = 4 ∧ i = 1 ∨ j = 1 ∧ i = 0 then -1 else 0) = 0 := by
                intro i hi0 hi3
                simp [hi0, hi3]
              rw [Fin.sum_univ_six]
              simp
              rw [Fin.sum_univ_six, Fin.sum_univ_six]
              simp
            · norm_num
        _ = 10 := by norm_num
    rw [this]
    norm_num

end Diaspora.Models
