/-

# Topological Genesis

Formal verification that topological closure (adding an edge to form a cycle)
is a necessary and sufficient condition for the emergence of non-trivial
harmonic forms under a uniform non-conservative constraint field.
\-/

import Diaspora.DiscreteCalculus
import Diaspora.HodgeDecomposition
import Diaspora.HarmonicAnalysis
import Diaspora.TopologyDynamics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

namespace DiscreteHodge

open BigOperators

/-\! \#\# System Configuration -/

/-- System size N=3. Minimum complexity required for a non-trivial cycle. -/
abbrev n_sys : ℕ := 3

/--
State A: The Open Topology (Line Graph).
Structure: 0 <-> 1 <-> 2
First Betti Number b1 = 0.
-/
def G_open : DynamicGraph n_sys where
active_edges := {(0,1), (1,0), (1,2), (2,1)}
symmetric := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide
no_loops := by
  intro i
  simp
  fin_cases i <;> decide

/--
State B: The Closed Topology (Cycle Graph).
Structure: 0 <-> 1 <-> 2 <-> 0
First Betti Number b1 = 1.
This is G_open + edge (0,2).
-/
def G_closed : DynamicGraph n_sys where
active_edges := {(0,1), (1,0), (1,2), (2,1), (0,2), (2,0)}
symmetric := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide
no_loops := by
  intro i
  simp
  fin_cases i <;> decide

/-\! \#\# The Forcing Field -/

/--
A uniform rotational constraint σ.
It demands a flow of +1 along the path 0->1->2->0.
-/
def sigma_forcing : C1 n_sys := {
val := fun i j =>
if (i=0 ∧ j=1) ∨ (i=1 ∧ j=2) ∨ (i=2 ∧ j=0) then 1
else if (i=1 ∧ j=0) ∨ (i=2 ∧ j=1) ∨ (i=0 ∧ j=2) then -1
else 0
skew := by
  intro i j
  fin_cases i <;> fin_cases j <;> (simp; try split_ifs; try simp_all; try norm_num)
}

/-\! \#\# Theorems of Genesis -/

/--
Theorem 1: In the Open Topology, the forcing field is Exact.
There exists a potential ϕ such that dϕ = σ on all active edges.
Harmonic content is zero.
-/
theorem open_state_is_exact :
∃ ϕ : C0 n_sys, ∀ i j, (i, j) ∈ G_open.active_edges →
(d0 ϕ).val i j = sigma_forcing.val i j := by
-- Construct the potential by integrating σ along the path starting at 0
let ϕ : C0 n_sys := fun x =>
match x with
| 0 => 0
| 1 => 1
| 2 => 2

use ϕ
intro i j h_active
-- Verify dϕ = σ for every active edge
simp [G_open] at h_active
rcases h_active with h01|h10|h12|h21
· -- Edge (0,1)
  obtain ⟨rfl, rfl⟩ := h01
  simp [d0, sigma_forcing]; norm_num
· -- Edge (1,0)
  obtain ⟨rfl, rfl⟩ := h10
  simp [d0, sigma_forcing]; norm_num
· -- Edge (1,2)
  obtain ⟨rfl, rfl⟩ := h12
  simp [d0, sigma_forcing]; norm_num
· -- Edge (2,1)
  obtain ⟨rfl, rfl⟩ := h21
  simp [d0, sigma_forcing]; norm_num

/--
Theorem 2: In the Closed Topology, the forcing field is Not Exact.
No potential ϕ exists such that dϕ = σ on all active edges.
-/
theorem closed_state_is_not_exact :
¬ ∃ ϕ : C0 n_sys, ∀ i j, (i, j) ∈ G_closed.active_edges →
(d0 ϕ).val i j = sigma_forcing.val i j := by
intro h_exists
obtain ⟨ϕ, h_match⟩ := h_exists

-- Summing dϕ around the cycle 0->1->2->0 must be 0 (telescoping sum)
have h_cycle_d0 : (d0 ϕ).val 0 1 + (d0 ϕ).val 1 2 + (d0 ϕ).val 2 0 = 0 := by
  unfold d0
  simp

-- Evaluate σ on the active edges of the cycle
have h_match_01 : (d0 ϕ).val 0 1 = 1 := h_match 0 1 (by simp [G_closed])
have h_match_12 : (d0 ϕ).val 1 2 = 1 := h_match 1 2 (by simp [G_closed])
have h_match_20 : (d0 ϕ).val 2 0 = 1 := h_match 2 0 (by simp [G_closed])

-- Algebraic contradiction: 0 = 3
rw [h_match_01, h_match_12, h_match_20] at h_cycle_d0
norm_num at h_cycle_d0

/--
Theorem 3: Harmonic Genesis.
The Hodge Decomposition of σ in the Closed Topology yields a non-zero harmonic component γ.
This confirms the energy has shifted from local potential to topological structure.
-/
theorem harmonic_genesis :
∃ γ : C1 n_sys,
IsHarmonic γ ∧
norm_sq γ > 0 ∧
-- The harmonic form captures the winding number (3)
(holonomy γ {
coeff := fun i j => if (i=0∧j=1)∨(i=1∧j=2)∨(i=2∧j=0) then 1
else if (i=1∧j=0)∨(i=2∧j=1)∨(i=0∧j=2) then -1 else 0,
antisym := by intro i j; fin_cases i <;> fin_cases j <;> (simp; try split_ifs; try simp_all; try norm_num)
}) = 3 := by
-- Perform Hodge Decomposition on the forcing field
obtain ⟨ϕ, γ, h_decomp, h_harm, h_orth⟩ := hodge_decomposition sigma_forcing

use γ

-- First prove holonomy γ = 3 (needed for both bullets below)
have h_sigma_cycle : holonomy sigma_forcing {
  coeff := fun i j => if (i=0∧j=1)∨(i=1∧j=2)∨(i=2∧j=0) then 1
    else if (i=1∧j=0)∨(i=2∧j=1)∨(i=0∧j=2) then -1 else 0,
  antisym := by intro i j; fin_cases i <;> fin_cases j <;> (simp; try split_ifs; try simp_all; try norm_num)
} = 3 := by
  unfold holonomy eval sigma_forcing
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  norm_num

have h_dphi_cycle : holonomy (d0 ϕ) {
  coeff := fun i j => if (i=0∧j=1)∨(i=1∧j=2)∨(i=2∧j=0) then 1
                      else if (i=1∧j=0)∨(i=2∧j=1)∨(i=0∧j=2) then -1 else 0,
  antisym := by intro i j; fin_cases i <;> fin_cases j <;> (simp; try split_ifs; try simp_all; try norm_num)
} = 0 := by
  apply holonomy_exact_zero_on_cycles
  intro i
  rw [Fin.sum_univ_three]
  fin_cases i
  · simp
  · simp
  · decide

have h_gamma_cycle : holonomy γ {
  coeff := fun i j => if (i=0∧j=1)∨(i=1∧j=2)∨(i=2∧j=0) then 1
                      else if (i=1∧j=0)∨(i=2∧j=1)∨(i=0∧j=2) then -1 else 0,
  antisym := by intro i j; fin_cases i <;> fin_cases j <;> (simp; try split_ifs; try simp_all; try norm_num)
} = 3 := by
  rw [←h_sigma_cycle]
  let c : Chain1 n_sys := {
    coeff := fun i j => if (i=0∧j=1)∨(i=1∧j=2)∨(i=2∧j=0) then 1
                        else if (i=1∧j=0)∨(i=2∧j=1)∨(i=0∧j=2) then -1 else 0,
    antisym := by intro i j; fin_cases i <;> fin_cases j <;> (simp; try split_ifs; try simp_all; try norm_num)
  }
  have h_hol_eq : holonomy sigma_forcing c = holonomy {
    val := fun i j => (d0 ϕ).val i j + γ.val i j,
    skew := by intro i j; rw [(d0 ϕ).skew, γ.skew]; ring
  } c := by
    unfold holonomy eval
    simp only
    congr 2 with i
    congr 2 with j
    rw [h_decomp]
  rw [h_hol_eq, holonomy_add_cochain, h_dphi_cycle]
  ring

constructor
· exact h_harm
constructor
· -- Prove ||γ|| > 0 using contradiction
  -- If holonomy is non-zero, norm must be non-zero
  by_contra h_zero
  simp at h_zero
  have h_gamma_zero : γ.val = fun _ _ => 0 := by
    have h_norm_eq : norm_sq γ = 0 := by
      have h_nonneg : norm_sq γ ≥ 0 := by
        unfold norm_sq inner_product_C1
        apply mul_nonneg
        · norm_num
        · apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro j _; apply mul_self_nonneg
      linarith
    ext i j
    unfold norm_sq inner_product_C1 at h_norm_eq
    have h_sum_zero : ∑ i : Fin n_sys, ∑ j : Fin n_sys, γ.val i j * γ.val i j = 0 := by linarith
    have h_all_zero : ∀ i j, γ.val i j * γ.val i j = 0 := by
      intro i j
      have h : ∑ i, ∑ j, γ.val i j * γ.val i j = 0 ↔ ∀ i ∈ Finset.univ, ∑ j, γ.val i j * γ.val i j = 0 :=
        Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => mul_self_nonneg _))
      rw [h] at h_sum_zero
      specialize h_sum_zero i (Finset.mem_univ i)
      have h2 : ∑ j, γ.val i j * γ.val i j = 0 ↔ ∀ j ∈ Finset.univ, γ.val i j * γ.val i j = 0 :=
        Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => mul_self_nonneg _)
      rw [h2] at h_sum_zero
      exact h_sum_zero j (Finset.mem_univ j)
    have := h_all_zero i j
    exact mul_self_eq_zero.mp this
  unfold holonomy eval at h_gamma_cycle
  rw [h_gamma_zero] at h_gamma_cycle
  simp at h_gamma_cycle

· exact h_gamma_cycle

end DiscreteHodge
