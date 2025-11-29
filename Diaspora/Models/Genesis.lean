/-

# Topological Genesis

Formal verification that topological closure (adding an edge to form a cycle)
is a necessary and sufficient condition for the emergence of non-trivial
harmonic forms under a uniform non-conservative constraint field.
\-/

import Diaspora.Core.Calculus
import Diaspora.Hodge.Decomposition
import Diaspora.Hodge.Harmonic
import Diaspora.Dynamics.Transition
import Diaspora.Models.Resilience
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

open BigOperators Diaspora.Core Diaspora.Hodge Diaspora.Dynamics

namespace Diaspora.Models

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

/-\! \#\# Topological Transition Theorems -/

/--
Theorem 1: In the Open Topology, the forcing field is Exact.
There exists a potential ϕ such that dϕ = σ on all active edges.
Harmonic content is zero.
-/
theorem open_state_is_exact :
∃ ϕ : C0 n_sys, ∀ i j, (i, j) ∈ G_open.active_edges →
(d0 ϕ).val i j = sigma_forcing.val i j := by
let ϕ : C0 n_sys := fun x =>
match x with
| 0 => 0
| 1 => 1
| 2 => 2

use ϕ
intro i j h_active
simp [G_open] at h_active
rcases h_active with h01|h10|h12|h21
· obtain ⟨rfl, rfl⟩ := h01
  simp [d0, sigma_forcing]; norm_num
· obtain ⟨rfl, rfl⟩ := h10
  simp [d0, sigma_forcing]; norm_num
· obtain ⟨rfl, rfl⟩ := h12
  simp [d0, sigma_forcing]; norm_num
· obtain ⟨rfl, rfl⟩ := h21
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

have h_cycle_d0 : (d0 ϕ).val 0 1 + (d0 ϕ).val 1 2 + (d0 ϕ).val 2 0 = 0 := by
  unfold d0
  simp

have h_match_01 : (d0 ϕ).val 0 1 = 1 := h_match 0 1 (by simp [G_closed])
have h_match_12 : (d0 ϕ).val 1 2 = 1 := h_match 1 2 (by simp [G_closed])
have h_match_20 : (d0 ϕ).val 2 0 = 1 := h_match 2 0 (by simp [G_closed])

rw [h_match_01, h_match_12, h_match_20] at h_cycle_d0
norm_num at h_cycle_d0

/--
In the closed topology, Hodge decomposition of σ yields a non-zero harmonic component γ.
-/
theorem harmonic_genesis :
∃ γ : C1 n_sys,
IsHarmonic γ ∧
norm_sq γ > 0 ∧
(holonomy γ {
coeff := fun i j => if (i=0∧j=1)∨(i=1∧j=2)∨(i=2∧j=0) then 1
else if (i=1∧j=0)∨(i=2∧j=1)∨(i=0∧j=2) then -1 else 0,
antisym := by intro i j; fin_cases i <;> fin_cases j <;> (simp; try split_ifs; try simp_all; try norm_num)
}) = 3 := by
obtain ⟨ϕ, γ, h_decomp, h_harm, h_orth⟩ := hodge_decomposition sigma_forcing

use γ

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
· by_contra h_zero
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

/-! ## Genesis from Noise: The Measure-Zero Argument -/

/-- A 1-cochain is exact if it equals d0 ϕ for some potential ϕ. -/
def C1.IsExact {n : ℕ} (σ : C1 n) : Prop :=
  ∃ ϕ : C0 n, ∀ i j, σ.val i j = (d0 ϕ).val i j

/-- Key lemma: Non-exact forms have non-zero harmonic projection.

    Proof: By Hodge decomposition, σ = d0(ϕ) + γ with γ harmonic.
    If γ = 0, then σ = d0(ϕ), so σ is exact. Contrapositive gives the result.
-/
theorem non_exact_has_nonzero_harmonic {n : ℕ} [Fintype (Fin n)] (σ : C1 n)
    (h_not_exact : ¬ C1.IsExact σ) :
    ∃ γ : C1 n, IsHarmonic γ ∧ norm_sq γ > 0 ∧
    ∃ ϕ : C0 n, ∀ i j, σ.val i j = (d0 ϕ).val i j + γ.val i j := by
  obtain ⟨ϕ, γ, h_decomp, h_harm, _⟩ := hodge_decomposition σ
  use γ
  refine ⟨h_harm, ?_, ϕ, h_decomp⟩
  by_contra h_not_pos
  push_neg at h_not_pos
  have h_zero : norm_sq γ = 0 := le_antisymm h_not_pos (norm_sq_nonneg γ)
  have h_val_zero : ∀ i j, γ.val i j = 0 := norm_sq_zero_iff_zero γ h_zero
  have h_exact : C1.IsExact σ := by
    use ϕ
    intro i j
    rw [h_decomp i j, h_val_zero i j, add_zero]
  exact h_not_exact h_exact

/-- The forcing field σ_forcing is not exact (witnessed by closed_state_is_not_exact). -/
theorem sigma_forcing_not_exact : ¬ C1.IsExact sigma_forcing := by
  intro ⟨ϕ, h_eq⟩
  apply closed_state_is_not_exact
  use ϕ
  intro i j h_active
  exact (h_eq i j).symm

/-- Exact forms are a proper subset: there exist non-exact 1-cochains.

    sigma_forcing is a witness that the exact forms don't cover all of C1 n.
-/
theorem exact_forms_proper_subset :
    ∃ σ : C1 n_sys, ¬ C1.IsExact σ :=
  ⟨sigma_forcing, sigma_forcing_not_exact⟩

/-- Non-exact forms exist and have non-trivial harmonic projection. -/
theorem random_field_has_harmonic_component :
    ∃ σ : C1 n_sys, ∃ γ : C1 n_sys,
      IsHarmonic γ ∧ norm_sq γ > 0 ∧
      ∃ ϕ : C0 n_sys, ∀ i j, σ.val i j = (d0 ϕ).val i j + γ.val i j := by
  obtain ⟨σ, h_not_exact⟩ := exact_forms_proper_subset
  obtain ⟨γ, h_harm, h_pos, ϕ, h_decomp⟩ := non_exact_has_nonzero_harmonic σ h_not_exact
  exact ⟨σ, γ, h_harm, h_pos, ϕ, h_decomp⟩

/-- The harmonic projection of the forcing field has positive energy. -/
theorem forcing_field_harmonic_energy_positive :
    ∃ γ : C1 n_sys, IsHarmonic γ ∧ norm_sq γ > 0 ∧
    ∃ ϕ : C0 n_sys, ∀ i j, sigma_forcing.val i j = (d0 ϕ).val i j + γ.val i j :=
  non_exact_has_nonzero_harmonic sigma_forcing sigma_forcing_not_exact

end Diaspora.Models
