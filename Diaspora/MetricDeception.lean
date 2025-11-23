/-
# Metric Deception Theorem

Formal verification that in a frustrated Theta graph, both the Local Strain (dφ)
and the Harmonic Stress (γ) can point to the wrong edge to break.
-/

import Diaspora.FalseVacuum
import Diaspora.HodgeDecomposition

namespace DiscreteHodge

open BigOperators

/--
The harmonic component γ of trap_sigma under Hodge decomposition σ = dϕ + γ.
-/
noncomputable def trap_gamma : C1 n_theta := {
  val := fun i j =>
    if (i=0 ∧ j=1) then (19:ℝ)/4 else if (i=1 ∧ j=0) then -(19:ℝ)/4
    else if (i=0 ∧ j=2) then -(19:ℝ)/4 else if (i=2 ∧ j=0) then (19:ℝ)/4
    else if (i=1 ∧ j=2) then (1:ℝ)/2 else if (i=2 ∧ j=1) then -(1:ℝ)/2
    else if (i=1 ∧ j=3) then (17:ℝ)/4 else if (i=3 ∧ j=1) then -(17:ℝ)/4
    else if (i=2 ∧ j=3) then -(17:ℝ)/4 else if (i=3 ∧ j=2) then (17:ℝ)/4
    else 0
  skew := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp <;> norm_num
}

noncomputable def trap_phi : C0 n_theta :=
  fun i =>
    if i = 0 then 0
    else if i = 1 then -(19:ℝ)/4
    else if i = 2 then (19:ℝ)/4
    else 0

lemma trap_gamma_harmonic : IsHarmonic trap_gamma := by
  intro i
  show ∑ j, trap_gamma.val i j = 0
  fin_cases i
  · rw [Fin.sum_univ_four]
    unfold trap_gamma C1.val
    simp [fin_0, fin_1, fin_2, fin_3]
    norm_num
  · rw [Fin.sum_univ_four]
    unfold trap_gamma C1.val
    simp [fin_0, fin_1, fin_2, fin_3]
    norm_num
  · rw [Fin.sum_univ_four]
    unfold trap_gamma C1.val
    simp [fin_0, fin_1, fin_2, fin_3]
    norm_num
  · rw [Fin.sum_univ_four]
    unfold trap_gamma C1.val
    simp [fin_0, fin_1, fin_2, fin_3]
    norm_num

lemma trap_decomposition :
  ∀ i j, trap_sigma.val i j = (d0 trap_phi).val i j + trap_gamma.val i j := by
  intro i j
  unfold trap_sigma d0 trap_phi trap_gamma C1.val
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

lemma trap_orthogonality :
  inner_product_C1 (d0 trap_phi) trap_gamma = 0 := by
  unfold inner_product_C1 d0 trap_phi trap_gamma
  conv_lhs => arg 2; arg 2; intro i; rw [Fin.sum_univ_four]
  rw [Fin.sum_univ_four]
  simp [fin_0, fin_1, fin_2, fin_3]
  norm_num

theorem metric_deception_in_theta_graph :
  let γ := trap_gamma
  let γ_trap := γ.val 1 2
  let γ_smart := γ.val 1 3
  (γ_trap ^ 2 < γ_smart ^ 2) := by
  unfold trap_gamma C1.val
  simp
  norm_num

end DiscreteHodge
