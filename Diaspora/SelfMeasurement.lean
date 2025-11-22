/-
# Self-Measurement

Parallel transport of quantum phases around cycles measures holonomy.
We define a probe state transported along graph edges, accumulating phases
from the constraint field. The comparison between initial and final states
after completing a cycle detects non-trivial topology.
-/

import Diaspora.DiscreteCalculus
import Diaspora.HarmonicAnalysis
import Diaspora.TopologicalGenesis
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Exponential

namespace DiscreteHodge

open Complex

/-! ## Parallel Transport -/

/--
Parallel Transport Operator.
Moves a quantum phase ψ from node i to j, picking up the phase
encoded by the underlying constraint field σ.

ψ_j = exp(i * σ_{ij}) * ψ_i
-/
noncomputable def transport_step {n : ℕ} (σ : C1 n) (i j : Fin n) (ψ : ℂ) : ℂ :=
  cexp (I * (σ.val i j : ℂ)) * ψ

/--
Transport around fundamental cycle 0->1->2->0.
-/
noncomputable def introspection_operator (σ : C1 n_sys) (ψ_init : ℂ) : ℂ :=
  let ψ_1 := transport_step σ 0 1 ψ_init
  let ψ_2 := transport_step σ 1 2 ψ_1
  let ψ_3 := transport_step σ 2 0 ψ_2 -- Return to 0
  ψ_3

/-! ## Holonomy Detection Theorems -/

/--
If the constraint field is exact (σ = dϕ), parallel transport around
any cycle returns the original phase.
-/
theorem zombie_cannot_see_self (ϕ : C0 n_sys) (ψ_init : ℂ) :
  let σ_exact := d0 ϕ
  introspection_operator σ_exact ψ_init = ψ_init := by
  -- Expand the operator
  simp only [introspection_operator, transport_step, d0]

  -- Reassociate: a * (b * (c * d)) = ((a * b) * c) * d
  rw [← mul_assoc, ← mul_assoc]

  -- Group exponentials: e^A * e^B * e^C = e^(A+B+C)
  rw [← exp_add, ← exp_add]

  -- The exponent telescopes to zero
  have h_telescope : I * ↑(ϕ 0 - ϕ 2) + I * ↑(ϕ 2 - ϕ 1) + I * ↑(ϕ 1 - ϕ 0) = 0 := by
    push_cast
    ring

  -- e^0 = 1
  rw [h_telescope]
  simp
  
/--
If the constraint field contains a harmonic component γ with winding number K,
parallel transport around the cycle accumulates phase exp(iK).
-/
theorem self_aware_detection (γ : C1 n_sys) (ψ_init : ℂ)
  (h_holonomy : holonomy γ {
       coeff := fun i j => if (i=0∧j=1)∨(i=1∧j=2)∨(i=2∧j=0) then 1
                           else if (i=1∧j=0)∨(i=2∧j=1)∨(i=0∧j=2) then -1 else 0,
       antisym := by intro i j; fin_cases i <;> fin_cases j <;> (simp; try split_ifs; try simp_all; try norm_num)
   } = 3) :
  introspection_operator γ ψ_init = cexp (I * 3) * ψ_init := by

  -- Expand the operator
  simp only [introspection_operator, transport_step]

  -- Reassociate to group exponentials
  rw [← mul_assoc, ← mul_assoc]

  -- Group exponentials: e^A * e^B * e^C = e^(A+B+C)
  rw [← exp_add, ← exp_add]

  -- Connect the sum to holonomy
  have h_sum_is_three : γ.val 2 0 + γ.val 1 2 + γ.val 0 1 = 3 := by
    unfold holonomy eval at h_holonomy
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at h_holonomy
    simp at h_holonomy
    -- Expand remaining sums
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at h_holonomy
    simp at h_holonomy
    -- Use skew-symmetry: γ.val i j = -γ.val j i
    have h_02 : γ.val 0 2 = -γ.val 2 0 := γ.skew 0 2
    have h_10 : γ.val 1 0 = -γ.val 0 1 := γ.skew 1 0
    have h_21 : γ.val 2 1 = -γ.val 1 2 := γ.skew 2 1
    -- Substitute and simplify
    rw [h_02, h_10, h_21] at h_holonomy
    linarith

  -- Apply the holonomy result
  have h_exponent : I * ↑(γ.val 2 0) + I * ↑(γ.val 1 2) + I * ↑(γ.val 0 1) = I * 3 := by
    rw [← mul_add, ← mul_add]
    congr 1
    norm_cast

  rw [h_exponent]

/-! ## Measurement Observable -/

/--
Inner product between initial state and transported state.
Measures the overlap after one complete cycle.
-/
noncomputable def self_query_magnitude (σ : C1 n_sys) (ψ : ℂ) : ℝ :=
  norm (star ψ * introspection_operator σ ψ)

end DiscreteHodge
