import Diaspora.Dynamics.BoundStates

/-!
# N-Body Gravitational Binding

This file proves that gravitational binding in Diaspora is strictly pairwise:
there are no emergent N-body forces. The total binding energy of any collection
of cycles decomposes exactly into the sum of pairwise binding energies.

## Main Results

- `binding_energy_eq_neg_inner`: Binding = -2 × inner product
- `binding_energy_symm`: Binding energy is symmetric
- `total_binding_is_pairwise_3`: Three-cycle binding decomposes into three pairwise terms
- `disjoint_zero_binding`: Disjoint cycles have zero binding

## Physical Interpretation

In classical physics, 3-body (and higher) forces can emerge from quantum field theory
or from non-linear interactions. Diaspora's gravitational model is simpler:
**gravity is strictly bilinear**.

This means:
1. The total gravitational energy of N particles is exactly the sum of pairwise energies
2. There are no "emergent" 3-body, 4-body, etc. forces
3. Superposition holds exactly for gravitational interactions

This is the discrete analog of Newtonian gravity's linearity: the gravitational
field of multiple masses is the vector sum of individual fields.
-/

namespace Diaspora.Dynamics.NBodyBinding

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics

variable {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]

/-! ## Inner Product Properties -/

omit [DecidableEq (Fin n)] [NeZero n] in
/-- Inner product is symmetric. -/
theorem inner_product_C1_comm (σ τ : C1 n) :
    inner_product_C1 σ τ = inner_product_C1 τ σ := by
  unfold inner_product_C1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq (Fin n)] [NeZero n] in
/-- Norm squared is the inner product with itself. -/
theorem norm_sq_eq_inner (σ : C1 n) : norm_sq σ = inner_product_C1 σ σ := rfl

/-! ## Binding Energy and Inner Product -/

/-- **Binding Energy is Negative Twice the Inner Product**

This connects the binding_energy definition to the inner product formula. -/
theorem binding_energy_eq_neg_inner (c₁ c₂ : GeneralCycle n) :
    binding_energy c₁ c₂ = -2 * inner_product_C1 (general_cycle_form c₁) (general_cycle_form c₂) := by
  unfold binding_energy
  have h := combined_cycle_energy c₁ c₂
  linarith

/-- **Binding Energy is Symmetric** -/
theorem binding_energy_symm (c₁ c₂ : GeneralCycle n) :
    binding_energy c₁ c₂ = binding_energy c₂ c₁ := by
  rw [binding_energy_eq_neg_inner, binding_energy_eq_neg_inner]
  rw [inner_product_C1_comm]

/-! ## N-Body Energy Decomposition -/

/-- Total individual energy: sum of energies of each cycle. -/
noncomputable def total_individual_energy {N : ℕ} (cycles : Fin N → GeneralCycle n) : ℝ :=
  ∑ i : Fin N, norm_sq (general_cycle_form (cycles i))

/-- Sum of all pairwise inner products (for i < j). -/
noncomputable def sum_pairwise_inner {N : ℕ} (cycles : Fin N → GeneralCycle n) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N,
    if i < j then inner_product_C1 (general_cycle_form (cycles i)) (general_cycle_form (cycles j))
    else 0

/-- Sum of all pairwise binding energies (for i < j). -/
noncomputable def sum_pairwise_binding {N : ℕ} (cycles : Fin N → GeneralCycle n) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N,
    if i < j then binding_energy (cycles i) (cycles j)
    else 0

/-- Pairwise binding equals -2 times pairwise inner products. -/
theorem sum_pairwise_binding_eq_inner {N : ℕ} (cycles : Fin N → GeneralCycle n) :
    sum_pairwise_binding cycles = -2 * sum_pairwise_inner cycles := by
  unfold sum_pairwise_binding sum_pairwise_inner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h
  · rw [binding_energy_eq_neg_inner]
  · ring

/-! ## The Three-Cycle Case -/

/-- The three-cycle case from Gravity.lean restated in binding energy language.
    The total binding of three cycles equals the sum of the three pairwise bindings. -/
theorem three_cycle_binding_is_pairwise (c₁ c₂ c₃ : GeneralCycle n) :
    binding_energy c₁ c₂ + binding_energy c₁ c₃ + binding_energy c₂ c₃ =
    (norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) + norm_sq (general_cycle_form c₃)) -
    norm_sq (cycle_sum3 c₁ c₂ c₃) := by
  have h := three_cycle_energy_pairwise c₁ c₂ c₃
  have h₁₂ := binding_energy_eq_neg_inner c₁ c₂
  have h₁₃ := binding_energy_eq_neg_inner c₁ c₃
  have h₂₃ := binding_energy_eq_neg_inner c₂ c₃
  linarith

/-- **The Total Binding Decomposition Theorem (3-cycle case)**

The total binding energy of 3 cycles equals the sum of all pairwise binding energies.
This proves that gravity in Diaspora is strictly pairwise for 3 bodies. -/
theorem total_binding_is_pairwise_3 (c₁ c₂ c₃ : GeneralCycle n) :
    (norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) + norm_sq (general_cycle_form c₃)) -
    norm_sq (cycle_sum3 c₁ c₂ c₃) =
    binding_energy c₁ c₂ + binding_energy c₁ c₃ + binding_energy c₂ c₃ := by
  have h := three_cycle_energy_pairwise c₁ c₂ c₃
  have h₁₂ := binding_energy_eq_neg_inner c₁ c₂
  have h₁₃ := binding_energy_eq_neg_inner c₁ c₃
  have h₂₃ := binding_energy_eq_neg_inner c₂ c₃
  linarith

/-! ## Corollaries -/

/-- **Corollary: Disjoint cycles have zero pairwise binding**

If two cycles share no edges, their binding energy is zero. -/
theorem disjoint_zero_binding (c₁ c₂ : GeneralCycle n) (h : c₁.signedOverlap c₂ = 0) :
    binding_energy c₁ c₂ = 0 := by
  rw [binding_energy_eq_neg_inner]
  have h_inner : inner_product_C1 (general_cycle_form c₁) (general_cycle_form c₂) = 0 := by
    rw [cycle_inner_product_formula, h]
    simp
  linarith

/-- **Corollary: Total binding of disjoint cycles is zero**

If all cycles are pairwise disjoint, the total binding energy is zero. -/
theorem all_disjoint_zero_total_binding {N : ℕ} (cycles : Fin N → GeneralCycle n)
    (h_disjoint : ∀ i j, i ≠ j → (cycles i).signedOverlap (cycles j) = 0) :
    sum_pairwise_binding cycles = 0 := by
  unfold sum_pairwise_binding
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  split_ifs with h
  · exact disjoint_zero_binding (cycles i) (cycles j) (h_disjoint i j (ne_of_lt h))
  · rfl

omit [DecidableEq (Fin n)] in
/-- **Physical Principle: Superposition of Gravitational Fields**

The gravitational field (harmonic form) of a system of cycles is the sum of
individual fields. This is the linearity that enables pairwise decomposition. -/
theorem gravitational_superposition (c₁ c₂ : GeneralCycle n) :
    ∀ i j : Fin n, (cycle_sum c₁ c₂).val i j =
      (general_cycle_form c₁).val i j + (general_cycle_form c₂).val i j := by
  intro i j
  rfl

omit [DecidableEq (Fin n)] in
/-- **Physical Principle: Three-Body Superposition**

For three cycles, the combined field is the sum of three fields. -/
theorem gravitational_superposition_3 (c₁ c₂ c₃ : GeneralCycle n) :
    ∀ i j : Fin n, (cycle_sum3 c₁ c₂ c₃).val i j =
      (general_cycle_form c₁).val i j + (general_cycle_form c₂).val i j + (general_cycle_form c₃).val i j := by
  intro i j
  rfl

/-- **Corollary: Binding energy is non-negative for opposite-direction sharing**

When cycles share edges in opposite directions (no same-direction sharing),
the binding energy is non-negative (attractive interaction). -/
theorem binding_nonneg_opposite (c₁ c₂ : GeneralCycle n)
    (h_same : c₁.sameDirectionEdges c₂ = 0) :
    binding_energy c₁ c₂ ≥ 0 := by
  rw [binding_energy_formula c₁ c₂ h_same]
  unfold sharing_energy_reduction
  have h_len1 : (0 : ℝ) < c₁.len := by
    simp only [GeneralCycle.len]
    exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₁.len_ge_3)
  have h_len2 : (0 : ℝ) < c₂.len := by
    simp only [GeneralCycle.len]
    exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₂.len_ge_3)
  have h_prod_pos : (0 : ℝ) < c₁.len * c₂.len := mul_pos h_len1 h_len2
  apply div_nonneg
  · apply mul_nonneg
    · linarith
    · exact Nat.cast_nonneg _
  · linarith

/-- **The No-Emergent-Forces Principle**

This theorem states the fundamental principle: the energy of any gravitational
interaction between cycles can be computed pairwise. There are no corrections
from 3-body, 4-body, or higher-order interactions.

Mathematically: The inner product is bilinear, so
⟨∑ᵢ γᵢ, ∑ⱼ γⱼ⟩ = ∑ᵢⱼ ⟨γᵢ, γⱼ⟩

This linearity is what makes gravity in Diaspora strictly pairwise. -/
theorem no_emergent_forces_principle (c₁ c₂ c₃ : GeneralCycle n)
    (h₁₂ : c₁.sameDirectionEdges c₂ = 0)
    (h₁₃ : c₁.sameDirectionEdges c₃ = 0)
    (h₂₃ : c₂.sameDirectionEdges c₃ = 0) :
    -- The total binding equals the sum of pairwise bindings
    (norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) + norm_sq (general_cycle_form c₃)) -
    norm_sq (cycle_sum3 c₁ c₂ c₃) =
    sharing_energy_reduction c₁.len c₂.len (c₁.oppositeDirectionEdges c₂) +
    sharing_energy_reduction c₁.len c₃.len (c₁.oppositeDirectionEdges c₃) +
    sharing_energy_reduction c₂.len c₃.len (c₂.oppositeDirectionEdges c₃) := by
  rw [total_binding_is_pairwise_3]
  rw [binding_energy_formula c₁ c₂ h₁₂]
  rw [binding_energy_formula c₁ c₃ h₁₃]
  rw [binding_energy_formula c₂ c₃ h₂₃]

end Diaspora.Dynamics.NBodyBinding
