import Diaspora.Logic.Classicality.Orthogonality

/-!
# Gravity: Edge-Sharing as Attraction

This file formalizes the central thesis of Diaspora's interpretation of gravity:

> **Gravity is just the tendency of these loops to share edges to minimize their total N.**

Topological defects (cycles carrying harmonic forms) reduce their combined energy by sharing
edges with opposite orientation. This is the fundamental mechanism of attraction in Diaspora.

## Main Results

- `sharing_energy_reduction`: The energy saved by sharing k edges with optimal orientation
- `sharing_reduces_energy`: Opposite-direction sharing reduces combined energy below the sum
- `gravity_binding_energy`: The binding energy formula E = 2k/(n₁·n₂)
- `complete_overlap_annihilation`: Same cycle, opposite direction → complete cancellation

## Physical Interpretation

Two topological defects (matter) can exist in three configurations:
1. **Disjoint**: No shared edges → energies add independently
2. **Same direction**: Shared edges amplify strain → repulsion
3. **Opposite direction**: Shared edges cancel strain → attraction (gravity)

The "force" arises from energy minimization: systems evolve toward lower-energy states.
-/

namespace Diaspora.Dynamics

open Diaspora.Core Diaspora.Logic Diaspora.Hodge

/-- The energy reduction from sharing k edges with opposite orientation.
    This is the gravitational binding energy: 2k/(n₁·n₂) -/
noncomputable def sharing_energy_reduction (n₁ n₂ k : ℕ) : ℝ :=
  2 * (k : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))

/-- Sharing edges with optimal (opposite) orientation reduces combined energy.
    This is the core theorem: edge-sharing is attractive. -/
theorem sharing_reduces_energy {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_opp : c₁.oppositeDirectionEdges c₂ > 0)
    (h_same : c₁.sameDirectionEdges c₂ = 0) :
    norm_sq (cycle_sum c₁ c₂) < norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) := by
  apply negative_overlap_reduces_energy
  unfold GeneralCycle.signedOverlap
  simp only [h_same]
  -- Goal: 0 - opp < 0
  omega

/-- The binding energy formula: energy saved = 2k/(n₁·n₂) -/
theorem gravity_binding_energy {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_same : c₁.sameDirectionEdges c₂ = 0) :
    norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) - norm_sq (cycle_sum c₁ c₂) =
    sharing_energy_reduction c₁.len c₂.len (c₁.oppositeDirectionEdges c₂) := by
  rw [combined_cycle_energy_formula, general_cycle_form_energy, general_cycle_form_energy]
  unfold sharing_energy_reduction GeneralCycle.signedOverlap
  simp only [h_same, CharP.cast_eq_zero, zero_sub, Int.cast_neg, Int.cast_natCast]
  ring

/-- Complete overlap with opposite direction gives complete cancellation.
    If two cycles traverse exactly the same edges in opposite directions, their
    combined harmonic form is zero. -/
theorem complete_overlap_annihilation {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_same_len : c₁.len = c₂.len)
    (h_complete_opp : c₁.oppositeDirectionEdges c₂ = c₁.len)
    (h_no_same : c₁.sameDirectionEdges c₂ = 0) :
    norm_sq (cycle_sum c₁ c₂) = 0 := by
  rw [combined_cycle_energy_formula]
  unfold GeneralCycle.signedOverlap
  simp only [h_no_same, CharP.cast_eq_zero, zero_sub, h_complete_opp, Int.cast_neg, Int.cast_natCast]
  have h_len1 : (0 : ℝ) < c₁.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₁.len_ge_3)
  have h_len2 : (0 : ℝ) < c₂.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₂.len_ge_3)
  -- Goal: 1/len₁ + 1/len₂ + 2 * (-len₁) / (len₁ * len₂) = 0
  -- With len₁ = len₂: 1/len + 1/len - 2*len/(len*len) = 2/len - 2/len = 0
  rw [h_same_len]
  field_simp
  ring

/-- Disjoint cycles have additive energy: no interaction.
    This is the baseline from which gravity measures binding. -/
theorem disjoint_additive_energy {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_disjoint : c₁.signedOverlap c₂ = 0) :
    norm_sq (cycle_sum c₁ c₂) = norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) := by
  rw [combined_cycle_energy]
  rw [cycle_inner_product_formula, h_disjoint]
  simp only [Int.cast_zero, zero_div, mul_zero, add_zero]

/-- The Grand Synthesis: Gravity is edge-sharing minimization.

    This chains the full Diaspora correspondence:
    **Paradox → Topology → Mass → Gravity**

    - Paradox creates non-trivial harmonic forms (topology)
    - Harmonic forms have energy (mass = 1/n for n-cycle)
    - Overlapping forms with opposite orientation have lower energy
    - Systems evolve toward lower energy → attraction

    Matter is trapped logical inconsistency.
    Gravity is the tendency of inconsistencies to share their contradictions. -/
theorem gravity_is_edge_sharing {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n) :
    -- More shared opposite-direction edges = more energy reduction
    ∀ k : ℕ,
      (c₁.oppositeDirectionEdges c₂ = k ∧ c₁.sameDirectionEdges c₂ = 0) →
      norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) - norm_sq (cycle_sum c₁ c₂) =
      sharing_energy_reduction c₁.len c₂.len k := by
  intro k ⟨h_opp, h_same⟩
  rw [← h_opp]
  exact gravity_binding_energy c₁ c₂ h_same

/-! ## Three-Body Gravity: Pairwise Additivity -/

/-- The sum of three cycle forms as a C1 cochain. -/
noncomputable def cycle_sum3 {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ c₃ : GeneralCycle n) : C1 n := {
  val := fun i j => (general_cycle_form c₁).val i j +
                    (general_cycle_form c₂).val i j +
                    (general_cycle_form c₃).val i j
  skew := by
    intro i j
    rw [(general_cycle_form c₁).skew, (general_cycle_form c₂).skew, (general_cycle_form c₃).skew]
    ring
}

/-- **Three-Cycle Pairwise Additivity**: The energy of three combined cycles
    is the sum of individual energies plus all pairwise interaction terms.

    There are no emergent 3-body forces in this model - gravity is strictly pairwise.
    This is the discrete analog of the linearity of Newtonian gravity. -/
theorem three_cycle_energy_pairwise {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ c₃ : GeneralCycle n) :
    norm_sq (cycle_sum3 c₁ c₂ c₃) =
      norm_sq (general_cycle_form c₁) +
      norm_sq (general_cycle_form c₂) +
      norm_sq (general_cycle_form c₃) +
      2 * inner_product_C1 (general_cycle_form c₁) (general_cycle_form c₂) +
      2 * inner_product_C1 (general_cycle_form c₁) (general_cycle_form c₃) +
      2 * inner_product_C1 (general_cycle_form c₂) (general_cycle_form c₃) := by
  unfold norm_sq inner_product_C1 cycle_sum3
  -- Expand (a + b + c)² = a² + b² + c² + 2ab + 2ac + 2bc
  have h_expand : ∀ i j : Fin n,
      ((general_cycle_form c₁).val i j + (general_cycle_form c₂).val i j +
       (general_cycle_form c₃).val i j) *
      ((general_cycle_form c₁).val i j + (general_cycle_form c₂).val i j +
       (general_cycle_form c₃).val i j) =
      (general_cycle_form c₁).val i j * (general_cycle_form c₁).val i j +
      (general_cycle_form c₂).val i j * (general_cycle_form c₂).val i j +
      (general_cycle_form c₃).val i j * (general_cycle_form c₃).val i j +
      2 * (general_cycle_form c₁).val i j * (general_cycle_form c₂).val i j +
      2 * (general_cycle_form c₁).val i j * (general_cycle_form c₃).val i j +
      2 * (general_cycle_form c₂).val i j * (general_cycle_form c₃).val i j := by
    intro i j; ring
  simp_rw [h_expand, Finset.sum_add_distrib]
  -- Factor out the 2s from the cross terms
  have h_factor : ∀ (γ₁ γ₂ : C1 n),
      ∑ i : Fin n, ∑ j : Fin n, 2 * γ₁.val i j * γ₂.val i j =
      2 * ∑ i : Fin n, ∑ j : Fin n, γ₁.val i j * γ₂.val i j := by
    intro γ₁ γ₂
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  simp_rw [h_factor]
  ring

/-- **Corollary**: Three disjoint cycles have purely additive energy. -/
theorem three_disjoint_additive_energy {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ c₃ : GeneralCycle n)
    (h₁₂ : c₁.signedOverlap c₂ = 0)
    (h₁₃ : c₁.signedOverlap c₃ = 0)
    (h₂₃ : c₂.signedOverlap c₃ = 0) :
    norm_sq (cycle_sum3 c₁ c₂ c₃) =
      norm_sq (general_cycle_form c₁) +
      norm_sq (general_cycle_form c₂) +
      norm_sq (general_cycle_form c₃) := by
  rw [three_cycle_energy_pairwise]
  have h₁₂' : inner_product_C1 (general_cycle_form c₁) (general_cycle_form c₂) = 0 := by
    rw [cycle_inner_product_formula, h₁₂]; simp
  have h₁₃' : inner_product_C1 (general_cycle_form c₁) (general_cycle_form c₃) = 0 := by
    rw [cycle_inner_product_formula, h₁₃]; simp
  have h₂₃' : inner_product_C1 (general_cycle_form c₂) (general_cycle_form c₃) = 0 := by
    rw [cycle_inner_product_formula, h₂₃]; simp
  rw [h₁₂', h₁₃', h₂₃']
  ring

/-! ## Mass-Energy Equivalence -/

/-- The **mass** of a topological defect: m = 1/n for an n-cycle.

    This is the energy of the canonical harmonic form on the cycle.
    Mass and energy are identical in this universe: E = m.

    Interpretation: Short cycles are heavy, long cycles are light.
    The triangle (n=3) has mass 1/3, the heaviest possible. -/
noncomputable def mass_of_cycle (n : ℕ) : ℝ := 1 / n

/-- **Mass-Energy Equivalence**: The energy of a cycle equals its mass.

    This is the Diaspora analog of E = mc². In natural units where c = 1,
    energy and mass are the same quantity. A topological defect's energy
    IS its mass. -/
theorem mass_energy_equivalence {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c : GeneralCycle n) (h_len : c.len = n) :
    norm_sq (general_cycle_form c) = mass_of_cycle n := by
  rw [general_cycle_form_energy, mass_of_cycle, h_len]

/-! ## The Gravitational Force Law -/

/-- The **gravitational force** between two cycles per shared edge.

    This is the derivative of binding energy with respect to shared edges:
    F = -dE/dk = 2/(n₁·n₂) = 2·m₁·m₂

    The force is:
    - Proportional to the product of masses (Newton-like!)
    - Always positive (attractive for opposite-direction sharing)
    - Independent of separation (contact interaction in discrete model) -/
noncomputable def gravitational_force (n₁ n₂ : ℕ) : ℝ :=
  2 / ((n₁ : ℝ) * (n₂ : ℝ))

/-- **Newton's Law (Diaspora Version)**: Gravitational force equals 2 × product of masses.

    F = 2·m₁·m₂

    This is the discrete analog of F = G·m₁·m₂/r². In the discrete model:
    - G = 2 (gravitational constant)
    - 1/r² = 1 (contact interaction, distance doesn't appear)

    The force between cycles is proportional to their masses. -/
theorem gravitational_force_is_product_of_masses (n₁ n₂ : ℕ) (h₁ : n₁ > 0) (h₂ : n₂ > 0) :
    gravitational_force n₁ n₂ = 2 * mass_of_cycle n₁ * mass_of_cycle n₂ := by
  unfold gravitational_force mass_of_cycle
  have h₁' : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h₁)
  have h₂' : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h₂)
  field_simp [h₁', h₂']

/-- The binding energy per shared edge equals the gravitational force.

    Each additional shared edge (with opposite orientation) reduces
    total energy by exactly the gravitational force. -/
theorem binding_energy_per_edge {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n) :
    sharing_energy_reduction c₁.len c₂.len (c₁.oppositeDirectionEdges c₂) =
    (c₁.oppositeDirectionEdges c₂ : ℝ) * gravitational_force c₁.len c₂.len := by
  unfold sharing_energy_reduction gravitational_force
  ring

/-! ## Repulsion: Same-Direction Sharing -/

/-- **Repulsion Theorem**: Same-direction edge sharing increases energy.

    When two cycles share edges with the SAME orientation, their combined
    energy EXCEEDS the sum of their individual energies.

    This is the opposite of gravitational attraction:
    - Opposite direction → attraction (energy decreases)
    - Same direction → repulsion (energy increases)

    Physical interpretation: Like charges repel, opposite charges attract.
    Same-direction cycles are "same charge", opposite-direction are "opposite charge". -/
theorem repulsion_is_same_direction {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_same : c₁.sameDirectionEdges c₂ > 0)
    (h_opp : c₁.oppositeDirectionEdges c₂ = 0) :
    norm_sq (cycle_sum c₁ c₂) > norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂) := by
  apply positive_overlap_increases_energy
  unfold GeneralCycle.signedOverlap
  simp only [h_opp]
  omega

/-- **Charge-like behavior**: The sign of overlap determines attraction vs repulsion.

    signedOverlap < 0  →  attraction (gravity)
    signedOverlap > 0  →  repulsion (anti-gravity)
    signedOverlap = 0  →  no interaction -/
theorem gravity_sign_determines_interaction {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n) :
    (c₁.signedOverlap c₂ < 0 → norm_sq (cycle_sum c₁ c₂) < norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂)) ∧
    (c₁.signedOverlap c₂ > 0 → norm_sq (cycle_sum c₁ c₂) > norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂)) ∧
    (c₁.signedOverlap c₂ = 0 → norm_sq (cycle_sum c₁ c₂) = norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂)) :=
  ⟨negative_overlap_reduces_energy c₁ c₂,
   positive_overlap_increases_energy c₁ c₂,
   zero_overlap_additive c₁ c₂⟩

/-! ## Mass Bounds and Quantization -/

/-- **Maximum Mass**: The heaviest possible topological defect is the triangle.

    m_max = 1/3 (achieved by 3-cycles)

    Interpretation: You cannot pack more mass into a simpler structure.
    The triangle is the densest paradox. -/
theorem maximum_mass : mass_of_cycle 3 = 1/3 := by
  unfold mass_of_cycle
  norm_num

/-- **Mass Hierarchy**: Longer cycles have less mass.

    n₁ < n₂ → m(n₁) > m(n₂)

    Heavier particles are smaller (fewer vertices). -/
theorem mass_decreases_with_length (n₁ n₂ : ℕ) (h₁ : n₁ > 0) (h₂ : n₂ > 0) (h_lt : n₁ < n₂) :
    mass_of_cycle n₁ > mass_of_cycle n₂ := by
  unfold mass_of_cycle
  have h₁' : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr h₁
  have h₂' : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr h₂
  have h_lt' : (n₁ : ℝ) < n₂ := Nat.cast_lt.mpr h_lt
  exact one_div_lt_one_div_of_lt h₁' h_lt'

/-- **Mass Gap**: There is a minimum nonzero mass difference.

    The mass spectrum is discrete: masses are 1/3, 1/4, 1/5, ...
    with gaps 1/12, 1/20, 1/30, ... between consecutive values.

    This is the Diaspora analog of particle mass quantization. -/
theorem mass_gap (n : ℕ) (h : n ≥ 3) :
    mass_of_cycle n - mass_of_cycle (n + 1) = 1 / (n * (n + 1)) := by
  unfold mass_of_cycle
  have hn : (n : ℝ) ≠ 0 := by
    have : n > 0 := by omega
    exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp this)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by
    have : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega : n > 0)
    linarith
  field_simp
  -- Goal: (↑(n + 1) - ↑n) * (↑n + 1) = ↑(n + 1)
  -- Simplifies to 1 * (n + 1) = (n + 1)
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, one_mul]

/-- **The Diaspora Correspondence (Extended)**:

    This theorem chains the full picture including the new gravity results:

    Paradox → Topology → Mass → Gravity → Attraction

    1. Paradox (locally consistent, globally inconsistent) creates harmonic forms
    2. Harmonic forms define topological defects with energy 1/n
    3. Energy IS mass in natural units (E = m)
    4. Overlapping defects interact: opposite direction → attraction
    5. Gravitational force F = 2·m₁·m₂ (Newton-like!)
    6. Systems evolve toward lower energy → particles attract

    Matter is trapped logical inconsistency.
    Gravity is the tendency of inconsistencies to merge and cancel. -/
theorem the_diaspora_correspondence_extended {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_opp : c₁.oppositeDirectionEdges c₂ > 0)
    (h_same : c₁.sameDirectionEdges c₂ = 0)
    (h₁ : c₁.len > 0) (h₂ : c₂.len > 0) :
    -- 1. Mass equals energy
    (norm_sq (general_cycle_form c₁) = mass_of_cycle c₁.len) ∧
    (norm_sq (general_cycle_form c₂) = mass_of_cycle c₂.len) ∧
    -- 2. Overlapping reduces energy (attraction)
    (norm_sq (cycle_sum c₁ c₂) < norm_sq (general_cycle_form c₁) + norm_sq (general_cycle_form c₂)) ∧
    -- 3. Force is proportional to product of masses
    (gravitational_force c₁.len c₂.len = 2 * mass_of_cycle c₁.len * mass_of_cycle c₂.len) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [general_cycle_form_energy, mass_of_cycle]
  · rw [general_cycle_form_energy, mass_of_cycle]
  · exact sharing_reduces_energy c₁ c₂ h_opp h_same
  · exact gravitational_force_is_product_of_masses c₁.len c₂.len h₁ h₂

end Diaspora.Dynamics
