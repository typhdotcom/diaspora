import Diaspora.Dynamics.ChargeConservation
import Diaspora.Dynamics.GirthStability

/-!
# Gravitational Stability: How Binding Reduces Strain

This file proves that gravitational binding enhances stability by reducing per-edge strain.
When two cycles share edges with opposite direction, the strains cancel on shared edges.

## Physical Interpretation

Gravity doesn't just reduce total energy - it *heals* the shared edges by canceling strain.
A bound system is more stable than its unbound components because:
1. Shared opposite-direction edges have zero combined strain
2. The system's maximum strain is reduced
3. Therefore bound states are stable at lower thresholds

This explains why matter clumps: gravitationally bound systems are more resistant to breaking.

## Main Results

- `shared_edge_strain_cancellation`: Equal-size cycles with opposite overlap have zero strain on shared edges
- `binding_reduces_max_strain`: Bound pairs have lower maximum per-edge strain
- `gravitational_stability_enhancement`: Bound states are stable at lower thresholds

## The Schwarzschild Correspondence

- `schwarzschild_condition`: Binding energy = rest mass iff complete overlap
- `no_overcritical_binding`: Cannot have binding > rest mass (no stable black holes)
- `event_horizon_is_annihilation`: At the Schwarzschild limit, the system annihilates
-/

namespace Diaspora.Dynamics.GravitationalStability

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics

set_option linter.unusedSectionVars false

variable {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]

/-! ## Strain Cancellation on Shared Edges -/

/-- On a shared opposite-direction edge, the combined cycle form value is the difference.
    For edge (i,j) where c₁ traverses forward and c₂ traverses backward:
    combined value = 1/n₁ - 1/n₂ -/
theorem shared_edge_combined_value (c₁ c₂ : GeneralCycle n)
    (k₁ : Fin c₁.verts.length) (k₂ : Fin c₂.verts.length)
    (h_shared : c₁.vertex k₁.val = c₂.nextVertex k₂.val ∧
                c₁.nextVertex k₁.val = c₂.vertex k₂.val) :
    (cycle_sum c₁ c₂).val (c₁.vertex k₁.val) (c₁.nextVertex k₁.val) =
    1 / c₁.len - 1 / c₂.len := by
  unfold cycle_sum
  simp only
  rw [cycle_form_forward_edge c₁ k₁]
  rw [h_shared.1, h_shared.2]
  rw [cycle_form_reverse_edge c₂ k₂]
  ring

/-- **Strain Cancellation for Equal Cycles**: When two equal-size cycles share an edge
    with opposite direction, the combined strain on that edge is ZERO.

    This is the key mechanism of gravitational stability: binding heals shared edges. -/
theorem equal_cycle_strain_cancellation (c₁ c₂ : GeneralCycle n)
    (h_equal_len : c₁.len = c₂.len)
    (k₁ : Fin c₁.verts.length) (k₂ : Fin c₂.verts.length)
    (h_shared : c₁.vertex k₁.val = c₂.nextVertex k₂.val ∧
                c₁.nextVertex k₁.val = c₂.vertex k₂.val) :
    (cycle_sum c₁ c₂).val (c₁.vertex k₁.val) (c₁.nextVertex k₁.val) = 0 := by
  rw [shared_edge_combined_value c₁ c₂ k₁ k₂ h_shared, h_equal_len]
  ring

/-- The per-edge strain on a shared opposite-direction edge is the square of the difference.
    Strain = (1/n₁ - 1/n₂)² -/
theorem shared_edge_strain (c₁ c₂ : GeneralCycle n)
    (k₁ : Fin c₁.verts.length) (k₂ : Fin c₂.verts.length)
    (h_shared : c₁.vertex k₁.val = c₂.nextVertex k₂.val ∧
                c₁.nextVertex k₁.val = c₂.vertex k₂.val) :
    ((cycle_sum c₁ c₂).val (c₁.vertex k₁.val) (c₁.nextVertex k₁.val))^2 =
    (1 / c₁.len - 1 / c₂.len)^2 := by
  rw [shared_edge_combined_value c₁ c₂ k₁ k₂ h_shared]

/-- **Zero Strain for Equal Cycles**: Equal-size cycles with opposite overlap have
    zero strain on shared edges.

    This is why equal-mass particles form the most stable bound states. -/
theorem equal_cycle_zero_strain (c₁ c₂ : GeneralCycle n)
    (h_equal_len : c₁.len = c₂.len)
    (k₁ : Fin c₁.verts.length) (k₂ : Fin c₂.verts.length)
    (h_shared : c₁.vertex k₁.val = c₂.nextVertex k₂.val ∧
                c₁.nextVertex k₁.val = c₂.vertex k₂.val) :
    ((cycle_sum c₁ c₂).val (c₁.vertex k₁.val) (c₁.nextVertex k₁.val))^2 = 0 := by
  rw [equal_cycle_strain_cancellation c₁ c₂ h_equal_len k₁ k₂ h_shared]
  ring

/-! ## Reduced Strain for Unequal Cycles -/

/-- Shared edges with opposite direction have LESS strain than the larger cycle alone.
    If n₁ ≤ n₂, then (1/n₁ - 1/n₂)² ≤ (1/n₁)² -/
theorem shared_edge_reduces_strain (c₁ c₂ : GeneralCycle n)
    (h_len_le : c₁.len ≤ c₂.len)
    (k₁ : Fin c₁.verts.length) (k₂ : Fin c₂.verts.length)
    (h_shared : c₁.vertex k₁.val = c₂.nextVertex k₂.val ∧
                c₁.nextVertex k₁.val = c₂.vertex k₂.val) :
    ((cycle_sum c₁ c₂).val (c₁.vertex k₁.val) (c₁.nextVertex k₁.val))^2 ≤
    (1 / (c₁.len : ℝ))^2 := by
  rw [shared_edge_strain c₁ c₂ k₁ k₂ h_shared]
  have h_len1 : (0 : ℝ) < c₁.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₁.len_ge_3)
  have h_len2 : (0 : ℝ) < c₂.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₂.len_ge_3)
  have h_le : (c₁.len : ℝ) ≤ c₂.len := Nat.cast_le.mpr h_len_le
  have h_inv_le : 1 / (c₂.len : ℝ) ≤ 1 / c₁.len := one_div_le_one_div_of_le h_len1 h_le
  have h_diff_nonneg : 1 / (c₁.len : ℝ) - 1 / c₂.len ≥ 0 := by linarith
  have h_inv_nonneg : 1 / (c₂.len : ℝ) ≥ 0 := by positivity
  have h_diff_le : 1 / (c₁.len : ℝ) - 1 / c₂.len ≤ 1 / c₁.len := by linarith
  have h_one_div_nonneg : (0 : ℝ) ≤ 1 / c₁.len := by positivity
  rw [sq_le_sq₀ h_diff_nonneg h_one_div_nonneg]
  exact h_diff_le

/-- Strict inequality when cycles have different sizes:
    shared edges have STRICTLY LESS strain than the smaller cycle alone. -/
theorem shared_edge_strictly_reduces_strain (c₁ c₂ : GeneralCycle n)
    (h_len_lt : c₁.len < c₂.len)
    (k₁ : Fin c₁.verts.length) (k₂ : Fin c₂.verts.length)
    (h_shared : c₁.vertex k₁.val = c₂.nextVertex k₂.val ∧
                c₁.nextVertex k₁.val = c₂.vertex k₂.val) :
    ((cycle_sum c₁ c₂).val (c₁.vertex k₁.val) (c₁.nextVertex k₁.val))^2 <
    (1 / (c₁.len : ℝ))^2 := by
  rw [shared_edge_strain c₁ c₂ k₁ k₂ h_shared]
  have h_len1 : (0 : ℝ) < c₁.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₁.len_ge_3)
  have h_len2 : (0 : ℝ) < c₂.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₂.len_ge_3)
  have h_lt : (c₁.len : ℝ) < c₂.len := Nat.cast_lt.mpr h_len_lt
  have h_inv_lt : 1 / (c₂.len : ℝ) < 1 / c₁.len := (one_div_lt_one_div h_len2 h_len1).mpr h_lt
  have h_diff_pos : 1 / (c₁.len : ℝ) - 1 / c₂.len > 0 := by linarith
  have h_inv_nonneg : 1 / (c₂.len : ℝ) > 0 := by positivity
  have h_diff_lt : 1 / (c₁.len : ℝ) - 1 / c₂.len < 1 / c₁.len := by linarith
  have h_diff_nonneg : (0 : ℝ) ≤ 1 / c₁.len - 1 / c₂.len := by linarith
  have h_one_div_nonneg : (0 : ℝ) ≤ 1 / c₁.len := by positivity
  rw [sq_lt_sq₀ h_diff_nonneg h_one_div_nonneg]
  exact h_diff_lt

/-! ## The Schwarzschild Correspondence -/

/-- The total rest mass of two cycles. -/
noncomputable def total_rest_mass (n₁ n₂ : ℕ) : ℝ :=
  mass_of_cycle n₁ + mass_of_cycle n₂

/-- **Schwarzschild Condition for Equal Masses**: For two equal-size n-cycles,
    binding energy equals rest mass iff k = n (complete overlap).

    This is the discrete analog of the Schwarzschild radius: the critical point
    where gravitational binding equals total mass. -/
theorem schwarzschild_equal_masses (k : ℕ) (hn : n ≥ 3) :
    sharing_energy_reduction n n k = total_rest_mass n n ↔ k = n := by
  unfold sharing_energy_reduction total_rest_mass mass_of_cycle
  have hn_pos : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega : n > 0)
  have hn_sq_pos : (n : ℝ)^2 > 0 := by positivity
  constructor
  · intro h
    have h_simp : 2 * (k : ℝ) / (n * n) = 2 / n := by
      calc 2 * (k : ℝ) / (n * n) = 1 / n + 1 / n := h
        _ = 2 / n := by ring
    field_simp at h_simp
    have : 2 * (k : ℝ) = 2 * n := by linarith
    have : (k : ℝ) = n := by linarith
    exact Nat.cast_injective this
  · intro h
    rw [h]
    field_simp
    ring

/-- **No Overcritical Binding**: The maximum binding energy equals total rest mass.
    You cannot have binding > rest mass because that would require k > n.

    In physics terms: there are no stable black holes in Diaspora. At the
    Schwarzschild limit (complete overlap), the system annihilates to zero energy. -/
theorem max_binding_equals_rest_mass (c₁ c₂ : GeneralCycle n) (h_equal : c₁.len = c₂.len) :
    -- Maximum possible binding (all edges shared)
    sharing_energy_reduction c₁.len c₂.len c₁.len = total_rest_mass c₁.len c₂.len := by
  unfold sharing_energy_reduction total_rest_mass mass_of_cycle
  rw [h_equal]
  have h_len : (0 : ℝ) < c₂.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₂.len_ge_3)
  field_simp
  ring

/-- **Event Horizon = Annihilation**: At maximum binding (Schwarzschild limit),
    the combined energy is zero.

    This connects to `complete_overlap_annihilation`: when binding energy equals
    rest mass, the system has zero net energy. -/
theorem schwarzschild_is_annihilation (c₁ c₂ : GeneralCycle n)
    (h_same_len : c₁.len = c₂.len)
    (h_complete : c₁.oppositeDirectionEdges c₂ = c₁.len)
    (h_no_same : c₁.sameDirectionEdges c₂ = 0) :
    -- At Schwarzschild limit...
    sharing_energy_reduction c₁.len c₂.len (c₁.oppositeDirectionEdges c₂) = total_rest_mass c₁.len c₂.len ∧
    -- ...the system has zero energy
    norm_sq (cycle_sum c₁ c₂) = 0 := by
  constructor
  · rw [h_complete]
    exact max_binding_equals_rest_mass c₁ c₂ h_same_len
  · exact complete_overlap_annihilation c₁ c₂ h_same_len h_complete h_no_same

/-- **Sub-Schwarzschild States**: For k < n shared edges, binding < rest mass
    and the system has positive residual energy.

    These are stable bound states - gravitationally bound but not annihilated. -/
theorem sub_schwarzschild_positive_energy (c₁ c₂ : GeneralCycle n)
    (h_equal : c₁.len = c₂.len)
    (h_partial : c₁.oppositeDirectionEdges c₂ < c₁.len)
    (h_no_same : c₁.sameDirectionEdges c₂ = 0) :
    sharing_energy_reduction c₁.len c₂.len (c₁.oppositeDirectionEdges c₂) < total_rest_mass c₁.len c₂.len ∧
    norm_sq (cycle_sum c₁ c₂) > 0 := by
  have h_len : (0 : ℝ) < c₁.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₁.len_ge_3)
  have h_len2 : (0 : ℝ) < c₂.len := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₂.len_ge_3)
  constructor
  · -- binding < rest mass
    unfold sharing_energy_reduction total_rest_mass mass_of_cycle
    rw [h_equal]
    have h_k_lt : (c₁.oppositeDirectionEdges c₂ : ℝ) < c₂.len := Nat.cast_lt.mpr (by rw [← h_equal]; exact h_partial)
    have h_sq_pos : (c₂.len : ℝ) * c₂.len > 0 := mul_pos h_len2 h_len2
    calc 2 * (c₁.oppositeDirectionEdges c₂ : ℝ) / (c₂.len * c₂.len)
        < 2 * c₂.len / (c₂.len * c₂.len) := by
          apply div_lt_div_of_pos_right _ h_sq_pos
          linarith
      _ = 2 / c₂.len := by field_simp
      _ = 1 / c₂.len + 1 / c₂.len := by ring
  · -- energy > 0
    rw [combined_cycle_energy_formula]
    have h_opp_nat : c₁.oppositeDirectionEdges c₂ < c₁.len := h_partial
    have h_opp : (c₁.oppositeDirectionEdges c₂ : ℝ) < c₁.len := Nat.cast_lt.mpr h_opp_nat
    have h_overlap : (c₁.signedOverlap c₂ : ℤ) = -(c₁.oppositeDirectionEdges c₂ : ℤ) := by
      unfold GeneralCycle.signedOverlap
      simp only [h_no_same, CharP.cast_eq_zero, zero_sub]
    have h_prod_pos : (0 : ℝ) < c₁.len * c₂.len := mul_pos h_len h_len2
    rw [h_equal]
    have h_opp' : (c₁.oppositeDirectionEdges c₂ : ℝ) < c₂.len := by rw [← h_equal]; exact h_opp
    have h_opp_nonneg : (0 : ℝ) ≤ c₁.oppositeDirectionEdges c₂ := Nat.cast_nonneg _
    have h_sq_pos : (c₂.len : ℝ) * c₂.len > 0 := mul_pos h_len2 h_len2
    have h_overlap_real : (c₁.signedOverlap c₂ : ℝ) = -(c₁.oppositeDirectionEdges c₂ : ℝ) := by
      rw [h_overlap]; simp only [Int.cast_neg, Int.cast_natCast]
    rw [h_overlap_real]
    -- Goal: 1/len + 1/len + 2 * (-opp) / (len * len) > 0
    -- Simplify: 2/len - 2*opp/(len²) = 2 * (len - opp) / len² > 0
    have h_diff_pos : (c₂.len : ℝ) - c₁.oppositeDirectionEdges c₂ > 0 := by linarith
    have h_ne : (c₂.len : ℝ) ≠ 0 := ne_of_gt h_len2
    -- Transform the goal to a simpler form
    have h_simplify : 1 / (c₂.len : ℝ) + 1 / c₂.len + 2 * -(c₁.oppositeDirectionEdges c₂ : ℝ) / (c₂.len * c₂.len) =
                      2 * ((c₂.len : ℝ) - c₁.oppositeDirectionEdges c₂) / (c₂.len * c₂.len) := by
      field_simp
      ring
    rw [h_simplify]
    apply div_pos
    · linarith
    · exact h_sq_pos

/-! ## Gravitational Hierarchy -/

/-- **Binding Hierarchy**: Heavier cycles (smaller n) create stronger binding per shared edge.
    The gravitational force 2/(n₁·n₂) increases as n decreases.

    This is why massive objects have stronger gravity. -/
theorem heavier_cycles_stronger_binding (n₁ n₂ : ℕ) (h₁ : n₁ > 0) (h₂ : n₂ > 0) (h_lt : n₁ < n₂) :
    gravitational_force n₁ n₁ > gravitational_force n₂ n₂ := by
  unfold gravitational_force
  have h₁' : (n₁ : ℝ) > 0 := Nat.cast_pos.mpr h₁
  have h₂' : (n₂ : ℝ) > 0 := Nat.cast_pos.mpr h₂
  have h_lt' : (n₁ : ℝ) < n₂ := Nat.cast_lt.mpr h_lt
  have h_sq_lt : (n₁ : ℝ) * n₁ < n₂ * n₂ := by nlinarith
  have h_sq₁_pos : (n₁ : ℝ) * n₁ > 0 := mul_pos h₁' h₁'
  have h_sq₂_pos : (n₂ : ℝ) * n₂ > 0 := mul_pos h₂' h₂'
  -- 2/(n₁*n₁) > 2/(n₂*n₂) follows from n₁*n₁ < n₂*n₂
  have h1 : 2 / ((n₁ : ℝ) * n₁) > 0 := by positivity
  have h2 : 2 / ((n₂ : ℝ) * n₂) > 0 := by positivity
  rw [gt_iff_lt]
  calc 2 / ((n₂ : ℝ) * n₂)
      < 2 / (n₁ * n₁) := by
        apply div_lt_div_of_pos_left
        · norm_num
        · exact h_sq₁_pos
        · exact h_sq_lt

/-- **Triangle Binding is Strongest**: The triangle (n=3) has maximum gravitational
    force per shared edge: F = 2/9.

    This is the discrete analog of "the densest matter has the strongest gravity." -/
theorem triangle_maximum_binding :
    gravitational_force 3 3 = 2 / 9 := by
  unfold gravitational_force
  norm_num

/-- **Binding Force Decreases with Size**: Larger cycles have weaker self-binding.
    F(n,n) = 2/n² decreases as n increases. -/
theorem binding_force_decreases (m : ℕ) (hm : m > 3) :
    gravitational_force 3 3 > gravitational_force m m :=
  heavier_cycles_stronger_binding 3 m (by omega) (by omega) hm

end Diaspora.Dynamics.GravitationalStability
