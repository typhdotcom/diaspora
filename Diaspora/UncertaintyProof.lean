/-
# Concrete Proof of Geometric Uncertainty Principle

Shows that incompatible structural requirements force bounded product of errors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Diaspora.Axioms
import Diaspora.Task

open Classical

/-! ## Definitions -/

/-- Two external costs representing incompatible gauge requirements -/
structure IncommensurableGauges where
  V_ext_X : ConfigSpace → ℝ
  V_ext_P : ConfigSpace → ℝ
  V_X_nonneg : ∀ G, 0 ≤ V_ext_X G
  V_P_nonneg : ∀ G, 0 ≤ V_ext_P G

/-- Two gauge requirements are structurally incompatible if they demand
    conflicting topological properties -/
def structurally_incompatible (gauges : IncommensurableGauges) : Prop :=
  ∃ (property_X property_P : ConfigSpace → Prop),
  (∀ G, gauges.V_ext_X G < ε → property_X G) ∧
  (∀ G, gauges.V_ext_P G < ε → property_P G) ∧
  (∀ G, property_X G → ¬property_P G)
  where ε := 0.1

/-! ## Numeric Helpers -/

lemma one_not_lt_tenth : ¬(1:ℝ) < (1:ℝ) / 10 := by norm_num

lemma one_not_lt_tenth_inv : ¬(1:ℝ) < (10:ℝ)⁻¹ := by norm_num

lemma one_not_lt_point_one : ¬(1:ℝ) < 0.1 := by norm_num

lemma tenth_le_one : (1:ℝ) / 10 ≤ 1 := by norm_num

/-! ## Setup: Incompatible Gauge Requirements -/

/-- A task requiring planar structure -/
def planar_task : ExternalTask where
  required_paths := [(0, 1), (1, 2)]
  required_cycles := []

/-- Planarity is a topological property -/
axiom is_planar : Graph → Prop

/-- Planar graphs can't satisfy non-planar tasks -/
axiom planar_excludes_K5 (G : Graph) :
  is_planar G → ¬satisfies_task G nonplanar_task

/-- Non-planar graphs satisfying K5 can't be planar -/
theorem K5_not_planar (G : Graph) :
  satisfies_task G nonplanar_task → ¬is_planar G :=
  fun h_sat h_planar => planar_excludes_K5 G h_planar h_sat

/-! ## Gauge Structure -/

/-- External cost for planarity gauge -/
noncomputable def V_planar (X : ConfigSpace) : ℝ :=
  if is_planar X.G then 0 else 1

/-- External cost for non-planarity gauge -/
noncomputable def V_nonplanar (X : ConfigSpace) : ℝ :=
  if satisfies_task X.G nonplanar_task then 0 else 1

/-- The planar/non-planar gauges are incommensurable -/
noncomputable def planar_gauges : IncommensurableGauges where
  V_ext_X := V_planar
  V_ext_P := V_nonplanar
  V_X_nonneg := by
    intro G
    unfold V_planar
    by_cases h : is_planar G.G <;> simp [h]
  V_P_nonneg := by
    intro G
    unfold V_nonplanar
    by_cases h : satisfies_task G.G nonplanar_task <;> simp [h]

/-! ## Structural Incompatibility Proof -/

/-- Planar and non-planar requirements are structurally incompatible -/
theorem planar_nonplanar_incompatible :
    structurally_incompatible planar_gauges := by
  unfold structurally_incompatible planar_gauges V_planar V_nonplanar
  use fun X => is_planar X.G, fun X => satisfies_task X.G nonplanar_task
  refine ⟨?_, ?_, ?_⟩
  · intro G hG
    by_cases h : is_planar G.G
    · exact h
    · simp [h] at hG
      exact absurd hG one_not_lt_point_one
  · intro G hG
    by_cases h : satisfies_task G.G nonplanar_task
    · exact h
    · simp [h] at hG
      exact absurd hG one_not_lt_point_one
  · intro G hplanar
    exact planar_excludes_K5 G.G hplanar

/-! ## Uncertainty Bound Proof -/

/-- Can't have both planar and non-planar simultaneously -/
theorem planar_mutual_exclusion :
    ∀ G : ConfigSpace,
    V_planar G < (1:ℝ) / 10 → ¬(V_nonplanar G < (1:ℝ) / 10) := by
  intro G hplanar
  unfold V_planar at hplanar
  by_cases hp : is_planar G.G
  · simp [hp] at hplanar
    intro hnonplanar
    unfold V_nonplanar at hnonplanar
    by_cases hnp : satisfies_task G.G nonplanar_task
    · simp [hnp] at hnonplanar
      exact planar_excludes_K5 G.G hp hnp
    · simp [hnp] at hnonplanar
      exact absurd hnonplanar one_not_lt_tenth_inv
  · simp [hp] at hplanar
    exact absurd hplanar one_not_lt_tenth_inv

/-- Uncertainty bound: at least one cost is large -/
theorem planar_uncertainty_bound :
    ∀ G : ConfigSpace,
    (1:ℝ) / 10 ≤ V_planar G ∨ (1:ℝ) / 10 ≤ V_nonplanar G := by
  intro G
  by_cases hp : is_planar G.G
  · right
    unfold V_nonplanar
    by_cases hnp : satisfies_task G.G nonplanar_task
    · exfalso
      exact planar_excludes_K5 G.G hp hnp
    · simp only [hnp, ite_false]
      exact tenth_le_one
  · left
    unfold V_planar
    simp only [hp, ite_false]
    exact tenth_le_one

/-- The geometric uncertainty principle for planar gauges -/
theorem planar_geometric_uncertainty :
    ∃ Ω > 0, ∀ G : ConfigSpace,
    planar_gauges.V_ext_X G < Ω → Ω ≤ planar_gauges.V_ext_P G := by
  use (1:ℝ) / 10
  constructor
  · norm_num
  · intro G hX
    have h := planar_mutual_exclusion G
    unfold planar_gauges at hX
    exact le_of_not_gt (h hX)
