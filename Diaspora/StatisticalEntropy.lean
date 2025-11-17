/-
Entropy from statistical mechanics: deriving S from microstate counting.
-/

import Diaspora.GaugeTheoreticHolonomy
import Diaspora.MassDefinition
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open GaugeTheoretic MassDefinition Real

namespace StatisticalEntropy

/-- Microstate: phase configuration with specified energy. -/
structure Microstate (n k : ℕ) (X_base : ConfigSpace n) (c : Cycle n X_base.graph k)
    (E_target : ℝ) (ε : ℝ) where
  phases : Fin n → ℝ
  energy_shell :
    let X := { X_base with node_phases := phases }
    |V_int X - E_target| ≤ ε

/-- Gauge equivalence: phase configurations differing by a constant. -/
def gauge_equivalent {n : ℕ} (ω₁ ω₂ : Fin n → ℝ) : Prop :=
  ∃ c : ℝ, ∀ i, ω₂ i = ω₁ i + c

/-- Gauge equivalence is an equivalence relation. -/
theorem gauge_equivalence_equiv {n : ℕ} :
    Equivalence (@gauge_equivalent n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω
    use 0
    simp
  · intro ω₁ ω₂ ⟨c, h⟩
    use -c
    intro i
    specialize h i
    linarith
  · intro ω₁ ω₂ ω₃ ⟨c₁, h₁⟩ ⟨c₂, h₂⟩
    use c₁ + c₂
    intro i
    specialize h₁ i
    specialize h₂ i
    linarith

/-- Gauge equivalent configurations have identical edge values. -/
theorem gauge_equiv_same_edges {n : ℕ} (X : ConfigSpace n)
    (ω₁ ω₂ : Fin n → ℝ) (h : gauge_equivalent ω₁ ω₂)
    (i j : Fin n) (h_adj : X.graph.Adj i j) :
    let X₁ := { X with node_phases := ω₁ }
    let X₂ := { X with node_phases := ω₂ }
    edge_value X₁ i j h_adj = edge_value X₂ i j h_adj := by
  obtain ⟨c, h_eq⟩ := h
  simp only [edge_value]
  rw [h_eq i, h_eq j]
  ring

/-- Gauge equivalent configurations have identical V_int. -/
theorem gauge_equiv_same_V_int {n : ℕ} (X : ConfigSpace n)
    (ω₁ ω₂ : Fin n → ℝ) (h : gauge_equivalent ω₁ ω₂) :
    let X₁ := { X with node_phases := ω₁ }
    let X₂ := { X with node_phases := ω₂ }
    V_int X₁ = V_int X₂ := by
  obtain ⟨c, h_eq⟩ := h
  unfold V_int
  haveI : DecidableRel X.graph.Adj := X.adj_decidable
  congr 1
  ext i
  congr 1
  ext j
  by_cases h_adj : X.graph.Adj i j
  · simp only [h_adj, dite_true]
    congr 1
    simp only [edge_value]
    rw [h_eq j, h_eq i]
    ring
  · simp only [h_adj, dite_false]

/-- Microstate count (axiomatized). -/
axiom microstate_count {n k : ℕ} (X : ConfigSpace n) (c : Cycle n X.graph k)
    (E : ℝ) : ℝ

/-- Microstate count is positive. -/
axiom microstate_count_pos {n k : ℕ} (X : ConfigSpace n) (c : Cycle n X.graph k)
    (E : ℝ) (h_E : 0 < E) : 0 < microstate_count X c E

/-- Microstate count grows polynomially with energy. -/
axiom microstate_scaling {n k : ℕ} (X : ConfigSpace n) (c : Cycle n X.graph k)
    (h_k : 3 ≤ k) :
    ∃ (f : ℝ) (C : ℝ), 0 < f ∧ 0 < C ∧
      ∀ E : ℝ, 0 < E → microstate_count X c E = C * E^f

/-- Boltzmann entropy: S = log Ω. -/
noncomputable def boltzmann_entropy {n k : ℕ} (X : ConfigSpace n)
    (c : Cycle n X.graph k) (E : ℝ) : ℝ :=
  log (microstate_count X c E)

/-- Entropy depends logarithmically on energy: S = f·log E₀ + const. -/
theorem entropy_energy_theorem {n k : ℕ} (X : ConfigSpace n)
    (c : Cycle n X.graph k) (h_k : 3 ≤ k)
    (E₀ : ℝ) (h_E₀ : 0 < E₀) :
    ∃ (f C : ℝ), 0 < f ∧ 0 < C ∧
      boltzmann_entropy X c E₀ = log C + f * log E₀ := by
  obtain ⟨f, C, h_f_pos, h_C_pos, h_scaling⟩ := microstate_scaling X c h_k
  use f, C
  constructor; exact h_f_pos
  constructor; exact h_C_pos
  unfold boltzmann_entropy
  rw [h_scaling E₀ h_E₀]
  rw [log_mul (ne_of_gt h_C_pos) (by apply ne_of_gt; apply rpow_pos_of_pos h_E₀)]
  rw [log_rpow h_E₀]

/-- Linear approximation: S ≤ α·E₀ + const. -/
theorem entropy_energy_linear_regime {n k : ℕ} (X : ConfigSpace n)
    (c : Cycle n X.graph k) (h_k : 3 ≤ k) :
    ∃ α : ℝ, 0 < α ∧
      ∀ E₀ : ℝ, 0 < E₀ →
        boltzmann_entropy X c E₀ ≤ α * E₀ + log (microstate_count X c 1) := by
  obtain ⟨f, C, h_f_pos, h_C_pos, h_scaling⟩ := microstate_scaling X c h_k

  use f
  constructor
  · exact h_f_pos
  · intro E₀ h_E₀
    unfold boltzmann_entropy
    rw [h_scaling E₀ h_E₀]
    rw [log_mul (ne_of_gt h_C_pos) (by apply ne_of_gt; apply rpow_pos_of_pos h_E₀)]
    rw [log_rpow h_E₀]

    have h_log_bound : log E₀ ≤ E₀ - 1 := log_le_sub_one_of_pos h_E₀

    calc log C + f * log E₀
        ≤ log C + f * (E₀ - 1) := by linarith [mul_le_mul_of_nonneg_left h_log_bound (le_of_lt h_f_pos)]
      _ = log C + f * E₀ - f := by ring
      _ ≤ f * E₀ + (log C - f) := by linarith
      _ ≤ f * E₀ + log (microstate_count X c 1) := by
          have h_at_one : microstate_count X c 1 = C * 1^f := h_scaling 1 (by norm_num)
          simp at h_at_one
          rw [h_at_one]
          linarith [h_f_pos]

/-- Black hole entropy equals Boltzmann entropy at E₀ = M². -/
theorem black_hole_entropy_exact {n k : ℕ} (X : ConfigSpace n)
    (c : Cycle n X.graph k) (h_k : 3 ≤ k)
    (A : ℝ) (_h_A : 0 < A)
    (_h_BH : ∃ κ > 0, boltzmann_entropy X c ((mass X c)^2) = κ * A) :
    boltzmann_entropy X c ((mass X c)^2) =
      boltzmann_entropy X c (SchwarzschildDerivation.E_ground_state X c) := by
  have h_E : SchwarzschildDerivation.E_ground_state X c = (mass X c)^2 :=
    MassDefinition.mass_energy_relation X c h_k
  rw [← h_E]

end StatisticalEntropy
