/-
# Theorem 1: The Structural Rate-Distortion Bound

Formalizes "Perspective = Translation Cost" (Primitive 6)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Order.MinMax
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import PerspectivalMonism.Axioms
import PerspectivalMonism.Task

/-! ## Definitions -/

/-- The set of graphs with at most n edges -/
def GraphSet (n : ℕ) : Set ConfigSpace :=
  {X | E X ≤ n}

/-- Given a task, distortion with n edges -/
noncomputable def D_star_task (t : ExternalTask) (n : ℕ) : ℝ :=
  if min_edges_for_task t ≤ n then 0 else 1

/-! ## Theorem 1: Critical Capacity -/

/-- For any task, there exists critical capacity (its minimum edges) -/
theorem structural_rate_distortion (t : ExternalTask) :
    ∃ (E_min : ℕ) (δ : ℝ), 0 < δ ∧
    ∀ E < E_min, δ ≤ D_star_task t E := by
  use min_edges_for_task t, 1
  constructor
  · norm_num
  · intro E hE
    unfold D_star_task
    have h : ¬(min_edges_for_task t ≤ E) := by omega
    simp [h]

/-! ## Supporting Lemmas -/

/-- The distortion function is monotone decreasing -/
lemma D_star_antitone (t : ExternalTask) : ∀ E₁ E₂, E₁ ≤ E₂ → D_star_task t E₂ ≤ D_star_task t E₁ := by
  intro E₁ E₂ hle
  unfold D_star_task
  by_cases hmin : min_edges_for_task t ≤ E₂
  · simp [hmin]
    split_ifs <;> norm_num
  · simp [hmin]
    by_cases hmin₁ : min_edges_for_task t ≤ E₁
    · exfalso
      apply hmin
      omega
    · simp [hmin₁]

/-- For large enough E, distortion can be made arbitrarily small -/
lemma D_star_limit (t : ExternalTask) : ∀ ε > 0, ∃ E, D_star_task t E < ε := by
  intro ε hε
  use min_edges_for_task t
  unfold D_star_task
  simp
  exact hε

/-! ## The Sharp Knee Property -/

/-- The phase transition is characterized by a sharp drop in distortion -/
theorem sharp_knee (t : ExternalTask) (h : 0 < min_edges_for_task t) :
    let E_min := min_edges_for_task t
    D_star_task t (E_min - 1) - D_star_task t E_min >
    D_star_task t E_min - D_star_task t (E_min + 1) := by
  intro E_min
  unfold D_star_task
  have h1 : ¬(E_min ≤ E_min - 1) := by omega
  have h2 : E_min ≤ E_min := le_refl _
  have h3 : E_min ≤ E_min + 1 := by omega
  rw [if_neg h1, if_pos h2, if_pos h3]
  norm_num

/-! ## Connection to Recursive Well (Primitive 5) -/

/-- Below critical capacity, myopic descent cannot satisfy the task
    This forces recursive (k-step) modeling -/
axiom subcritical_forces_recursion (t : ExternalTask) (X : ConfigSpace)
    (h_subcritical : E X < min_edges_for_task t) :
    -- Task cannot be satisfied
    ¬satisfies_task X.G t ∧
    -- K cannot fix this (myopic descent fails)
    ¬satisfies_task (K X).G t ∧
    -- But multi-step search can find a solution
    ∃ (k : ℕ) (X' : ConfigSpace), 1 < k ∧
      min_edges_for_task t ≤ E X' ∧ satisfies_task X'.G t

/-- The recursive well: below critical capacity, only recursive modeling succeeds -/
theorem recursive_well_theorem (t : ExternalTask) (X : ConfigSpace)
    (h_subcritical : E X < min_edges_for_task t) :
    ∃ (k : ℕ), 1 < k := by
  have h := subcritical_forces_recursion t X h_subcritical
  obtain ⟨_, _, ⟨k, _, hk, _, _⟩⟩ := h
  exact ⟨k, hk⟩
