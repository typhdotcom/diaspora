import Diaspora.Logic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Diaspora.Logic.Genesis

open Diaspora.Logic Diaspora.Logic.Omega

/-! ## 1. The Setup: A Universe of 3 Nodes -/

/-- We work in a universe with 3 vertices (Fin 3). -/
abbrev n_gen : ℕ := 3

/-! ## 2. The Program: "Let there be Rotation" -/

/-- The genesis program: three rising edges forming a cycle. -/
def rotational_program : Program n_gen := [
  { src := 0, dst := 1, pol := .pos },
  { src := 1, dst := 2, pol := .pos },
  { src := 2, dst := 0, pol := .pos }
]

/--
The constraints decoded into the Theory.
-/
lemma decode_genesis : decode rotational_program = [
  { src := 0, dst := 1, val := 1 },
  { src := 1, dst := 2, val := 1 },
  { src := 2, dst := 0, val := 1 }
] := rfl

/-! ## 3. The Proof of Impossibility (The Spark) -/

/-- The genesis program is unsatisfiable (sum around loop is 3, not 0). -/
theorem genesis_is_unsatisfiable :
  ¬ Satisfiable (decode rotational_program) := by
  intro h_sat
  -- 1. Unpack the model ϕ
  unfold Satisfiable at h_sat
  obtain ⟨ϕ, h_model⟩ := h_sat

  -- 2. Extract the three laws
  rw [decode_genesis] at h_model
  have h1 : ϕ 1 - ϕ 0 = 1 := by
    apply h_model { src := 0, dst := 1, val := 1 }
    exact .head _
  have h2 : ϕ 2 - ϕ 1 = 1 := by
    apply h_model { src := 1, dst := 2, val := 1 }
    exact .tail _ (.head _)
  have h3 : ϕ 0 - ϕ 2 = 1 := by
    apply h_model { src := 2, dst := 0, val := 1 }
    exact .tail _ (.tail _ (.head _))

  -- 3. The Summation (Kirchhoff's Law)
  -- If we walk the loop, the potential differences must sum to 0.
  have h_sum_zero : (ϕ 1 - ϕ 0) + (ϕ 2 - ϕ 1) + (ϕ 0 - ϕ 2) = 0 := by
    ring

  -- 4. The Contradiction
  -- But our laws say they sum to 1 + 1 + 1 = 3.
  have h_sum_three : (ϕ 1 - ϕ 0) + (ϕ 2 - ϕ 1) + (ϕ 0 - ϕ 2) = 3 := by
    rw [h1, h2, h3]
    ring

  -- 5. 0 ≠ 3
  rw [h_sum_zero] at h_sum_three
  norm_num at h_sum_three

/-! ## 4. The Existence of Mass -/

/-- The genesis program is locally consistent. -/
lemma genesis_is_consistent : LocallyConsistent (decode rotational_program) := by
  unfold LocallyConsistent
  intro c1 h1 c2 h2
  rw [decode_genesis] at h1 h2
  refine ⟨?_, ?_⟩ <;> intro ⟨hsrc, hdst⟩
  -- All cases: iterate cases until fixed point, then simp_all
  all_goals (cases h1 <;> cases h2 <;> (repeat' (rename_i h; cases h)) <;> simp_all)

/-- Unsatisfiability implies nonzero harmonic form. -/
theorem structure_is_mandatory :
  ∃ γ, γ ∈ Diaspora.Hodge.HarmonicSubspace (theory_graph (decode rotational_program)) ∧ γ ≠ 0 := by
  apply inconsistency_implies_topology
  · exact genesis_is_consistent
  · exact genesis_is_unsatisfiable

end Diaspora.Logic.Genesis
