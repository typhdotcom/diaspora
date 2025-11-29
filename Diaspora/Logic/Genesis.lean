import Diaspora.Logic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Diaspora.Logic.Genesis

open Diaspora.Logic Diaspora.Logic.Omega

/-! ## 1. The Setup: A Universe of 3 Nodes -/

/-- We work in a universe with 3 vertices (Fin 3). -/
abbrev n_gen : ℕ := 3

/-! ## 2. The Program: "Let there be Rotation" -/

/--
The "Genesis Program" is a simple sequence of 3 commands:
1.  0 → 1 must rise (+1)
2.  1 → 2 must rise (+1)
3.  2 → 0 must rise (+1)

It is the request for an Escher staircase.
-/
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

/--
This theorem proves that the Genesis Program contains a logical contradiction
that cannot be resolved by scalar potentials.
-/
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

/--
The Program defines a consistent local graph (it forms a cycle 0-1-2).
(Proof omitted for brevity, but trivial: 0!=1, 1!=2, 2!=0).
-/
lemma genesis_is_consistent : LocallyConsistent (decode rotational_program) := by
  unfold LocallyConsistent
  intro c1 h1 c2 h2
  rw [decode_genesis] at h1 h2
  refine ⟨?_, ?_⟩ <;> intro ⟨hsrc, hdst⟩
  -- All cases: iterate cases until fixed point, then simp_all
  all_goals (cases h1 <;> cases h2 <;> (repeat' (rename_i h; cases h)) <;> simp_all)

/--
**THE GENESIS THEOREM**
Because the Rotational Program does not Halt (is unsatisfiable),
the Universe *must* generate a non-zero Harmonic Form.

The logical contradiction (0 = 3) is converted into physical structure (γ).
-/
theorem structure_is_mandatory :
  ∃ γ, γ ∈ Diaspora.Hodge.HarmonicSubspace (theory_graph (decode rotational_program)) ∧ γ ≠ 0 := by
  apply inconsistency_implies_topology
  · exact genesis_is_consistent
  · exact genesis_is_unsatisfiable

end Diaspora.Logic.Genesis
