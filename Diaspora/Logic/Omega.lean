import Diaspora.Logic.Theory
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Diaspora.Logic.Omega

open Diaspora.Logic BigOperators

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-! ## 1. Discretizing the Input (The "Coin Flips") -/

/-- Discrete constraint values: +1 or -1. -/
inductive DiscreteVal
| pos : DiscreteVal -- +1
| neg : DiscreteVal -- -1
deriving Fintype, DecidableEq

def val_to_real : DiscreteVal → ℝ
| DiscreteVal.pos => 1
| DiscreteVal.neg => -1

/-- An atomic constraint: source, destination, polarity. -/
structure AtomicConstraint (n : ℕ) where
  src : Fin n
  dst : Fin n
  pol : DiscreteVal
deriving Fintype, DecidableEq

/-- Alphabet size: 2n². -/
def alphabet_size (n : ℕ) : ℝ := 2 * (n : ℝ)^2

/-! ## 2. The Program (The Theory) -/

/-- A "Program" is just a list of atomic constraints. -/
def Program (n : ℕ) := List (AtomicConstraint n)

/-- Decoding a Program into a Theory (The "Compiler"). -/
def decode (P : Program n) : Theory n :=
  P.map (fun c => { src := c.src, dst := c.dst, val := val_to_real c.pol })

/-! ## 3. The Halting Condition -/

/-- Halting predicate: 1 if satisfiable, 0 otherwise. -/
def Halts (P : Program n) [Decidable (Satisfiable (decode P))] : ℕ :=
  if Satisfiable (decode P) then 1 else 0

/-! ## 4. Chaitin's Omega -/

/-- Probability weight of a program. -/
noncomputable def program_weight (P : Program n) : ℝ :=
  (1 / alphabet_size n) ^ P.length

/-- Programs of length k. -/
abbrev ProgramsOfLength (n k : ℕ) := Fin k → AtomicConstraint n

/-- Convert a fixed-length program to a list. -/
def toProgram {n k : ℕ} (f : ProgramsOfLength n k) : Program n :=
  List.ofFn f

/-- The Partial Omega for length k. -/
noncomputable def omega_at_length (k : ℕ) [∀ T : Theory n, Decidable (Satisfiable T)] : ℝ :=
  ∑ P : ProgramsOfLength n k, (program_weight (toProgram P)) * (Halts (toProgram P))

/-- The infinite sum over all program lengths. -/
noncomputable def Chaitins_Omega_Diaspora
    (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)]
    [∀ T : Theory n, Decidable (Satisfiable T)] : ℝ :=
  ∑' k : ℕ, omega_at_length (n := n) k

/-! ## 5. The Meaning of Life (Metabiology) -/

/-- 1 - Omega. -/
noncomputable def Probability_of_Genesis
  (omega : ℝ) : ℝ := 1 - omega

/-- If a locally consistent program does not halt, there exists non-trivial harmonic content. -/
theorem genesis_requires_topology
  (P : Program n) [Decidable (Satisfiable (decode P))]
  (h_cons : LocallyConsistent (decode P)) :
  (Halts P = 0) → ∃ γ, γ ∈ Diaspora.Hodge.HarmonicSubspace (theory_graph (decode P)) ∧ γ ≠ 0 := by
  intro h_loops
  have h_unsat : ¬ Satisfiable (decode P) := by
    by_contra h_sat
    simp [Halts, h_sat] at h_loops
  exact inconsistency_implies_topology (decode P) h_cons h_unsat

end Diaspora.Logic.Omega
