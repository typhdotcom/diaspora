import Diaspora.Logic.Theory
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Diaspora.Logic.Omega

open Diaspora.Logic BigOperators

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-! ## 1. Discretizing the Input (The "Coin Flips") -/

/--
To calculate a probability, we restrict our "Program Space" to a discrete set.
Instead of Real values, our constraints can only be {-1, 1} (e.g., "Pull Left" or "Pull Right").
-/
inductive DiscreteVal
| pos : DiscreteVal -- +1
| neg : DiscreteVal -- -1
deriving Fintype, DecidableEq

def val_to_real : DiscreteVal → ℝ
| DiscreteVal.pos => 1
| DiscreteVal.neg => -1

/--
A "Bit" of information in this universe is a choice of:
1. A source node
2. A destination node
3. A polarity (positive or negative)
-/
structure AtomicConstraint (n : ℕ) where
  src : Fin n
  dst : Fin n
  pol : DiscreteVal
deriving Fintype, DecidableEq

/--
The "Alphabet Size" of our universe language.
K = 2 * n * n
-/
def alphabet_size (n : ℕ) : ℝ := 2 * (n : ℝ)^2

/-! ## 2. The Program (The Theory) -/

/-- A "Program" is just a list of atomic constraints. -/
def Program (n : ℕ) := List (AtomicConstraint n)

/-- Decoding a Program into a Theory (The "Compiler"). -/
def decode (P : Program n) : Theory n :=
  P.map (fun c => { src := c.src, dst := c.dst, val := val_to_real c.pol })

/-! ## 3. The Halting Condition -/

/--
"Does it Halt?"
In Chaitin: Does the Turing machine stop?
In Diaspora: Does the Energy relax to Zero? (Is it Satisfiable?)

Note: We assume Decidable Satisfiability here (via Gaussian elimination),
which is true for finite linear systems.
-/
def Halts (P : Program n) [Decidable (Satisfiable (decode P))] : ℕ :=
  if Satisfiable (decode P) then 1 else 0

/-! ## 4. Chaitin's Omega -/

/--
The probability weight of a specific program of length k.
If we pick constraints uniformly at random, the probability of generating
exactly program P is (1/AlphabetSize)^k.
-/
noncomputable def program_weight (P : Program n) : ℝ :=
  (1 / alphabet_size n) ^ P.length

/--
All programs of a given length k (vectors of k atomic constraints).
-/
abbrev ProgramsOfLength (n k : ℕ) := Fin k → AtomicConstraint n

/-- Convert a fixed-length program to a list. -/
def toProgram {n k : ℕ} (f : ProgramsOfLength n k) : Program n :=
  List.ofFn f

/--
The Partial Omega for length k.
Sum of weights of all programs of length k that Halt (Relax to Zero).
-/
noncomputable def omega_at_length (k : ℕ) [∀ T : Theory n, Decidable (Satisfiable T)] : ℝ :=
  ∑ P : ProgramsOfLength n k, (program_weight (toProgram P)) * (Halts (toProgram P))

/--
The "Probability of Triviality".
This number encodes the density of logical consistency in your topology.
Defined as the infinite sum over all program lengths.
-/
noncomputable def Chaitins_Omega_Diaspora
    (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)]
    [∀ T : Theory n, Decidable (Satisfiable T)] : ℝ :=
  ∑' k : ℕ, omega_at_length (n := n) k

/-! ## 5. The Meaning of Life (Metabiology) -/

/--
If Omega is the probability of Halting (Death/Stasis),
then (1 - Omega) is the probability of Genesis.
-/
noncomputable def Probability_of_Genesis
  (omega : ℝ) : ℝ := 1 - omega

/--
If a locally consistent program does not halt (is unsatisfiable),
then there exists non-trivial harmonic content (topology) in its graph.
Local consistency ensures that unsatisfiability is due to global
topological obstruction, not mere self-contradiction.
-/
theorem genesis_requires_topology
  (P : Program n) [Decidable (Satisfiable (decode P))]
  (h_cons : LocallyConsistent (decode P)) :
  (Halts P = 0) → ∃ γ, γ ∈ Diaspora.Hodge.HarmonicSubspace (theory_graph (decode P)) ∧ γ ≠ 0 := by
  intro h_loops
  -- If Halts = 0, then Satisfiable is false
  have h_unsat : ¬ Satisfiable (decode P) := by
    by_contra h_sat
    simp [Halts, h_sat] at h_loops
  -- Therefore, topology exists
  exact inconsistency_implies_topology (decode P) h_cons h_unsat

end Diaspora.Logic.Omega
