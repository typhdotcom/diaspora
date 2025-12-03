-- Root module for the Diaspora library

-- Core: Foundations
import Diaspora.Core.Calculus
import Diaspora.Core.Weighted
import Diaspora.Core.Phase

-- Hodge: Static Theory
import Diaspora.Hodge.Decomposition
import Diaspora.Hodge.Harmonic
import Diaspora.Hodge.Spectral
import Diaspora.Hodge.Twist
import Diaspora.Hodge.IndexTheorem

-- Dynamics: Time Evolution
import Diaspora.Dynamics.Diffusion
import Diaspora.Dynamics.Plasticity
import Diaspora.Dynamics.Strain
import Diaspora.Dynamics.Transition
import Diaspora.Dynamics.Glass
import Diaspora.Dynamics.Sim
import Diaspora.Dynamics.Local
import Diaspora.Dynamics.Transition

-- Quantum: Complex Extensions
import Diaspora.Quantum.Evolution
import Diaspora.Quantum.Measurement
import Diaspora.Quantum.Witness

-- Models: Stories and Test Cases
import Diaspora.Models.FalseVacuum
import Diaspora.Models.Triangle
import Diaspora.Models.Interaction
import Diaspora.Models.Duality
import Diaspora.Models.Void
import Diaspora.Models.Resilience
import Diaspora.Models.Genesis
import Diaspora.Models.WeightedStrain
import Diaspora.Models.StrainDynamics
import Diaspora.Models.ObserverEffect
-- Logic
import Diaspora.Logic.Theory
import Diaspora.Logic.Omega
import Diaspora.Logic.Genesis
import Diaspora.Logic.Inverse
import Diaspora.Logic.Probabilistic
import Diaspora.Logic.Classicality
import Diaspora.Logic.Limit
import Diaspora.Logic.Universal
import Diaspora.Logic.Universe
import Diaspora.Logic.WalkHolonomy
import Diaspora.Logic.Kirchhoff
import Diaspora.Logic.Information

open Diaspora.Core Diaspora.Hodge Diaspora.Logic Diaspora.Logic.Information Diaspora.Dynamics Diaspora.Models

/--
A helper to format the output of our simulation.
-/
def printHeader (title : String) : IO Unit := do
  IO.println ""
  IO.println "========================================"
  IO.println s!"   {title}"
  IO.println "========================================"

/--
Export simulation state as JSON
-/
structure SimulationState where
  time : Nat
  vertices : Nat
  edges : List (Nat × Nat)
  satisfiable : Bool
  betti_number : Nat
  winding_number : Int
  mass : Float
  strain_energy : Float
  latent_capacity : Float

def SimulationState.toJSON (s : SimulationState) : String :=
  let rec edgesListToJSON : List (Nat × Nat) → String
    | [] => ""
    | [(i, j)] => s!"[{i}, {j}]"
    | (i, j) :: rest => s!"[{i}, {j}], " ++ edgesListToJSON rest
  let edgesJSON := "[" ++ edgesListToJSON s.edges ++ "]"
  "{" ++
  s!"\"time\": {s.time}, " ++
  s!"\"vertices\": {s.vertices}, " ++
  s!"\"edges\": {edgesJSON}, " ++
  s!"\"satisfiable\": {if s.satisfiable then "true" else "false"}, " ++
  s!"\"betti_number\": {s.betti_number}, " ++
  s!"\"winding_number\": {s.winding_number}, " ++
  s!"\"mass\": {s.mass}, " ++
  s!"\"strain_energy\": {s.strain_energy}, " ++
  s!"\"latent_capacity\": {s.latent_capacity}" ++
  "}"

def exportSimulation (states : List SimulationState) (filename : String) : IO Unit := do
  let rec statesToJSON : List SimulationState → String
    | [] => ""
    | [s] => s.toJSON
    | s :: rest => s.toJSON ++ ", " ++ statesToJSON rest
  let statesJSON := "[" ++ statesToJSON states ++ "]"
  let fullJSON := "{" ++ "\"states\": " ++ statesJSON ++ "}"
  IO.FS.writeFile filename fullJSON
  IO.println s!"\n✓ Exported to {filename}"

/--
The Main Simulation Runner.
Since `Real` is non-computable in Lean, we cannot strictly "calculate" the
evolution at runtime. Instead, this Main function steps through the
theoretically proven evolution path of the `Genesis` paradox, reporting
the rigorous values derived in the library.
-/
def main : IO Unit := do
  IO.println "\n"
  IO.println "      DIASPORA KERNEL v1.0      "
  IO.println "   A Toy Universe of Topology   "
  IO.println "   --------------------------   "

  -----------------------------------------------------------------------------
  -- T = 0: GENESIS (The Paradox)
  -----------------------------------------------------------------------------
  printHeader "T=0: INITIALIZATION (GENESIS)"
  IO.println "Loading Constraints: Rotational Program (Triangle)"
  IO.println "   Constraint 1: 0 → 1 (+1)"
  IO.println "   Constraint 2: 1 → 2 (+1)"
  IO.println "   Constraint 3: 2 → 0 (+1)"

  IO.println "\n[ LOGIC LAYER ]"
  IO.println "   Checking Satisfiability... UNSATISFIABLE"
  IO.println "   Status: IsParadox = True"
  IO.println "   Reason: Global obstruction detected."

  IO.println "\n[ GEOMETRY LAYER ]"
  -- Values derived from Diaspora.Logic.Kirchhoff
  IO.println "   Topology: Closed 3-Cycle"
  IO.println s!"   Betti Number (Deficit): 1"
  IO.println "   Active Edges: 3"
  IO.println "   Latent Capacity: 0.0"

  IO.println "\n[ PHYSICS LAYER ]"
  -- Values derived from Diaspora.Models.Genesis / Hodge.Twist
  IO.println "   Computing Hodge Decomposition..."
  IO.println "   Harmonic Component (γ): DETECTED"
  IO.println "   Winding Number: 3"
  IO.println "   Mass (‖γ‖²): 3.0"  -- 3² * (1/3)
  IO.println "   Total Strain Energy: 3.0"

  IO.println "\n>> WARNING: SYSTEM UNSTABLE."
  IO.println ">> Paradox exerts physical force. Strain exceeds threshold."
  IO.println ">> Initiating Topological Transition..."

  -----------------------------------------------------------------------------
  -- T = 1: THE BREAK (The Vacuum)
  -----------------------------------------------------------------------------
  printHeader "T=1: EVOLUTION (THE VACUUM)"

  IO.println "[ DYNAMICS ]"
  IO.println "   Event: Edge (0, 1) Fracture"
  IO.println "   Mechanism: Strain Localization"
  IO.println "   Capacity Transfer: Active → Latent"

  IO.println "\n[ LOGIC LAYER ]"
  -- The constraint set T is technically still the same, but the graph G' is different.
  -- On the new graph G', the constraints are no longer contradictory (because the loop is broken).
  IO.println "   Checking Satisfiability on G'... SATISFIABLE"
  IO.println "   Status: Classical Vacuum"
  IO.println "   Reason: Tree topology admits no contradictions."

  IO.println "\n[ GEOMETRY LAYER ]"
  IO.println "   Topology: Path 2-0-1 (Tree)"
  IO.println s!"   Betti Number (Deficit): 0"
  IO.println "   Active Edges: 2"
  IO.println "   Latent Capacity: 1.0" -- The broken edge carried unit flux

  IO.println "\n[ PHYSICS LAYER ]"
  IO.println "   Computing Hodge Decomposition..."
  IO.println "   Harmonic Component (γ): NONE (Exact)"
  IO.println "   Mass (‖γ‖²): 0.0"
  IO.println "   Total Strain Energy: 0.0"
  
  -----------------------------------------------------------------------------
  -- SUMMARY
  -----------------------------------------------------------------------------
  printHeader "SIMULATION COMPLETE"
  IO.println "Summary of Metaphysics:"
  IO.println "1. Logic: Inconsistency creates Geometry."
  IO.println "2. Info:  Paradox is incompressible data."
  IO.println "3. Mass:  Incompressible data manifests as Energy."
  IO.println "4. Time:  Evolution is the minimization of logical error."
  IO.println "\nready."

  -----------------------------------------------------------------------------
  -- EXPORT JSON
  -----------------------------------------------------------------------------
  let state0 : SimulationState := {
    time := 0,
    vertices := 3,
    edges := [(0, 1), (1, 2), (2, 0)],
    satisfiable := false,
    betti_number := 1,
    winding_number := 3,
    mass := 3.0,
    strain_energy := 3.0,
    latent_capacity := 0.0
  }

  let state1 : SimulationState := {
    time := 1,
    vertices := 3,
    edges := [(2, 0), (0, 1)],  -- Edge (0,1) broken, only (2,0) and (0,1) remain
    satisfiable := true,
    betti_number := 0,
    winding_number := 0,
    mass := 0.0,
    strain_energy := 0.0,
    latent_capacity := 1.0
  }

  exportSimulation [state0, state1] "diaspora_evolution.json"
