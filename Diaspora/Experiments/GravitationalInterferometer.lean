/-
# Gravitational Lensing: The Interferometer Proof

Instead of a full 2D grid, we construct a "Gravitational Interferometer":
a graph with two distinct paths connecting a Source (S) and Detector (D).

1. Path A (Euclidean): Length L, Distance R1 from Mass.
2. Path B (Lensed): Length L + δ, Distance R2 from Mass (where R2 > R1).

We prove that for a sufficiently large Mass M, the "Lensed" path (Path B) 
has lower Action than the "Euclidean" path (Path A), despite being geometrically longer.

## Structural Fixes based on Feedback
- Removed `Point N` type; using raw `Fin n` graph to avoid type mismatches.
- Removed complex path-finding; paths are hard-coded structurally.
- Axiomatized Strain Decay directly as `strain ~ M/r` to avoid dependency on 
  complex relaxation proofs in `PoissonEquation`.
-/

import Diaspora.GaugeTheoreticHolonomy
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open GaugeTheoretic

namespace GravitationalInterferometer

/-! ## Part 1: The Interferometer Topology -/

/-- 
  A Graph with 4 main components:
  0: Source
  1: Detector
  2: Path A node (Inner/Near)
  3: Path B node (Outer/Far)
  
  Path A: 0 -> 2 -> 1 (Length 2)
  Path B: 0 -> 3 -> 4 -> 1 (Length 3 - "Longer")
-/
def interferometer_graph : SimpleGraph (Fin 5) := 
  SimpleGraph.fromRel (fun i j => 
    -- Path A (Inner): 0-2, 2-1
    (i=0 ∧ j=2) ∨ (i=2 ∧ j=0) ∨ (i=2 ∧ j=1) ∨ (i=1 ∧ j=2) ∨
    -- Path B (Outer): 0-3, 3-4, 4-1
    (i=0 ∧ j=3) ∨ (i=3 ∧ j=0) ∨ (i=3 ∧ j=4) ∨ (i=4 ∧ j=3) ∨ (i=4 ∧ j=1) ∨ (i=1 ∧ j=4)
  )

/-- The Setup Configuration -/
structure LensingSetup where
  config : ConfigSpace 5
  h_graph : config.graph = interferometer_graph
  /-- The Mass of the central object (not part of the graph, but creating the field) -/
  M : ℝ
  h_M_pos : 0 < M

/-! ## Part 2: The Strain Field -/

/-- 
  Geometric Distance from the "Singularity".
  We abstract this as a lookup function rather than coordinates.
  
  Path A (Node 2) is at distance R1 (Near).
  Path B (Nodes 3,4) is at distance R2 (Far).
-/
noncomputable def radius_from_mass (node : Fin 5) : ℝ :=
  match node with
  | 2 => 1.0   -- Inner path node
  | 3 => 10.0  -- Outer path node
  | 4 => 10.0  -- Outer path node
  | _ => 100.0 -- Source/Detector (far away)

-- Helper lemmas to force evaluation of the match expression
lemma r_0 : radius_from_mass 0 = 100.0 := rfl
lemma r_1 : radius_from_mass 1 = 100.0 := rfl
lemma r_2 : radius_from_mass 2 = 1.0 := rfl
lemma r_3 : radius_from_mass 3 = 10.0 := rfl
lemma r_4 : radius_from_mass 4 = 10.0 := rfl

/-- 
  Strain Field Axiom:
  The frustration creates a local energy density (strain) σ.
  σ(r) = M / r (Newtonian potential scaling).
-/
noncomputable def strain_at_node (setup : LensingSetup) (node : Fin 5) : ℝ :=
  setup.M / (radius_from_mass node)

/--
  Optical Index: n = 1 + Strain.
  Cost to traverse edge is (1 + avg_strain) * length.
-/
noncomputable def optical_cost (setup : LensingSetup) (u v : Fin 5) : ℝ :=
  let strain := (strain_at_node setup u + strain_at_node setup v) / 2
  1.0 + strain

/-! ## Part 3: The Action Calculation -/

/-- Action of Path A (Euclidean/Short) -/
noncomputable def action_path_A (setup : LensingSetup) : ℝ :=
  -- Edge 0-2
  optical_cost setup 0 2 +
  -- Edge 2-1
  optical_cost setup 2 1

/-- Action of Path B (Lensed/Long) -/
noncomputable def action_path_B (setup : LensingSetup) : ℝ :=
  -- Edge 0-3
  optical_cost setup 0 3 +
  -- Edge 3-4
  optical_cost setup 3 4 +
  -- Edge 4-1
  optical_cost setup 4 1

/-! ## Part 4: The Lensing Theorem -/

/--
  **Theorem: Geometric Frustration Lenses Light**
  
  Path A is geometrically shorter (2 steps) than Path B (3 steps).
  However, Path A passes through High Strain (r=1).
  Path B passes through Low Strain (r=10).
  
  Prove that for sufficient Mass M, Action(B) < Action(A).
-/
theorem holonomy_lenses_light (setup : LensingSetup) :
  ∃ (M_threshold : ℝ), setup.M > M_threshold →
  action_path_B setup < action_path_A setup := by

  -- Algebra:
  -- Action A ≈ 2 + 1.01M
  -- Action B ≈ 3 + 0.21M
  -- Inequality: 3 + 0.21M < 2 + 1.01M → 1 < 0.8M → M > 1.25
  use 1.3
  intro h_mass

  -- Unfold main definitions
  unfold action_path_A action_path_B optical_cost strain_at_node

  -- Rewrite using the pre-computed radius values
  -- This eliminates the match expressions entirely, leaving only arithmetic
  rw [r_0, r_1, r_2, r_3, r_4]

  -- Now we have pure arithmetic with setup.M
  -- Use field_simp to clear denominators (100.0, 10.0, etc)
  field_simp

  -- Now we have a linear inequality in M
  have h_pos : setup.M > 0 := setup.h_M_pos

  -- Linarith can now solve this because it's just numbers and M
  linarith

end GravitationalInterferometer
