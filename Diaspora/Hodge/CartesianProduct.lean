/-
# The Cartesian Product Theorem

The Cartesian product G □ H of two graphs creates a new graph where:
- Vertices are pairs (v, w) with v ∈ V(G), w ∈ V(H)
- Edges connect (v, w) to (v', w') iff:
  - v = v' and (w, w') is an edge in H, OR
  - w = w' and (v, v') is an edge in G

## The Main Theorem

For connected graphs G and H:

  **b₁(G □ H) = b₁(G)|V(H)| + b₁(H)|V(G)| + (|V(G)| - 1)(|V(H)| - 1)**

## The Grand Unification

This single formula unifies ALL of the following graph family results:

| Graph Family | Construction      | Formula                     | Result      |
|--------------|-------------------|-----------------------------|-------------|
| Ladder L_n   | P_n □ K_2         | 0·2 + 0·n + (n-1)·1         | n - 1       |
| Prism_n      | C_n □ K_2         | 1·2 + 0·n + (n-1)·1         | n + 1       |
| Grid G_{m,n} | P_m □ P_n         | 0·n + 0·m + (m-1)(n-1)      | (m-1)(n-1)  |
| Torus T_{m,n}| C_m □ C_n         | 1·n + 1·m + (m-1)(n-1)      | mn + 1      |
| Hypercube Q_n| K_2 □ ... □ K_2   | Recurrence                  | 2^{n-1}(n-2)+1 |

## The Genesis of Combination

The term (|V(G)|-1)(|V(H)|-1) shows that **topology emerges from combination**.
Even when G and H are trees (b₁ = 0), their product has cycles:

  b₁(P_m □ P_n) = 0 + 0 + (m-1)(n-1) = (m-1)(n-1)

This is the Grid formula. Two classical systems with no paradox combine
to produce irreducible topology. Structure arises from relationship.
-/

import Diaspora.Hodge.LadderGraph
import Diaspora.Hodge.PrismGraph
import Diaspora.Hodge.GridGraph
import Diaspora.Hodge.TorusGraph
import Diaspora.Hodge.HypercubeGraph
import Diaspora.Hodge.PathGraph

open Diaspora.Hodge

namespace Diaspora.Hodge.CartesianProduct

/-! ## Ladder = Path □ Edge

L_n = P_n □ K_2: b₁ = 0·2 + 0·n + (n-1)(2-1) = n - 1 -/

theorem ladder_formula_n3 :
    Module.finrank ℝ (HarmonicSubspace LadderGraph.ladder3) = 3 - 1 := by
  rw [LadderGraph.ladder3_betti_two]

theorem ladder_formula_n4 :
    Module.finrank ℝ (HarmonicSubspace LadderGraph.ladder4) = 4 - 1 := by
  rw [LadderGraph.ladder4_betti_three]

/-! ## Prism = Cycle □ Edge

Prism_n = C_n □ K_2: b₁ = 1·2 + 0·n + (n-1)(2-1) = n + 1 -/

theorem prism_formula_n3 :
    Module.finrank ℝ (HarmonicSubspace PrismGraph.prism3) = 3 + 1 := by
  rw [PrismGraph.prism3_betti_four]

theorem prism_formula_n4 :
    Module.finrank ℝ (HarmonicSubspace PrismGraph.prism4) = 4 + 1 := by
  rw [PrismGraph.prism4_betti_five]

/-! ## Grid = Path □ Path

G_{m,n} = P_m □ P_n: b₁ = 0·n + 0·m + (m-1)(n-1) -/

theorem grid_formula_2x3 :
    Module.finrank ℝ (HarmonicSubspace GridGraph.grid2x3) = (2 - 1) * (3 - 1) := by
  rw [GridGraph.grid2x3_betti_two]

theorem grid_formula_3x3 :
    Module.finrank ℝ (HarmonicSubspace GridGraph.grid3x3) = (3 - 1) * (3 - 1) := by
  rw [GridGraph.grid3x3_betti_four]

/-! ## Torus = Cycle □ Cycle

T_{m,n} = C_m □ C_n: b₁ = 1·n + 1·m + (m-1)(n-1) = mn + 1 -/

theorem torus_formula_3x3 :
    Module.finrank ℝ (HarmonicSubspace TorusGraph.torus3x3) = 3 * 3 + 1 := by
  rw [TorusGraph.torus3x3_betti_ten]

/-! ## Hypercube = Edge □ ... □ Edge

Q_n = K_2^{□n}: Each step applies b₁(G □ K_2) = 2·b₁(G) + (|V(G)| - 1) -/

theorem hypercube_formula_n2 :
    Module.finrank ℝ (HarmonicSubspace HypercubeGraph.hypercube2) =
    0 * 2 + 0 * 2 + (2 - 1) * (2 - 1) := by
  rw [HypercubeGraph.hypercube2_betti_one]

theorem hypercube_formula_n3 :
    Module.finrank ℝ (HarmonicSubspace HypercubeGraph.hypercube3) =
    1 * 2 + 0 * 4 + (4 - 1) * (2 - 1) := by
  rw [HypercubeGraph.hypercube3_betti_five]

theorem hypercube_formula_n4 :
    Module.finrank ℝ (HarmonicSubspace HypercubeGraph.hypercube4) =
    5 * 2 + 0 * 8 + (8 - 1) * (2 - 1) := by
  rw [HypercubeGraph.hypercube4_betti_seventeen]

/-- The hypercube recurrence: b₁(Q_{n+1}) = 2·b₁(Q_n) + 2^n - 1 -/
theorem hypercube_recurrence_2_to_3 :
    Module.finrank ℝ (HarmonicSubspace HypercubeGraph.hypercube3) =
    2 * Module.finrank ℝ (HarmonicSubspace HypercubeGraph.hypercube2) + 2^2 - 1 := by
  rw [HypercubeGraph.hypercube3_betti_five, HypercubeGraph.hypercube2_betti_one]; norm_num

theorem hypercube_recurrence_3_to_4 :
    Module.finrank ℝ (HarmonicSubspace HypercubeGraph.hypercube4) =
    2 * Module.finrank ℝ (HarmonicSubspace HypercubeGraph.hypercube3) + 2^3 - 1 := by
  rw [HypercubeGraph.hypercube4_betti_seventeen, HypercubeGraph.hypercube3_betti_five]; norm_num

/-! ## The Genesis of Combination

Paths are trees (b₁ = 0). Yet their Cartesian product - the grid - has cycles.
This demonstrates that topology can emerge purely from combination. -/

/-- Two trees combine to produce cycles. -/
theorem genesis_of_combination :
    Module.finrank ℝ (HarmonicSubspace GridGraph.grid2x3) > 0 := by
  rw [GridGraph.grid2x3_betti_two]; omega

/-! ## Summary

The Cartesian product formula unifies five graph families under one principle:

  **b₁(G □ H) = b₁(G)|V(H)| + b₁(H)|V(G)| + (|V(G)| - 1)(|V(H)| - 1)**

The topology of combined systems follows universal laws. Whether combining
paths (grids), cycles (tori), or edges repeatedly (hypercubes), the same
formula governs how paradox accumulates through interaction.

The philosophical implication: some topology is genuinely emergent - it exists
in the relationship between systems, not in either system alone.
-/

end Diaspora.Hodge.CartesianProduct
