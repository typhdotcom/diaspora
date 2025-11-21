    o-------o-------o
   / ↻ \    |    / ↺ \
  o-----o-[-γ-]-o-----o
   \   /    |    \   /
    o-------o-------o

# Diaspora
**Deriving Physical Intuition from Graph Topology**

Diaspora is a formally verified implementation of Discrete Hodge Theory in Lean 4. It demonstrates that a simple discrete graph structure is **mathematically isomorphic** to complex physical phenomena, including conservation laws, energy quantization, and topological defects.

## The Core Insight

Diaspora maps physical problems onto topological structures.

### 1. The Origin of Energy (The Misbuttoned Shirt)

Imagine buttoning a shirt in the dark. You follow a strict local rule: match the current button to the hole directly next to it. Every step feels locally correct. 

However, when you reach the collar, you find a misalignment. This "twist" is not a mistake in any single button; it is a global property of the chain. Diaspora defines **Energy** not as a mysterious fluid, but as this structural tension ($L^2$ norm). It is the cost of trying to force a global map onto conflicting local rules.

### 2. The Conservation of Energy (The Rug Bubble)

Now, imagine that "misalignment" as a bump in a wall-to-wall carpet. You can push the bump down (local adjustment), but it simply pops up somewhere else. You can chase it around the room, but you cannot eliminate the excess material without lifting the carpet at the edges.

In Diaspora, this models the **Hodge Decomposition**. The bump represents the **Harmonic Form ($\gamma$)**. The mathematics proves that this component is orthogonal to local gradients—meaning no amount of local adjustment can destroy the topological error.

## What Is Formalized?

Starting with just a graph (nodes and edges), Diaspora verifies that:
- The $L^2$ norm (Energy) is strictly conserved under projection.
- Discrete geometry necessitates discrete energy levels (Quantization).
- Topological defects imply information horizons (No-Hair Theorem).

## How Diaspora Works

### 1. The Setup
We model the universe using two types of data:
- **Potentials (Nodes, $C^0$)**: The state at a location (e.g., pressure, voltage).
- **Constraints (Edges, $C^1$)**: The rule between locations (e.g., flow rate).

### 2. The Gradient
The gradient operator `d` acts as a **local predictor**.
```

(dφ)(edge i→j) = φ(j) - φ(i)

```
It predicts what the edge constraint *should* be, assuming the nodes are correct.

### 3. The Central Problem: Integration
We rarely see the global state ($\phi$) directly. Instead, we define systems by local constraints ($\sigma$). The central question is: **Do these local rules add up to a consistent reality?**

Can we find a set of node values $\phi$ that perfectly satisfies every local desire $\sigma$? 
**Generally, no.** Conflicting local constraints create impossible global requirements.

### 4. The Hodge Decomposition (Main Theorem)
Every edge configuration $\sigma$ splits uniquely:
```

σ = dφ + γ

```
where:
- `dφ` is achievable through node adjustments
- `γ` is the irreducible circulation

These components are orthogonal: `⟨dφ, γ⟩ = 0`

This proves **Independence**: You can adjust the local gradients ($d\phi$) as much as you like without ever accidentally creating or destroying a global loop ($\gamma$). The local noise and the global structure reside in mathematically distinct subspaces.

### 5. Consequences in Diaspora's Universe
The harmonic component $\gamma$:
- **Persists**: It is invariant under gradient flow.
- **Costs energy**: It contributes precisely `||γ||²` to the total system norm.
- **Quantizes**: Because the domain is discrete, the cohomology class is integer-valued.
- **Defines observables**: Only $\gamma$ is measurable via loop integrals.

## Structures in Diaspora

### Energy and Conservation
We define "Energy" as the squared norm of the system configuration. Diaspora proves that this value is **conserved** not because we added a physics rule, but because the projection operator in a Hilbert space is non-destructive to orthogonal components. The "Law of Conservation" here is a theorem of linear algebra.

### Quantization
Why are energy levels discrete? Because our axiom is a **discrete graph**.
You cannot wind a rubber band around a pole 1.5 times. In a discrete domain, this geometric fact forces the circulation to jump in integer steps. Diaspora highlights how quantum-like behavior is a natural consequence of discrete topology.

### Structural Collapse & The No-Hair Theorem
We model structural failure as a topological change: when local tension exceeds a threshold, an edge is removed. 

The system is left with a permanent topological defect (a non-trivial cohomology class). This defect acts as an information horizon: it preserves the magnitude of the failure ($\int \gamma$) but deletes the specific geometrical details ($d\phi$) of how the edge broke."

## File Structure

```

DiscreteCalculus.lean   -- Basic definitions: graphs, cochains, operators
HodgeDecomposition.lean -- The main theorem: existence and uniqueness
HarmonicAnalysis.lean   -- Consequences: energy, quantization, conservation
QuantumDynamics.lean    -- Complex extension: wave functions, geometric phase
TopologyChange.lean     -- The definitions of edge breaking/failure
TopologyDynamics.lean   -- Evolution: proofs regarding the post-break state

```

## Key Theorems

All formally proven in Lean 4:

1. **Hodge Decomposition**: Every configuration splits into gradient + circulation
2. **Orthogonality**: These components are perpendicular in function space  
3. **Energy Quantization**: Circulation energy = m²/n on n-cycles
4. **No-Hair Property**: Only topology survives measurement through loops
5. **Strain Localization**: High total strain forces some edge to break

## Building and Verifying

```bash
lake build
```

This verifies all proofs. The implementation uses only basic mathematical definitions from Mathlib—no physics libraries, just graph theory elevated through rigorous proof.

## Notes

  - This is a highly llm-collaborated project, serving as a self-learning tool for Lean proofs and neat areas of math.
  - The framework requires zero additional axioms beyond Lean's foundation
  - All functions are constructive where possible, noncomputable when necessary
  - Energy minimization uses Hilbert space projection theory
  - Quantum extensions use complex-valued cochains
