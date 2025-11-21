```
   o-------o-------o
  / ↻ \    |    / ↺ \
 o-----o-[-γ-]-o-----o
  \   /    |    \   /
   o-------o-------o
```


# Diaspora
**A Universe Where Geometry Emerges from Graph Structure**

Diaspora is a formally verified implementation of Discrete Hodge Theory in Lean 4. It constructs a self-contained universe where conservation laws, energy quantization, and irreducible structures arise from pure graph topology.

## The Core Insight

Diaspora formalizes two fundamental intuitions about structure and energy.

1. The Origin of Energy

Imagine buttoning a shirt in the dark. You follow a strict local rule: match the current button to the hole directly next to it. Every step feels locally correct. However, when you reach the collar, you find a misalignment—extra fabric or a missing hole. This "twist" is not a mistake in any single button; it is a global property of the chain. In Diaspora, this is Topology: a structural constraint that forces the system into a high-energy state.

2. The Conservation of Energy (The Rug Bubble)

Now, imagine that "misalignment" as a bump in a wall-to-wall carpet. You can push the bump down (local adjustment), but it simply pops up somewhere else. You can chase it around the room, redistribute it, or split it, but you cannot eliminate the excess material without lifting the carpet at the edges.In Diaspora, this is Hodge Decomposition. The bump represents the Harmonic Form ($\gamma$). It is a packet of curvature that is distinct from the flat sections of the rug. It can flow, but it cannot be destroyed.

## What Emerges

Starting with just a graph (nodes and edges), Diaspora derives:
- Energy that cannot be eliminated, only redistributed
- Discrete energy levels forced by topology
- Conservation laws as mathematical necessities
- Structural collapse when constraints exceed capacity

## How Diaspora Works

### 1. The Setup
A graph with two types of functions:
- **Node functions (C⁰)**: Values at vertices
- **Edge functions (C¹)**: Values on connections

### 2. The Gradient
The gradient operator `d` converts node values to edge values:
```
(dφ)(edge i→j) = φ(j) - φ(i)
```
Differences in node values create edge flows.

### 3. The Central Problem
Given desired edge values σ, can we find node values φ such that `dφ = σ`?

Generally, no. The constraints conflict.

### 4. The Hodge Decomposition (Main Theorem)
Every edge configuration σ splits uniquely:
```
σ = dφ + γ
```
where:
- `dφ` is achievable through node adjustments
- `γ` is the irreducible circulation

These components are orthogonal: `⟨dφ, γ⟩ = 0`

### 5. Consequences in Diaspora's Universe

The harmonic component γ:
- **Persists**: Cannot be removed by adjusting nodes
- **Costs energy**: Precisely `||γ||²` 
- **Quantizes**: On n-node cycles, energies are `m²/n` for integer m
- **Defines observables**: Only γ is measurable through loops

## Structures in Diaspora

### Energy and Conservation
The irreducible energy `||γ||²` cannot be destroyed within Diaspora's rules—only redistributed. This emerges from the mathematics, not by design.

### Quantization  
On a cycle in Diaspora, circulation requires energy `E = m²/n` where m is the winding number. Fractional winding is impossible—the discrete structure forces integer levels.

### Structural Collapse
When local strain exceeds capacity (formalized as edge breaking), Diaspora's graph tears. The theorem `black_hole_has_no_hair` proves that after collapse, only the harmonic component remains observable through loops—local details become inaccessible.

## File Structure

```
DiscreteCalculus.lean   -- Basic definitions: graphs, cochains, operators
HodgeDecomposition.lean -- The main theorem: existence and uniqueness
HarmonicAnalysis.lean   -- Consequences: energy, quantization, conservation
QuantumDynamics.lean    -- Complex extension: wave functions, geometric phase
TopologyChange.lean     -- Structural failure: what happens when edges break
TopologyDynamics.lean   -- Evolution: how the graph changes over time
```

## Key Theorems

All formally proven in Lean 4:

1. **Hodge Decomposition**: Every configuration splits into gradient + circulation
2. **Orthogonality**: These components are perpendicular in function space  
3. **Energy Quantization**: Circulation energy = m²/n on n-cycles
4. **No-Hair Property**: Only topology survives measurement through loops
5. **Strain Localization**: High total strain forces some edge to break

## Why "Diaspora"?

The name reflects how local configurations must sometimes "spread out" when they cannot be reconciled at a point. What cannot be satisfied locally becomes circulation through the entire system.

## Building and Verifying

```bash
lake build
```

This verifies all proofs. The implementation uses only basic mathematical definitions from Mathlib—no physics libraries, just graph theory elevated through rigorous proof.

## Notes

- The framework requires zero additional axioms beyond Lean's foundation
- All functions are constructive where possible, noncomputable when necessary
- Energy minimization uses Hilbert space projection theory
- Quantum extensions use complex-valued cochains
