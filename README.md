```
   o-------o-------o
  / ↻ \    |    / ↺ \
 o-----o-[-γ-]-o-----o
  \   /    |    \   /
   o-------o-------o
```

# Diaspora
**Toy Universe of Graph Topology**

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

### 5\. Topological Genesis (The Origin Story)

Where does the irreducible circulation ($\gamma$) come from?
Diaspora demonstrates that geometry dictates the existence of energy.

  * **The Open State:** On a line graph ($0 \leftrightarrow 1 \leftrightarrow 2$), any pattern of flow can be smoothed out by adjusting node potentials. The system is "Exact."
  * **The Closed State:** Connect $2 \leftrightarrow 0$. Suddenly, the same local flow rules become impossible to satisfy globally.

The moment the topology closes, energy emerges *ex nihilo* from the geometry. We prove that while an open topology can relax to zero energy, a closed topology with the same constraints traps a permanent harmonic form.

### 6\. The Glassy Landscape

In simple graphs, there is often one "best" way to relax. In complex graphs, the definition of "best" fractures.

Diaspora defines a **Glassy System** as one with multiple, non-isomorphic stable vacua. We model this using the "Frustrated Triangle"—a simple structure that forces the system to choose between breaking a "near" edge or a "far" edge.

  * **The False Vacuum:** We prove that a greedy algorithm (always fixing the locally worst error) will often trap the system in a high-energy metastable state.
  * **The Butterfly Effect:** Arbitrarily small changes in initial conditions can cause the system to "freeze" into topologically distinct universes.

### 7. Structural Collapse (The Limit of Connectivity)

What happens when the tension between two nodes becomes unbearable? The connection snaps.

We model this as a topological phase change. When the local strain on an edge exceeds a threshold, the edge is removed from the graph. This is a destructive act, but it is also a creative one:

* **Loss of Local Detail:** The specific strain ($d\phi$) that caused the break is effectively erased.
* **Creation of Global Memory:** The energy that broke the bond doesn't vanish; it becomes a permanent circulation ($\gamma$) around the newly formed void.

This is Diaspora's "Black Hole": a region where the geometry failed, erasing the local history of the failure but preserving its magnitude as a permanent topological mass.

### 8. Self-Measurement (The Geometry of Observation)

If the local history is gone, how can the system "know" the mass is there?

Diaspora models observation using **Parallel Transport**. To measure the system, we move a probe state ($\psi$) along a path.

* **The Zombie:** If the probe travels through a relaxed region, it returns to the start unchanged.
* **The Measurement:** If the probe encircles a topological defect, it picks up the "twist" left behind by the collapse ($e^{i\theta}$).

There is a precise geometric symmetry here: **Structural Collapse** creates the defect by destroying the *direct* path between nodes; **Measurement** detects the defect by traversing the *indirect* path (the loop) that surrounds it. One operation writes the memory into the topology; the other reads it back.

### File Structure

**Foundations**

```
DiscreteCalculus.lean   -- Basic definitions: graphs, cochains, operators
HodgeDecomposition.lean -- The main theorem: existence and uniqueness
HarmonicAnalysis.lean   -- Consequences: energy, quantization, conservation
```

**Phenomenology**

```
TopologicalGenesis.lean -- Origin: How closing a loop creates energy
GlassDynamics.lean      -- Complexity: Definitions of landscapes and isomorphism
FrustratedTriangle.lean -- Example: A system with multiple stable vacua
FalseVacuum.lean        -- Dynamics: Greedy algorithms vs. Global optima
```

**Observer & Evolution**

```
TopologyChange.lean     -- The Black Hole: Strain localization and edge breaking
TopologyDynamics.lean   -- Evolution: Step-by-step graph mutation
SelfMeasurement.lean    -- The Observer: Parallel transport and holonomy
QuantumDynamics.lean    -- Extensions: Berry phase and geometric evolution
```

### Key Theorems

All formally proven in Lean 4:

1.  **Hodge Decomposition**: Every configuration splits into gradient + circulation.
2.  **Harmonic Genesis**: Closing a topology is necessary and sufficient for energy emergence.
3.  **No-Hair Property**: Topological defects preserve energy mass but erase gradient history.
4.  **Greedy Non-Optimality**: Local strain relief can trap the system in a high-energy False Vacuum.
5.  **Aharonov-Bohm Detection**: A system can measure its own topology via internal parallel transport.
6.  **Tailed Triangle Glassiness**: Simple constraints can force non-isomorphic stable outcomes.

## Building and Verifying

```bash
lake build
```

This verifies all proofs. The implementation uses only basic mathematical definitions from Mathlib—no physics libraries, just graph theory elevated through rigorous proof.

## Notes

  - This is a highly llm-collaborated project (reader beware!), serving as a self-learning tool for Lean proofs and neat areas of math. Highly speculative.
  - The framework requires zero additional axioms beyond Lean's foundation.
  - All functions are constructive where possible, noncomputable when necessary.
