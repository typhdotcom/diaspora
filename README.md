<p align="center">
  <img src="img/logo.png" alt="Diaspora" height="100" />
</p>

# Diaspora
**A Universe of Graph Topology**

Diaspora is a formally verified exploration of Discrete Hodge Theory in Lean 4. It demonstrates how complex phenomena—conservation laws, energy quantization, topological defects, observation—emerge from a simple requirement: local perspectives on a discrete graph must form one consistent global reality.

---

## The Fundamental Problem: Perspectives That Must Agree

Imagine a network of observers. Each observer can only see their immediate surroundings - the connections touching them. Each one forms an opinion about how things should flow through their local connections.

You think three units should flow out.  
Your neighbor thinks five units should flow in.  
The wire between you hears both demands.

**The central question**: Can reality satisfy everyone simultaneously?

Usually, no. Local perspectives conflict. This mismatch - this impossibility of making everyone happy at once - is where everything interesting begins.

---

## The Misbuttoned Shirt: Where Energy Comes From

Imagine buttoning a shirt in the dark. You follow a simple rule: match each button to the hole right next to it. Every single pairing feels locally correct. Each button clicks into place satisfyingly.

But when you reach the collar, you discover you're off by one. There's a twist in the system.

**The crucial insight**: No individual button violates the local rule. Each one correctly followed the instructions. The error is **global** - it's a property of the whole chain, not any particular link.

You cannot fix this by adjusting individual buttons. You'd just move the problem around. The twist is stuck in the topology of the situation itself. Like a wrinkle in a fitted bedsheet that's slightly too large—you can smooth it down here, but it pops up over there. The excess is geometric fact.

Diaspora models energy as this twist—the measure of impossible demands, the distance between what local rules want and what global consistency allows. The twist (harmonic) and the flat configuration (gradient) live in separate dimensions of possibility-space. Conservation isn't a law imposed on the system—it's a theorem about dimensional separation.

---

## The Hodge Decomposition: The Great Separation

Every configuration of local demands splits uniquely into two parts:

**σ = dφ + γ**

- The **gradient part (dφ)** is what can be resolved by adjusting local perspectives. It's negotiable.
- The **harmonic part (γ)** is what's stuck in the topology. It's non-negotiable.

**The key property**: These parts are orthogonal. Completely independent. Living in separate dimensions.

Adjust perspectives all you want. You will **never** accidentally create or destroy the topological component. It's protected by geometry itself.

Diaspora formally proves this orthogonality: `⟨dφ, γ⟩ = 0`.

---

## Topological Genesis: How Closing a Loop Creates Energy

**Open topology** (a line of connected nodes): Every local demand can be satisfied. The system can relax to zero energy.

**Close the loop** (connect the endpoints): Suddenly, the same local demands become impossible to satisfy globally.

Energy appears from nowhere. Not because you added energy to the system, but because you **changed the topology**.

When perspectives form a circuit, their demands create a cycle of constraints. Go around the loop, and the constraints might not sum to zero. That excess becomes permanent circulation trapped in the topology.

---

## Quantization: The Spiral Staircase

Imagine a spiral staircase in a tall tower. To exit onto a floor, you must complete full loops. One circle → Floor 1. Two circles → Floor 2. **You cannot stop at 1.5 circles.** There's nowhere to stand.

Even though the climb feels smooth, the **stable states** are discrete. In a graph, you can't have 1.5 units of circulation because the path wouldn't connect back—you'd be left hanging in mid-air.

Energy levels jump in discrete steps because topology only allows integer windings.

---

## The Black Hole: Information Horizons From Structural Collapse

When an edge breaks:

1. **The topology changes** - you've created a hole
2. **Local details are destroyed** - the specific strain that caused the break is lost
3. **Global magnitude is preserved** - the energy becomes a permanent circulation

After a connection breaks, you know something broke here and how much energy was involved, but NOT the specific details of what broke or how.

Information is **compressed** - from high-dimensional local details into low-dimensional topological invariants.

---

## Interaction: Why Touching Isn't Talking

**One Bridge (Contact):** Flow requires a circuit. A single bridge provides no return path. The topology forces the flow to cancel itself out. The bridge is sterile.

**Two Bridges (Fusion):** A cycle can now leave World A, traverse World B, and return. A new harmonic form appears—a shared topological feature belonging to both.

**The Handshake Theorem:** To exchange information, two systems must topologically merge. Interaction is the creation of shared geometry.

---

## Self-Measurement: How a System Observes Its Own Topology

Send a probe around a loop tracking "which way is up." In flat space, it returns unchanged. Around a defect, it returns **rotated**.

The system detects the hole by **trying to pretend it's not there and failing**. Observation is the discovery of inconsistency—the system measures itself by noticing that local perspectives can't be made globally consistent.

---

## Metric Deception: Why Local Sensors Lie

In a complex graph, what looks like the "weakest link" depends on how fast you look.

To prove this, Diaspora constructs a specific topology: the **Theta Graph ($\Theta$)**.
* **The Trap (Middle Bar):** A structural bridge carrying a heavy load. Locally, it has the highest strain. It *looks* like the obvious point of failure.
* **The Smart Edge (Outer Loop):** A redundant path carrying a lighter load. Locally, it appears safe.

Diaspora proves that the stability of this structure depends entirely on the observer's timescale:

1.  **Quenched Limit (Fast):** Without relaxation, strain is determined purely by local flux constraints ($F$). Since $F_{trap} > F_{smart}$, the system blindly snaps the Trap.
2.  **Annealed Limit (Slow):** With relaxation, potentials ($\phi$) shift to distribute the load. We prove there exists a relaxation magnitude that **inverts** the strain profile. The Trap holds, and the "safe" Smart Edge breaks instead.

This proves that **stability is relative to the observer's timescale**. A system acting quickly perceives a different physical reality than one acting slowly. The "False Vacuum" is simply the result of acting on local metrics before global information has propagated.

***

## Summary

First there are **perspectives** (local encodings). These perspectives must **coexist** (share a reality). The topology of their **connections** creates constraints. Those constraints force the emergence of **everything else**.

---

## How Diaspora Works

### The Setup
We model the universe using two types of data:
- **Potentials (Nodes, $C^0$)**: The state at a location (e.g., pressure, voltage)
- **Constraints (Edges, $C^1$)**: The rule between locations (e.g., flow rate)

### The Gradient
The gradient operator `d` acts as a **local predictor**.
```
(dφ)(edge i→j) = φ(j) - φ(i)
```
It predicts what the edge constraint *should* be, assuming the nodes are correct.

### The Central Problem: Integration
We rarely see the global state ($\phi$) directly. Instead, we define systems by local constraints ($\sigma$). The central question is: **Do these local rules add up to a consistent reality?**

Can we find node values $\phi$ that perfectly satisfy every local desire $\sigma$? **Generally, no.** Conflicting local constraints create impossible global requirements.

---

## What Is Represented

Starting with just a graph (nodes and edges), Diaspora verifies that:
- The $L^2$ norm (energy) is strictly conserved under projection
- Discrete geometry necessitates discrete energy levels (quantization)
- Topological defects imply information horizons (no-hair theorem)
- Closed topologies are necessary and sufficient for energy emergence (harmonic genesis)
- Local strain relief can trap systems in high-energy false vacua (greedy non-optimality)
- Systems can measure their own topology via internal parallel transport (Aharonov-Bohm detection)
- The holonomy of the observer is identical to the divergence of the singularity (observer-particle duality)

Everything emerges from one axiom: **a discrete graph where local perspectives must coexist**.

From just this:

- **Energy** emerges as the measure of conflicting local demands
- **Conservation** follows from dimensional orthogonality  
- **Quantization** arises from discrete topology
- **Information horizons** appear when structure collapses into topology
- **Observation** is self-measurement through parallel transport
- **Observer-particle duality** shows measurement as reflexive structure

No additional physics or constants. Just topology, information geometry, and the requirement that local encoders share one reality.

---

## File Structure

**Foundations**
```
DiscreteCalculus.lean   -- Basic definitions: graphs, cochains, operators
HodgeDecomposition.lean -- The main theorem: existence and uniqueness
HarmonicAnalysis.lean   -- Consequences: energy, quantization, conservation
```

**Phenomenology & Dynamics**

```
TopologicalGenesis.lean -- Origin: How closing a loop creates energy
Interaction.lean        -- Fusion: Contact vs. shared reality (The Handshake)
GlassDynamics.lean      -- Complexity: Definitions of landscapes and isomorphism
FrustratedTriangle.lean -- Example: A system with multiple stable vacua
FalseVacuum.lean        -- Metric Deception: Formal proof that relaxation inverts topological stability
```

**Observer & Evolution**

```
TopologyChange.lean     -- The Black Hole: Strain localization and edge breaking
TopologyDynamics.lean   -- Evolution: Step-by-step graph mutation
SelfMeasurement.lean    -- The Observer: Parallel transport and holonomy
Duality.lean            -- The Mirror: Formal proof of Observer-Particle identity
QuantumDynamics.lean    -- Extensions: Berry phase and geometric evolution
```

---

## Building and Verifying

```bash
lake build
```

This verifies all proofs. The implementation uses only basic mathematical definitions from Mathlib—no physics libraries, just graph theory elevated through rigorous proof.

---

## Notes

- This is a highly LLM-collaborated project (reader beware!), serving as a self-learning tool for Lean proofs and exploring these mathematical structures. Highly speculative.
- The framework requires zero additional axioms beyond Lean's foundation.
- All functions are constructive where possible, noncomputable when necessary.
