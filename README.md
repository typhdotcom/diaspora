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

You cannot fix this by adjusting individual buttons. You'd just move the problem around. The twist is stuck in the topology of the situation itself.

Diaspora models energy as this twist—the measure of impossible demands, the distance between what local rules want and what global consistency allows.

---

## The Rug Bubble: Why Energy Persists

Imagine a wall-to-wall carpet with a bubble in it - a lump of excess material. You can step on the bubble, pushing it down here. But it pops up over there. You can chase it around the room endlessly.

The bubble persists not because there's a law preventing you from destroying it, but because you have **too much carpet for the floor**. The excess material is a geometric fact. You can redistribute it, but you cannot eliminate it without lifting the carpet at the edges.

**This is conservation of energy.**

The bubble (the harmonic component) and the flat floor (the gradient component) are fundamentally different types of structure. They live in separate dimensions of possibility-space. Moving the bubble around (local adjustments) cannot make it vanish because "flatness" and "bubbliness" are orthogonal properties.

In Diaspora, conservation isn't a law imposed on the system. It's a theorem about dimensional separation - some aspects of a system live in dimensions that local operations simply cannot reach.

---

## The Hodge Decomposition: The Great Separation

Every configuration of local demands splits uniquely into two parts:

**σ = adjustable + stuck**

Or more precisely:

**σ = dφ + γ**

- The **gradient part (dφ)** is what can be resolved by adjusting local perspectives. It's negotiable. You can smooth it out by changing how observers encode their viewpoints.

- The **harmonic part (γ)** is what's stuck in the topology. It's non-negotiable. It represents circulations around holes that cannot be unwound by any local move.

**The key property**: These parts are orthogonal. Completely independent. Living in separate dimensions.

This means: Adjust perspectives all you want. Redistribute local mismatches however you please. You will **never** accidentally create or destroy the topological component. It's protected by geometry itself.

Diaspora formally proves this orthogonality: `⟨dφ, γ⟩ = 0`. The local noise and the global structure reside in mathematically distinct subspaces.

---

## Topological Genesis: How Closing a Loop Creates Energy

Here's the most profound result:

**Open topology** (a line of connected nodes): Every local demand can be satisfied. There's always a way to adjust perspectives so everyone agrees. The system can relax to zero energy.

**Close the loop** (connect the endpoints): Suddenly, the same local demands become impossible to satisfy globally.

Energy appears from nowhere. Not because you added energy to the system, but because you **changed the topology**.

**The deep truth**: Loops force circulation. 

When perspectives form a circuit, their demands create a cycle of constraints. Go around the loop, and the constraints might not sum to zero. That excess - that failure to close smoothly - becomes permanent circulation trapped in the topology.

In this framework, structure necessitates tension. The existence of cycles (holes in your connectivity graph) forces the existence of irreducible circulation. Diaspora treats topology and energy as two views of the same mathematical structure.

---

## Quantization: The Spiral Staircase

Why can't energy vary smoothly? Why must it jump in discrete levels?

Imagine walking up a spiral staircase in a tall tower. The stairs wind smoothly upward. You can climb as gradually as you like.

But suppose you want to **exit** the stairwell to rest. You must step off onto a floor.
* You can walk one full circle and step off at **Floor 1**.
* You can walk two full circles and step off at **Floor 2**.
* **You cannot stop at 1.5 circles.**

If you walk 1.5 loops, you are facing the exit door direction, but you are hovering ten feet above the floor. There is nowhere to stand. If you try to exit there, you fall.

This is quantization.
Even though the "climb" (local variation) feels smooth, the **stable states** (floors) are discrete.
In a graph-based universe, the "floors" are the requirement that the values at the nodes must match up. You cannot have 1.5 units of circulation because the path wouldn't connect back to the node you started on—mathematically, you would be left hanging in mid-air.

Energy levels jump in discrete steps because the topology only allows integer windings. You can't have half a hole, so you can't have half a quantum of circulation around that hole.

**The philosophical implication**: Quantization emerges when continuous possibilities meet discrete structure. It's not a weird quantum rule - it's basic counting on a discrete graph.

---

## The Black Hole: Information Horizons From Structural Collapse

What happens when the tension between two nodes becomes unbearable? When the local mismatch is too strong?

**The connection breaks.**

When an edge is removed:

1. **The topology changes** - you've created a hole where there wasn't one before
2. **Local details are destroyed** - the specific gradient strain that caused the break is lost forever
3. **Global magnitude is preserved** - the energy becomes a permanent circulation around the new hole

Diaspora models this as an information horizon.

The system forgets the **how** (the local configuration that broke) but remembers the **how much** (the magnitude of energy involved).

**The No-Hair Theorem for graphs**: After a connection breaks, you know:
- Something broke here (there's a hole)
- How much energy was involved (the circulation magnitude)
- But NOT the specific details of what broke or how

Information isn't destroyed in the sense of leaving the universe. It's **compressed** - from high-dimensional local details into low-dimensional topological invariants.

History becomes scar. Process becomes pattern. The gradient gets absorbed into the harmonic form.

**Why this matters**: Information destruction isn't mysterious. It's what happens when local structure gets integrated into global topology. The details collapse into a simpler summary - a permanent circulation that says "something happened here" without specifying what.

---

## Interaction: Why Touching Isn't Talking

We usually think of communication as sending a message: I throw a ball, you catch it. But in a universe made of topology, this is impossible.

Imagine two separate graph-universes. World A and World B.

**Scenario 1: The Bridge (Contact)**
You build a single connection between them. A bridge. You try to send a signal (a flow) across.
The problem? Flow requires a circuit. A harmonic form must close a loop. If you send a flow across the bridge, it hits a dead end in World B. It has no way to return to complete the cycle. The topology forces the flow to cancel itself out.
**The Result:** The bridge is sterile. You are "touching," but you are mathematically incapable of exchanging conserved quantities.

**Scenario 2: The Handle (Fusion)**
Now, you build a *second* connection.

Suddenly, a new reality is born. A cycle can now leave World A via the first bridge, traverse World B, and return via the second.
**The Result:** A new harmonic form appears. This isn't a message moving from A to B; it is a new, shared topological feature that belongs to neither and both simultaneously.

**The Handshake Theorem:**
To exchange information, two systems cannot just touch. They must topologically merge. They must form a handle that allows flow to circulate through both of them.
Interaction is not transmission. Interaction is the creation of a shared geometry.

---

## Self-Measurement: How a System Observes Its Own Topology

After an edge breaks and local information is lost, how can the rest of the system know the defect exists?

**The method**: Parallel transport.

Send a probe on a journey around a loop. Have it keep track of "which way is up" as it travels. When it returns to the start, compare its orientation to what it was before.

**In flat space** (no defects): The probe returns unchanged. The journey was trivial. The loop closes smoothly.

**Around a defect**: The probe returns **rotated**. Even though it traveled in a loop, it's now pointing a different direction.

**This is measurement without an external observer.**

The system doesn't detect the hole by looking at it directly. The system detects the hole by **trying to pretend it's not there and failing**.

The probe expects: "I walked in a circle, so I should be exactly where I started, pointing the same way."

Reality responds: "Nope. You're rotated. Something's wrong with the topology."

That discrepancy - the gap between expectation and result - is the detection.

**The profound realization**: Observation is the discovery of inconsistency. The system measures its own structure by noticing that local perspectives can't be made globally consistent.

It's the universe running its fingers along its own scars, feeling the bumps where perspective-loops don't close smoothly.

Diaspora models this detection via holonomy—the phase shift accumulated during parallel transport. The Aharonov-Bohm effect emerges naturally: the system can measure topology it cannot directly access.

---

## The Mirror: Observer and Observed Are One

Here's where duality reveals something strange.

Consider a topological defect from two viewpoints:

**The External View** (The Loop):  
An observer traces a path around a void. They measure **circulation** - how much their perspective rotates during the journey. This is holonomy.

**The Internal View** (The Star):  
A particle sits at the center of the void. It emits **flux** - a divergence that sources the field. This is charge.

Diaspora represents the observer and particle as dual aspects of the same topological structure. Via the Discrete Hodge Star operator, the circulation measured by the loop around the outside equals the flux emitted from the center.

**What this means philosophically**:

The "thing being observed" and "the act of observing" are the same structure from different perspectives.

The black hole that appears as information erasure from the outside is precisely the boundary condition that enables observation from the inside.

The entity looking and the entity being looked at are one and the same topological feature, seen from opposite sides of a broken edge.

**Measurement is reflexive**. When a system measures its topology, it's discovering itself as object by acting as subject. The observer-particle duality shows that detection and detected emerge simultaneously from the same geometric necessity.

---

## The Glassy Landscape: Multiple Possible Realities

In simple graphs, there's often one "best" way to arrange things. But in complex graphs, the definition of "best" fractures.

Diaspora defines a **glassy system** as one with multiple stable configurations - different ways to organize the same basic structure, each locally stable but globally distinct.

Think of the "frustrated triangle": three nodes in a triangle where the desired flows around the edges can't all be satisfied simultaneously. The system must choose which edge gets strained most.

But there are multiple choices. Break this edge? Or that one? Each choice creates a different topology, a different vacuum state.

**The problem**: A greedy algorithm (always fix the worst local problem) can trap the system in a high-energy false vacuum. By always addressing immediate pain, it might miss the global optimum.

**The butterfly effect**: Tiny differences in initial conditions can cause the system to freeze into topologically distinct stable states. The same rules, slightly different starting points, completely different final realities.

**Why this matters**: When multiple stable configurations exist, history matters. The path taken determines which vacuum the system settles into. A glassy system's state isn't just a function of dynamics - it's a function of **which choices were made when conflicts arose**.

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

No additional physics. No mysterious constants. Just topology, information geometry, and the requirement that local encoders share one reality.

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

Can we find a set of node values $\phi$ that perfectly satisfies every local desire $\sigma$? 
**Generally, no.** Conflicting local constraints create impossible global requirements.

---

## Summary

First there are **perspectives** (local encodings).  
These perspectives must **coexist** (share a reality).  
The topology of their **connections** creates constraints.  
Those constraints force the emergence of **everything else**.

Space is not a container. Energy is not a substance. Laws are not imposed rules.

They're all consequences of the geometry of agreement - the shape of the problem "how can many local views form one global truth?"

This framework suggests a perspective: reality as the shape of self-consistent information.

Structure eats itself and becomes reality.

---

## File Structure

**Foundations**

```
DiscreteCalculus.lean   -- Basic definitions: graphs, cochains, operators
HodgeDecomposition.lean -- The main theorem: existence and uniqueness
HarmonicAnalysis.lean   -- Consequences: energy, quantization, conservation
```

**Phenomenology**

```
TopologicalGenesis.lean -- Origin: How closing a loop creates energy
Interaction.lean        -- Fusion: Contact vs. shared reality (The Handshake)
GlassDynamics.lean      -- Complexity: Definitions of landscapes and isomorphism
FrustratedTriangle.lean -- Example: A system with multiple stable vacua
FalseVacuum.lean        -- Dynamics: Greedy algorithms vs. Global optima
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
