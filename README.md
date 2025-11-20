# Diaspora

**A Discrete Hodge Theory Universe**

Diaspora is a formalization of Discrete Exterior Calculus (DEC) on graphs, written in the Lean 4 proof assistant. It constructs a self-contained "toy universe" where physical phenomena—mass, energy spectra, and conservation laws—emerge naturally from the topology of the graph.

This project is **formally verified**. The core framework relies on zero axioms and contains zero `sorrys`.

---

## The Logic of the Universe

Diaspora models a universe defined by connectivity. It begins with a graph and builds a calculus upon it.

### 1. The Entities (Cochains)
The universe consists of **0-cochains** (values on nodes, $\phi$) and **1-cochains** (flows on edges, $\sigma$).
* **Phases ($\phi$):** Scalar potentials defined at each location.
* **Constraints ($\sigma$):** Target flow or "flux" defined along connections.

### 2. The Operators (Discrete Calculus)
Motion is defined by three linear operators:
* **The Gradient ($d^0$):** Converts potentials into flows. $(d\phi)_{ij} = \phi_j - \phi_i$.
* **The Divergence ($d^*$):** Calculates net flow accumulation at a node.
* **The Laplacian ($\Delta$):** The diffusion operator. $\Delta = d^* \circ d$.

### 3. The Engine (Hodge Decomposition)
The central theorem of this universe is the **Hodge Decomposition**. It proves that any constraint configuration $\sigma$ can be uniquely split into two orthogonal components:
$$\sigma = d\phi + \gamma$$
1.  **Exact Component ($d\phi$):** The part that can be satisfied by setting local potentials (gradient flow).
2.  **Harmonic Component ($\gamma$):** The part that is "topologically trapped" on cycles and cannot be relaxed away.

### 4. Emergent Physics
From this decomposition, physical properties emerge without being explicitly programmed:
* **Mass as Topology:** The "internal energy" of a system cannot be zero if there is non-trivial holonomy around a cycle. This irreducible energy ($||\gamma||^2$) acts as mass.
* **Quantized Spectra:** On closed cycles, sustained harmonic flows are forced into discrete, quantized steps ($E \propto m^2/n$).
* **Conservation:** The Fundamental Theorem of Discrete Calculus ensures that gradient flows vanish on closed loops (Stokes' Theorem).

---

## Project Structure

The codebase is architected in layers, moving from definitions to functional analysis to physical interpretation.

### Core Framework
* **`DiscreteCalculus.lean`**
    * Defines the vocabulary: Cochains, Inner Products, Coboundaries, and Chains.
    * Contains the basic algebraic identities.
* **`HodgeDecomposition.lean`**
    * **The Engine.** Contains the rigorous functional analysis proofs.
    * Uses Hilbert space projection theory to prove the existence, uniqueness, and orthogonality of the decomposition $\sigma = d\phi + \gamma$.
* **`HarmonicAnalysis.lean`**
    * **The Physics.** Derives consequences of the decomposition.
    * Proves that energy minimization leads to the harmonic form.
    * Derives topological quantization and spectral properties.

### Extensions
* **`QuantumDynamics.lean`**
    * Extends the universe to $\mathbb{C}$.
    * Defines the Schrödinger evolution $i\partial_t \psi = \hat{H}\psi$.
    * Models geometric phases (Berry Phase) arising from parameter-dependent topology.

---

## Origin Note

Diaspora began as an attempt to model "social frustration" and "negotiation" using graph theory. I found that "frustration" is mathematically identical to the **harmonic component** in Hodge Theory.

Recognizing that the math was trying to be physics, I stripped away the metaphors. What remains is a pure implementation of discrete geometry, where the "cost of frustration" is simply the energy of the system.

---

## Verification

To verify the proofs, clone the repository and build with Lake:

```bash
lake build
