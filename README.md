# Diaspora: A Formal Model of Configuration Spaces and Negotiation

This project, written in the Lean 4 proof assistant, formally models complex systems as **Configuration Spaces**. It explores two primary concepts:

1.  **Gauge Negotiation:** How two different systems ("perspectives") can "negotiate" to find a novel, third system that is better than either of the originals or their simple combination.
2.  **Gauge-Theoretic Holonomy:** How "frustration" or "incompatibility" in a system's constraints (a property called holonomy) creates a fundamental, unavoidable, and provably non-zero cost.

The entire project is **formally verified**, meaning all definitions are mathematically precise, and all theorems are proven with logical certainty.

---

## 🚀 Key Concept 1: Concrete Gauge Negotiation

This part of the project models a "negotiation" between two different configurations, `perspective_A` and `perspective_B`.

* **What is a Configuration?** A configuration (`ConfigSpace`) is a graph where each edge has a "target value" (a **constraint**) and a "current value."
* **What is Cost?** A configuration has three types of costs:
    1.  **Internal Cost (`V_int`):** How far the "current values" are from their "target values" (a sum of squared errors). Lower is better.
    2.  **External Cost (`V_ext`):** How well the configuration solves an "external task." Lower is better.
    3.  **Complexity Cost (`E`):** The number of edges in the graph. Lower is simpler.
* **What is Negotiation?** Negotiation is a process that tries to find a *new* configuration, `X`, that minimizes a total cost function, the **Lagrangian (`ℒ`)**. This function balances the internal cost, external cost, and complexity cost (weighted by a parameter `lam`).

### 🎯 The Main Result: Negotiation Creates Novelty

The project provides a **concrete, 8-node example** to prove that this negotiation process works. It defines:
* `G_A`: A "rigid" configuration with 20 edges.
* `G_B`: An "adaptive" configuration with 37 edges.
* `G_N`: The **negotiated** configuration with 34 edges.
* `G_Union`: The simple combination of A and B, with 43 edges.

Using explicit, hard-coded values, the project *numerically verifies* in Lean that the total cost of the negotiated solution `G_N` is **lower than all the alternatives**:

* `Cost(G_N) < Cost(G_A)`
* `Cost(G_N) < Cost(G_B)`
* `Cost(G_N) < Cost(G_Union)`

This proves by construction that negotiation can produce a **novel solution (`G_N` is not `G_A` or `G_B`)** that is **more efficient (lower cost)** than either starting point or their simple union.

---

## 🌀 Key Concept 2: Gauge-Theoretic Holonomy

This part of the project explores a deeper, "gauge-theoretic" model to understand the fundamental limits of a system.

* **What's the New Model?** Instead of letting each "current edge value" be arbitrary, this model defines them based on "potentials" at each node (called **`node_phases`**). The value of an edge `(i, j)` is simply `phase[j] - phase[i]`.
* **The "Cycle" Property:** A key consequence of this model is that if you sum these edge values around any closed loop (a "cycle"), the "phases" cancel out, and the total sum is **exactly zero**. (This is a "telescoping sum").
* **What is Holonomy?** Holonomy (or "frustration") occurs when the *target constraints* for that same cycle **do not** sum to zero.
    * **System says:** "The sum of values on this path *must* be 0."
    * **Task says:** "The sum of targets for this path *must* be 5.0."
* **The Mismatch:** The system is fundamentally "frustrated." It is *impossible* for the edge values (which must sum to 0) to equal the edge constraints (which sum to 5.0).

### 🎯 The Main Result: Holonomy Creates Unavoidable Cost

The project proves that this frustration creates a permanent, non-zero cost. The core theorem, proven using constrained optimization (Lagrange multipliers), states:

> **The minimum possible internal cost (`V_int`) for a cycle is exactly `K² / n`**

Where:
* `K` is the **holonomy** (the sum of the *constraints* around the cycle, e.g., `5.0`).
* `n` is the number of edges in the cycle.

This theorem (`cycle_creates_holonomy`) formally proves that if a system has *any* cycles with non-zero holonomy (`K ≠ 0`), its internal cost **can never be zero**. It is fundamentally, provably impossible for the system to "perfectly" satisfy its constraints.

---

## 📁 File Breakdown

* **`Diaspora/Concrete.lean`**
    * Defines the basic `ConfigSpace` (a graph with constraints and values).
    * Defines the internal cost (`V_int`), external cost (`V_ext`), and Lagrangian (`ℒ`).
    * Defines a `K` operator (a "local relaxation" step) and proves it reduces the internal cost.
* **`Diaspora/ConcreteGaugeNegotiation.lean`**
    * Defines the `ConcreteNegotiation` structure and the `concrete_negotiation_cost`.
    * Proves the *abstract* theorems that negotiation can create novelty and intermediate complexity, using the 8-node example as evidence.
* **`Diaspora/GaugeNegotiationVerified.lean`**
    * The "data" file. Contains all the hard-coded numbers (graphs, phases, constraints, costs) for the 8-node example.
* **`Diaspora/GaugeNegotiationExplicit.lean`**
    * Performs the explicit arithmetic for the 8-node example.
    * This is where the proofs `L_N_explicit < L_A_explicit`, etc., live, which are verified by Lean's `norm_num` tactic (a numerical calculator).
* **`Diaspora/GaugeNegotiationProofs.lean`**
    * A helper file that bridges the explicit data (like `G_A_edge_count = 20`) to the abstract theorems in `ConcreteGaugeNegotiation.lean`.
* **`Diaspora/GaugeTheoreticHolonomy.lean`**
    * Defines the "gauge-theoretic" `ConfigSpace` where edge values come from `node_phases`.
    * Defines `Cycle` and `cycle_holonomy`.
    * Proves the main theorem: if holonomy `K ≠ 0`, then the internal cost `V_int` must be greater than `0`.
* **`Diaspora/HolonomyLagrangeProof.lean`**
    * The core mathematical engine for the holonomy proof.
    * Proves (using the solution from Lagrange multipliers) that the minimum value for `V_int` on a cycle is exactly `K² / n`.

## ✅ Verification

  All proofs are complete with zero axioms and zero sorries:

  ```bash
  lake build          # Clean build, 3007 jobs
  rg "axiom " Diaspora/*.lean  # 0 matches
  rg "sorry" Diaspora/*.lean   # 0 matches
