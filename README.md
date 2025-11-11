# Diaspora: A Formal Model of Configuration Spaces and Holonomy

This project, written in the Lean 4 proof assistant, formally models complex systems as **Configuration Spaces** using a gauge-theoretic framework. It explores two primary concepts:

1.  **Gauge-Theoretic Holonomy:** How "frustration" or "incompatibility" in a system's constraints (a property called holonomy) creates a fundamental, unavoidable, and provably non-zero cost.
2.  **Gauge Negotiation:** How merging two different systems ("perspectives") can create or resolve holonomy, with structural consequences proven by construction.

The entire project is **formally verified**, meaning all definitions are mathematically precise, and all theorems are proven with logical certainty.

---

## 🌀 Key Concept 1: Gauge-Theoretic Holonomy

* **What is a Configuration?** A configuration (`ConfigSpace`) is a graph where:
    * Each node has a **phase** (a potential value)
    * Each edge `(i, j)` has a **current value** = `phase[j] - phase[i]`
    * Each edge has a **target constraint**
* **What is Cost?** A configuration has three types of costs:
    1.  **Internal Cost (`V_int`):** Sum of squared differences between current values and constraints. Lower is better.
    2.  **External Cost (`V_ext`):** How well the configuration solves an "external task." Lower is better.
    3.  **Complexity Cost (`E`):** The number of edges in the graph. Lower is simpler.
* **The "Cycle" Property:** If you sum edge values around any closed loop (a "cycle"), the phases cancel out via telescoping, and the total sum is **exactly zero**.
* **What is Holonomy?** Holonomy (or "frustration") occurs when the *target constraints* around a cycle **do not** sum to zero.
    * **System constraint:** "The sum of values on this cycle *must* be 0."
    * **Task constraint:** "The sum of targets for this cycle should be K ≠ 0."
* **The Mismatch:** The system is fundamentally "frustrated." It is *impossible* for the edge values (which must sum to 0) to equal the edge constraints (which sum to K).

### 🎯 The Main Result: Holonomy Creates Unavoidable Cost

The project proves that this frustration creates a permanent, non-zero cost. The core theorem, proven using constrained optimization (Lagrange multipliers), states:

> **The minimum possible internal cost (`V_int`) for a cycle is exactly `K² / n`**

Where:
* `K` is the **holonomy** (the sum of the *constraints* around the cycle, e.g., `5.0`).
* `n` is the number of edges in the cycle.

This theorem (`cycle_creates_holonomy`) formally proves that if a system has *any* cycles with non-zero holonomy (`K ≠ 0`), its internal cost **can never be zero**. It is fundamentally, provably impossible for the system to "perfectly" satisfy its constraints.

---

## 🚀 Key Concept 2: Gauge Negotiation

This part proves structural theorems about what happens when two configurations are merged.

* **What is Merging?** Given two configurations `X_A` and `X_B`:
    * Create union graph: edges from either graph
    * Merge constraints: average when both have an edge, otherwise keep the unique constraint
    * Find optimal node phases for the merged system
* **What is Negotiation?** The process of finding node phases that minimize the **Lagrangian (`ℒ`)**, which balances internal cost, external cost, and complexity cost (weighted by parameter `lam`).

### 🎯 The Main Results: Structural Consequences

The project proves two theorems by explicit construction:

**Theorem 1: Merging Can Create Holonomy**
* Start with `X_A` (path 0→1→2) and `X_B` (path 2→3→0), both holonomy-free
* Union creates 4-cycle: 0→1→2→3→0
* Each edge has constraint 5.0, so cycle holonomy K = 20.0
* Proven: `negotiation_creates_holonomy` and `negotiation_creates_cost`

**Theorem 2: Merging Can Resolve Holonomy**
* Start with `X_C` (frustrated triangle, holonomy = 30.0)
* Merge with `X_D` (single edge with opposite constraint on shared edge)
* Shared edge averages to 0.0, other edges remain 10.0 each
* Result: cycle holonomy reduced from 30.0 to 20.0
* Proven: `negotiation_resolves_holonomy` and `negotiation_reduces_holonomy_value`

---

## 📁 File Breakdown

* **`Diaspora/HolonomyLagrangeProof.lean`**
    * The core mathematical engine for the holonomy proof.
    * Proves (using the solution from Lagrange multipliers) that the minimum value for `V_int` on a cycle is exactly `K² / n`.
* **`Diaspora/GaugeTheoreticHolonomy.lean`**
    * Defines the gauge-theoretic `ConfigSpace` where edge values come from `node_phases`.
    * Defines `Cycle` and `cycle_holonomy`.
    * Defines cost functions (`V_int`, `V_ext`, `E`, `ℒ`).
    * Defines graph union and constraint merging operations.
    * Proves the main theorem: if holonomy `K ≠ 0`, then the internal cost `V_int` must be greater than `0`.
* **`Diaspora/GaugeNegotiation.lean`**
    * Proves Theorem 1: merging two holonomy-free systems can create holonomy (4-node example).
    * Proves Theorem 2: merging a frustrated system with counter-perspective can reduce holonomy (3-node example).
    * All proofs use explicit finite examples with verified arithmetic.

## ✅ Verification

All proofs are complete with zero axioms and zero sorries:

```bash
lake build                    # Clean build, 1786 jobs
rg "axiom " Diaspora/*.lean   # 0 matches
rg "sorry" Diaspora/*.lean    # 0 matches
```
