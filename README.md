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

**Theorem 3: Merging Can Eliminate Holonomy**
* Start with `X_Frustrated` (triangle with all constraints +10.0, holonomy = +30.0)
* Merge with `X_Opposed` (triangle with all constraints -10.0, holonomy = -30.0)
* All edges average to 0.0
* Result: cycle holonomy K_final = 0.0 (complete cancellation)
* Proven: `negotiation_damps_holonomy` and `consensus_reduces_cost_bound`
* **Key insight:** merge_constraints acts as a frustration-canceling mechanism, not just an aggregator

---

## 🎯 Key Concept 3: Purposeful Frustration

This proves that a system may rationally accept *higher* internal frustration to achieve external goals.

* **The Setup:** A triangle with holonomy K = 30 (all constraints = 10.0)
* **The Conflict:** An external task wants edge (0,1) to equal 5.0, but internal constraints want it to equal 10.0
* **Two Strategies:**
    * **Calm:** Minimize V_int only → V_int = 600, V_ext = 25, ℒ = 625
    * **Purposeful:** Optimize total ℒ → V_int = 612 (higher!), V_ext = 9 (much lower), ℒ = 621 (better!)
* Proven: `purposeful_beats_calm`
* **Key insight:** Purposeful self-contradiction is rationally optimal when internal incoherence serves external purpose

---

## 🔗 Key Concept 4: Localized Frustration Spillover

This proves that in coupled systems, **local stress becomes global frustration** - you cannot quarantine the cost of a local conflict.

* **The Setup:** A "figure-eight" graph with two triangular cycles sharing node 0
    * **Cycle A** (nodes 0, 1, 2): K_A = 30.0
    * **Cycle B** (nodes 0, 3, 4): K_B = 30.0
* **The Conflict:** External task pulls phase[1] to 5.0 (100× penalty weight)
    * This task **only** conflicts with Cycle A (which contains node 1)
    * Cycle B has **nothing to do** with the external task
* **Two States:**
    * **Calm:** Minimize V_int only
        - V_int_A = 600, V_int_B = 600, V_ext = 2500, ℒ = 3700
    * **Purposeful:** Optimize total ℒ
        - V_int_A = 652 (↑ as expected, task conflicts with Cycle A)
        - V_int_B = 612 (↑ contaminated! even though "innocent")
        - V_ext = 0, ℒ = 1264 (much better overall)
* Proven: `frustration_spillover` - Both cycles become more frustrated despite only one being targeted
* **Key insight:** The stress propagates through shared node 0. In coupled systems, **there is no such thing as a local problem** - tight coupling creates frustration transmission channels that make every local stress a global concern.

---

## 🧬 Key Concept 5: Purpose Survival Through Constraint Averaging

This proves that optimized phase structure persists when constraints are averaged with an unoptimized system.

* **The Setup:** Merge X_Purposeful (phases [0,2,1], constraints 10.0) with X_Opposed (phases [0,0,0], constraints 0.0)
* **The Merged World:** Constraint averaging creates new world with constraints = 5.0
* **Two Candidates in the 5.0-constraint world:**
    * **X_NewCalm:** phases [0,0,0] (minimize V_int only) → ℒ = 175
    * **X_Halfway:** phases [0,1,0.5] (adapted from purposeful) → ℒ = 169
* Proven: `purpose_survives_consensus`
* **Key insight:** The adapted configuration [0,1,0.5] outperforms the naive baseline [0,0,0] in the merged constraint world, proving that optimized phase structure survives constraint averaging.

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
* **`Diaspora/PurposefulFrustration.lean`**
    * Proves that accepting higher internal frustration can be globally optimal.
    * Triangle construction with competing internal/external constraints on same edge.
    * Shows V_int can rationally increase when it reduces total Lagrangian.
* **`Diaspora/IteratedNegotiation.lean`**
    * Proves that merge_constraints can completely eliminate holonomy through cancellation.
    * Two opposingly frustrated triangles (+30 and -30 holonomy) merge to zero holonomy.
    * Demonstrates frustration-damping property of consensus mechanisms.
* **`Diaspora/LocalizedFrustration.lean`**
    * Proves frustration spillover in coupled systems (figure-eight graph).
    * External task targeting Cycle A causes Cycle B to also become more frustrated.
    * 24 manual adjacency proofs for spillover analysis across both cycles.
    * Shows impossibility of quarantining local stress in interconnected systems.
* **`Diaspora/PurposeSurvival.lean`**
    * Tests whether optimized phase structure survives constraint averaging.
    * Merges purposeful (constraints 10.0) with opposed (constraints 0.0) systems.
    * Proves adapted configuration outperforms naive baseline in merged 5.0-constraint world.
    * Demonstrates that optimization structure persists through consensus mechanisms.

## ✅ Verification

All proofs are complete with zero axioms and zero sorries:

```bash
lake build                    # Clean build, 1790 jobs
rg "axiom " Diaspora/*.lean   # 0 matches
rg "sorry" Diaspora/*.lean    # 0 matches
```
