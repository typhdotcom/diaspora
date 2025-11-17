# Diaspora: A Formal Model of Configuration Spaces and Holonomy

This project, written in the Lean 4 proof assistant, formally models complex systems as **Configuration Spaces** using a gauge-theoretic framework. It explores several interconnected concepts:

1.  **Gauge-Theoretic Holonomy:** How "frustration" or "incompatibility" in a system's constraints (a property called holonomy) creates a fundamental, unavoidable, and provably non-zero cost.
2.  **Gauge Negotiation:** How merging two different systems ("perspectives") can create or resolve holonomy, with structural consequences proven by construction.
3.  **Purposeful Frustration:** How systems rationally accept higher internal frustration to achieve external goals.
4.  **Frustration Spillover:** How local stress propagates globally through coupled systems.
5.  **Conservation Laws:** How holonomy behaves under path merging and constraint averaging.
6.  **Historical Optimization:** How optimized structure from one system survives and provides value when transplanted to new constraint environments.

The entire project is **formally verified**, meaning all definitions are mathematically precise, and all theorems are proven with logical certainty (zero axioms in core framework, zero sorrys throughout).

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

### Shielding Characterization

The project also proves the mathematical boundary between spillover and insulation:

* **Shielding Condition:** V_int preserved on a cycle iff ∑(e' - c)² = ∑(e_calm - c)²
* **Generic Spillover:** When phases change to optimize external cost, the shielding condition is generically violated (requires measure-zero fine-tuning to preserve)
* Proven: `shielding_characterization` and `generic_spillover_contrapositive`
* **Key insight:** Insulation from spillover requires exact algebraic cancellation - a degenerate, non-generic constraint on configuration space.

---

## 🧮 Key Concept 5: Conservation of Holonomy

This proves two fundamental conservation laws for how holonomy behaves when paths are merged into cycles.

* **Path Merging:** Two edge-disjoint paths that connect head-to-tail form a cycle
* **Law of Emergence:** K_cycle = K_path₁ + K_path₂ (holonomy adds when merging to cycle)
* **Law of Averaging:** When constraint-averaging two systems, K_final = (K₁ + K₂) / 2
* Proven: `law_of_emergence` and `law_of_averaging` with complete distinct_edges proofs (zero axioms, zero sorrys)
* **Key insight:** Holonomy is conserved through system composition - it emerges from combining constraints, and averages when merging perspectives.

---

## 🧬 Key Concept 6: Purpose Survival Through Constraint Averaging

This proves that optimized phase structure persists when constraints are averaged with an unoptimized system.

* **The Setup:** Merge X_Purposeful (phases [0,2,1], constraints 10.0) with X_Opposed (phases [0,0,0], constraints 0.0)
* **The Merged World:** Constraint averaging creates new world with constraints = 5.0
* **Two Candidates in the 5.0-constraint world:**
    * **X_NewCalm:** phases [0,0,0] (minimize V_int only) → ℒ = 175
    * **X_Halfway:** phases [0,1,0.5] (adapted from purposeful) → ℒ = 169
* Proven: `purpose_survives_consensus`
* **Key insight:** The adapted configuration [0,1,0.5] outperforms the naive baseline [0,0,0] in the merged constraint world, proving that optimized phase structure survives constraint averaging.

---

## 🧬 Key Concept 7: The Inheritance Theorem

This proves that inheriting historically-optimized structure beats starting from scratch when merging systems.

* **The Setup:** Compare two strategies when merging a frustrated system into a new constraint world
    * **Calm Strategy:** Start with all phases at 0 (minimizes V_int only)
    * **Inheritance Strategy:** Scale down the original optimized phases by 1/2
* **The Physical Trade-Off:** Define two quantities:
    * **Cost of Purpose:** `V_int(original) - Σ(c_A)²` - the internal cost penalty paid to satisfy the external task
    * **Inheritance Payoff:** `3 × lam_ext × ext_target²` - the weighted external cost advantage from inheritance
* **Main Result:** When Cost of Purpose < Inheritance Payoff, inheritance beats calm
    * Proven: `inheritance_beats_calm`
    * The theorem does NOT assume the result - it assumes only the physical trade-off condition
    * V_int scaling proven from first principles: halving phases and constraints → V_int scales by 1/4
* **Key insight:** Historical optimization has value that survives system merging. When a system paid internal cost to achieve external purpose, that optimization structure remains valuable even when transplanted to a new constraint environment (at half-scale).

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
    * Defines `V_int_on_cycle` (internal cost restricted to a single cycle).
    * Proves `shielding_characterization` and `generic_spillover_contrapositive` (spillover boundary conditions).
* **`Diaspora/ConservationOfHolonomy.lean`**
    * Defines `Path` (open paths with distinct edges) and `MergeablePaths` (edge-disjoint paths forming cycles).
    * Proves `merge_to_cycle` (two paths merge to cycle with all properties verified).
    * Proves `law_of_emergence`: K_cycle = K_path₁ + K_path₂ (holonomy adds when merging).
    * Proves `law_of_averaging`: K_final = (K₁ + K₂) / 2 (holonomy averages under constraint merging).
    * Complete proofs including full `distinct_edges` verification (zero axioms, zero sorrys).
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
* **`Diaspora/Experiments/PurposeSurvival.lean`**
    * Tests whether optimized phase structure survives constraint averaging.
    * Merges purposeful (constraints 10.0) with opposed (constraints 0.0) systems.
    * Proves adapted configuration outperforms naive baseline in merged 5.0-constraint world.
    * Demonstrates that optimization structure persists through consensus mechanisms.
* **`Diaspora/InheritanceTheorem.lean`**
    * Proves the Inheritance Theorem: historical optimization beats starting from scratch.
    * Defines inheritance scenario: original optimized system merged at half-scale vs calm baseline.
    * Proves V_int scaling lemmas from first principles (halving phases/constraints → V_int scales by 1/4).
    * Main theorem `inheritance_beats_calm` assumes only physical trade-off: Cost of Purpose < Inheritance Payoff.
    * Complete proof with zero sorrys, using distributive law for nested sums with dependent types.

## ✅ Verification

All proofs are complete with zero sorrys. Core framework has zero axioms. Experiments use axioms only for physics bridge (Schwarzschild derivation):

```bash
lake build                                           # Clean build, 1791 jobs
rg "^axiom " Diaspora/*.lean                         # 0 matches (core framework)
rg "^axiom " Diaspora/Experiments/*.lean | wc -l     # 4 matches (Schwarzschild bridge axioms only)
rg "^sorry" Diaspora/*.lean Diaspora/Experiments/*.lean  # 0 matches
```
