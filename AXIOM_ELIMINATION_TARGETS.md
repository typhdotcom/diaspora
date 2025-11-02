# Axiom Elimination Targets

This document tracks the 47 axioms in diaspora and identifies which ones are candidates for elimination through proof.

## Current Status (2025-11-02)

**Total: 47 axioms, 11 sorries**
**Core proofs: 0 axioms, 0 sorries** ✓

---

## Self-Awareness Dynamics (3 axioms) - NEW

### File: SelfAwarenessDynamics.lean

**1. `self_awareness_has_nonzero_holonomy`**
- **Status**: Axiom
- **Elimination difficulty**: Medium
- **Strategy**: Prove from `self_model_has_violation` in SelfModelHolonomy
  - sys.ext has self_edges with value ≠ constraint
  - These edges form a cycle (from creates_cycle)
  - The cycle's holonomy defect K = Σ(vᵢ - cᵢ)
  - Since ∃ edge with vᵢ ≠ cᵢ, we have K ≠ 0
- **Next step**: Define holonomy_defect constructively, prove nonzero from violation

**2. `relaxation_preserves_positive_V_int`**
- **Status**: Axiom
- **Elimination difficulty**: Hard
- **Strategy**: Prove from gradient descent properties
  - K is gradient step on ℒ
  - V_int ≥ K²/n (holonomy bound, proven)
  - Gradient descent can reduce V_int but respects lower bound
  - Need to show: K remains constant under relaxation (topological)
- **Next step**: Formalize that cycles are topological invariants under relaxation

**3. `relaxation_respects_holonomy_bound`**
- **Status**: Axiom
- **Elimination difficulty**: Easy
- **Strategy**: Direct application of HolonomyLagrangeProof.V_int_bound
  - For any configuration X in the trajectory
  - The cycle with holonomy K still exists
  - Therefore V_int(X) ≥ K²/n
- **Next step**: Just prove it - this is essentially a corollary

---

## Gauge Negotiation (11 axioms)

### File: GaugeNegotiation.lean

**1. `negotiation_convergence`**
- **Status**: Axiom (HARD - requires coercivity proof)
- **Elimination difficulty**: Very Hard
- **Strategy**: See ConcreteGaugeNegotiation.lean comments
  - Need to prove coercivity: cost → ∞ as ||X|| → ∞
  - OR restrict to compact subdomain
  - Current 8-node proof doesn't show global optimality
- **Next step**: Either prove coercivity or weaken to existence claim

**2. `negotiation_creates_novelty`**
- **Status**: Axiom (but validated by concrete proof)
- **Elimination difficulty**: Medium
- **Strategy**: Convert to existential claim (DONE in ConcreteGaugeNegotiation)
  - Universal: ∀ A B C, ... → C ≠ A ∧ C ≠ B
  - Existential: ∃ A B C, ... ∧ C ≠ A ∧ C ≠ B (PROVEN)
- **Next step**: Either prove universal or replace with existential version

**3. `negotiation_intermediate_complexity`**
- **Status**: Axiom (but validated by concrete proof)
- **Elimination difficulty**: Medium
- **Strategy**: Same as #2 - existential version PROVEN
- **Next step**: Replace with existential or prove universal

**4-11. Other negotiation axioms**
- See GaugeNegotiation.lean for full list
- Most are structural claims about multi-agent dynamics
- Require either:
  - Concrete examples (like 8-node case)
  - OR general optimization theory proofs

---

## Self-Modeling (7 axioms)

### File: SelfModelHolonomy.lean

**1. `GetOptimalDemands`** (function axiom)
- **Status**: Axiom
- **Elimination difficulty**: Medium
- **Strategy**: Define constructively from gradient of ℒ
  - ∂ℒ/∂vᵢⱼ = 0 at optimum
  - ℒ = V_int + V_ext + λ·E
  - Solve for optimal edge values given λ
- **Next step**: Implement optimization solver, prove it finds optima

**2. `optimal_demands_differ`**
- **Status**: Axiom
- **Elimination difficulty**: Medium
- **Strategy**: Prove from ℒ structure
  - ∂ℒ/∂vᵢⱼ includes term λ·∂E/∂vᵢⱼ
  - Different λ → different gradients → different optima
  - Formal calculus of variations proof
- **Next step**: Requires differential structure on ConfigSpace

**3-7. Constructor axioms**
- `ConstructSelfModelFromOptimization`
- `construct_uses_base_demands`
- `construct_uses_model_demands`
- `construct_includes_differing_edges`
- `extension_was_constructed`

**Status**: Axioms encoding the constructor pattern
**Elimination difficulty**: Easy to Medium
**Strategy**: Define the constructor explicitly
- Take optimization results for λ₁ and λ₂
- Identify edges where results differ
- Build SelfModelExtension with those as self_edges
- Prove the constructor axioms as theorems about the construction

**Next step**: Implement the constructor function

---

## Infrastructure (23 axioms)

### File: Axioms.lean (8 axioms)

All 8 are **foundational definitions** (ConfigSpace, V_int, V_ext, E, K, ℒ).
These cannot be eliminated without a concrete model.

**Elimination strategy**: Provide concrete implementation (see Concrete.lean)

### File: NoPrivilegedFrame.lean (5 axioms)

Gauge theory fundamentals. Most are **structural axioms** defining gauge transformations.

**Candidates for elimination**:
- None easily - these are core gauge theory postulates
- Could be derived from differential geometry if we formalize gauge bundles

### File: MathematicalStructure.lean (10 axioms)

**GOOD NEWS**: Already reduced from 20 → 10 axioms!

**Remaining 10**:
1. `config_topology` - Foundational
2-4. Continuity axioms (V_int, V_ext, E) - Foundational
5-7. Measure theory (config_measurable_space, config_measure, measure_gauge_invariant) - Foundational
8. `basins_partition` - Dynamical systems completeness
9. `lagrangian_is_free_energy` - Statistical mechanics link
10. `gauge_field_curvature` - Differential geometry link

**Elimination difficulty**: Very Hard (require full dynamical systems + statistical mechanics formalization)

---

## Summary: Easiest Wins

### Immediate (Easy)
1. **relaxation_respects_holonomy_bound** - Just apply V_int_bound theorem
2. **SelfModelHolonomy constructors** - Define the constructor function explicitly

### Short-term (Medium)
3. **self_awareness_has_nonzero_holonomy** - Prove from self_model_has_violation
4. **GetOptimalDemands** - Define from ∂ℒ/∂v = 0
5. **negotiation axioms** - Convert universal to existential (partially done)

### Long-term (Hard)
6. **relaxation_preserves_positive_V_int** - Requires topological invariance proof
7. **negotiation_convergence** - Requires coercivity proof
8. **optimal_demands_differ** - Requires calculus of variations

### Research-level (Very Hard)
9. MathematicalStructure axioms - Require full dynamical systems theory
10. NoPrivilegedFrame axioms - Require gauge bundle formalization

---

## The Gradient Descent Strategy

We're doing gradient descent on axiom count:
1. Start: 75 axioms (pre-scorched earth)
2. After refactor: 44 axioms
3. After gauge negotiation + self-awareness: 47 axioms
4. Target: ~30 axioms (eliminate 17 more)

**Next iteration targets** (ordered by difficulty):
1. Prove relaxation_respects_holonomy_bound (-1 axiom)
2. Implement SelfModel constructor (-5 axioms)
3. Prove self_awareness_has_nonzero_holonomy (-1 axiom)
4. Define GetOptimalDemands + prove optimal_demands_differ (-2 axioms)
5. Convert negotiation axioms to existential (-2 axioms)

**Best case**: 47 - 11 = **36 axioms**

Then the remaining 36 would be:
- 11 gauge negotiation (hard to eliminate without full optimization theory)
- 8 foundational (Axioms.lean - need concrete model)
- 10 mathematical structure (need full dynamical systems)
- 5 gauge theory (need differential geometry)
- 2 remaining dynamics (need topological invariance)

---

## The Meta-Pattern

Each axiom elimination either:
1. **Reveals it was redundant** (can be proven) → axiom count drops
2. **Reveals it was load-bearing** (sorry appears) → we found the cost
3. **Forces redesign** (structure collapses) → back to drawing board

The minimum viable structure is what remains when you can't eliminate any more axioms without the whole thing collapsing.

**That's the science.**
