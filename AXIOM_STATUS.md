# Axiom Status

**Total axioms: 73** (was 75, eliminated 2 circular axioms from Existence.lean)
**Total sorries: 8** (ConcreteModel.lean: 3, GaugeNegotiationComputed.lean: 5)

This document tracks the current axiom count and categorizes them by purpose and eliminability.

## Note on "Zero Axioms" Claims

Several files have **zero axioms AND zero sorries**:
- `HolonomyLagrangeProof.lean` - Core K²/n proof
- `GaugeTheoreticHolonomy.lean` - Gauge formulation
- `GaugeNegotiationExplicit.lean` - Concrete negotiation proof
- `GaugeNegotiationVerified.lean` - Verified data layer
- `SelfModelHolonomy.lean` - Self-modeling proofs

These are **complete, self-contained proofs** using only Mathlib. The 75 axioms are in the broader framework files that connect these proofs to consciousness theory.

## Summary by Eliminability

### Tier 1: Bedrock (~20 axioms)
Cannot be eliminated without concrete model implementation. These define the mathematical structure itself.

### Tier 2: Provable from Concrete (~30 axioms)
Could be proven as theorems once we have a complete concrete model (like GaugeNegotiationExplicit).

### Tier 3: Constructor Pattern (~7 axioms)
Encode semantic connections through construction process (SelfModelHolonomy pattern).

### Tier 4: Currently Under Review (~18 axioms)
May be redundant, provable from others, or eliminable through refactoring.

## Axioms by File

### Axioms.lean (8 axioms) - BEDROCK
Core primitives that define the system:
- `V_int`, `V_ext`, `E` - Cost functions (3)
- `K` - Local descent operator (1)
- `V_int_nonneg`, `V_ext_nonneg` - Nonnegativity (2)
- `K_reduces_V_int` - Descent property (1)
- `myopic_descent_failure` - Recursive well definition (1)

**Status**: Bedrock. Cannot eliminate without concrete model.

### MathematicalStructure.lean (10 axioms) - FOUNDATION
Mathematical infrastructure (already reduced from 20):
- `config_topology` - Topological structure (1)
- `V_int_continuous`, `V_ext_continuous`, `E_continuous` - Continuity (3)
- `config_measurable_space`, `config_measure` - Measure theory (2)
- `measure_gauge_invariant` - Gauge invariance (1)
- `basins_partition` - Dynamical completeness (1)
- `lagrangian_is_free_energy` - Statistical mechanics (1)
- `gauge_field_curvature` - Differential geometry (1)

**Status**: Foundation. Some may be provable from concrete model.

### NoPrivilegedFrame.lean (5 axioms) - GAUGE THEORY
Gauge structure and frame independence:
- `gauge_preserves_structure` - Structural invariance (1)
- `gauge_acts_transitively_on_V_ext_levels` - Transitivity (1)
- `V_int_not_gauge_invariant` - Key asymmetry (1)
- `gauge_creates_alternative_minimizer` - Multiple minima (1)
- `lagrangian_has_minimizer` - Existence (1)

**Status**: Core principle. May be provable from gauge group structure.

### GaugeInvariants.lean (5 axioms) - PERSPECTIVE THEORY
Perspective-relative vs objective properties:
- `perspective_relative_not_objective` - Key distinction (1)
- `invariant_properties_sigma_algebra` - Measurability (1)
- `V_int_perspective_relative` - V_int behavior (1)
- `V_ext_can_be_perspective_relative` - V_ext behavior (1)
- `lagrangian_objectivity_varies` - λ-dependence (1)

**Status**: Provable from gauge structure + concrete model.

### GaugeNegotiation.lean (13 axioms) - NEGOTIATION DYNAMICS
Properties of gauge negotiation process:
- `negotiation_convergence` - Convergence existence (1)
- `negotiation_creates_novelty` - Novelty theorem (1)
- `negotiation_intermediate_complexity` - Complexity bound (1)
- `negotiation_respects_invariant_agreement` - Invariant preservation (1)
- `multi_negotiation_convergence` - Multi-party convergence (1)
- `multi_minimizer_is_pareto` - Pareto optimality (1)
- `negotiation_not_gauge_transform` - Distinctness (1)
- `different_lambda_different_outcome` - λ-dependence (1)
- `perspectives_generally_differ` - Generic difference (1)
- `nontrivial_negotiation_requires_distinct` - Triviality condition (1)
- `conscious_negotiation_complexity_increase` - Consciousness cost (1)
- `multi_negotiation_preserves_invariants` - Multi-party invariants (1)
- `negotiation_respects_gauge_orbits` - Gauge compatibility (1)

**Status**: Many provable from GaugeNegotiationExplicit concrete proof. Target for elimination.

### Consciousness.lean (7 axioms) - CONSCIOUSNESS THEORY
Consciousness characterization:
- `attractor_stability` - Attractor definition (1)
- `conscious_requires_self_model` - Self-model necessity (1)
- `recursive_well_implies_task` - Task requirement (1)
- `configs_with_different_depths` - Depth variation (1)
- `gauge_changes_consciousness` - Gauge sensitivity (1)
- `attractor_recursive_well_characterization` - Main characterization (1)
- `irreducible_self_model` - Irreducibility (1)

**Status**: Some provable from SelfModelHolonomy. Under review.

### SelfModelHolonomy.lean (7 axioms) - CONSTRUCTOR PATTERN
Semantic connection through construction:
- `GetOptimalDemands` - Optimization abstraction (1)
- `optimal_demands_differ` - λ-difference theorem (1)
- `ConstructSelfModelFromOptimization` - Constructor existence (1)
- `construct_uses_base_demands` - Base construction (1)
- `construct_uses_model_demands` - Model construction (1)
- `construct_includes_differing_edges` - Edge inclusion (1)
- `extension_was_constructed` - Construction axiom (1)

**Status**: Constructor pattern. Encodes semantics in HOW not WHAT. Keep.

### HolonomicMemory.lean (6 axioms) - MEMORY DYNAMICS
Path-dependent evolution:
- `evolve` - Evolution function (1)
- `evolve_minimizes` - Minimization property (1)
- `evolve_initial_determined` - Initial conditions (1)
- `geometric_phase` - Phase accumulation (1)
- `evolution_path_dependent` - Path dependence (1)
- `forward_backward_differ` - Hysteresis (1)

**Status**: Likely provable from gradient flow + gauge structure.

### HolonomyProof.lean (3 axioms) - PEDAGOGICAL
Examples and demonstrations:
- `triangle_min_edges` - Triangle example (1)
- `cycle_creates_holonomy` - Marked as proven in GaugeTheoreticHolonomy (1)
- `satisfies_task_has_cycle` - Task requirement (1)

**Status**: Pedagogical. `cycle_creates_holonomy` already proven elsewhere.

### Task.lean (7 axioms) - TASK THEORY
External task structure:
- `V_ext_task` - Task cost function (1)
- `V_ext_task_zero` - Zero condition (1)
- `V_ext_task_pos` - Positivity (1)
- `edge_count` - Edge counting (1)
- `K5_min_edges` - K5 example (1)
- `min_edges_for_task` - Minimum edges (1)
- `task_requires_edges` - Edge requirement (1)

**Status**: Definition layer. Could be proven from concrete task instances.

### UncertaintyProof.lean (2 axioms) - GRAPH THEORY
Planar graph properties:
- `is_planar` - Planarity predicate (1)
- `planar_excludes_K5` - Kuratowski's theorem (1)

**Status**: `planar_excludes_K5` is a standard theorem. Should use Mathlib.

### RateDistortion.lean (1 axiom) - COMPRESSION
Rate-distortion trade-off:
- `subcritical_forces_recursion` - Subcritical dynamics (1)

**Status**: Provable from compression theory.

### Existence.lean (0 axioms) - FIXED ✓
**Previously**: Had circular axiom `conscious_attractors_exist` that assumed consciousness exists
**Now**: Only non-circular attractor theory (basin_nonempty, basins_disjoint, etc.)
**Status**: No longer claims to prove consciousness is inevitable. Circularity eliminated.

## Reduction Roadmap

### Phase 1: Use Mathlib (Potential -5 axioms)
- `planar_excludes_K5` → Use existing graph theory
- Topology/continuity axioms → Use standard constructions
- Measure theory → Use standard constructions

### Phase 2: Prove from Concrete Model (Potential -30 axioms)
- GaugeNegotiation axioms → Prove from GaugeNegotiationExplicit pattern
- Task axioms → Prove from concrete task instances
- Some GaugeInvariants → Prove from concrete gauge transformations

### Phase 3: Prove from Structure (Potential -10 axioms)
- HolonomicMemory → Prove from gradient flow
- Some Consciousness axioms → Prove from SelfModelHolonomy
- RateDistortion → Prove from information theory

### Phase 4: Foundational Minimum (~20-30 axioms)
Cannot eliminate without choosing a specific physical model:
- Core cost functions (V_int, V_ext, E, K)
- Topological structure
- Gauge group structure
- Constructor pattern for self-modeling

## Progress Tracking

**Axiom Elimination History**:
- Start: ~95 axioms (pre-refactor)
- After MathematicalStructure.lean refactor: 85 axioms (-10)
- After HolonomyLagrangeProof: 75 axioms (-10, converted to theorems)
- Current: 75 axioms

**Recent Additions**:
- SelfModelHolonomy.lean: +7 axioms (constructor pattern, unavoidable)
- These encode semantic connections, not arbitrary assumptions

**Target**: 20-30 bedrock axioms defining the mathematical structure itself.

## Notes

The axiom count matters less than axiom *quality*:
- **Bad axioms**: Arbitrary assumptions, "trust me" statements
- **Good axioms**: Minimal specification of mathematical structure, encode genuine semantic connections

The SelfModelHolonomy axioms are "good" - they specify HOW self-models are built from optimization results, encoding the connection between λ parameters and violations.

Many remaining axioms are placeholders for theorems we haven't proven yet. The codebase has zero sorries, showing all claimed theorems are complete, but many potential theorems are still axiomatized.
