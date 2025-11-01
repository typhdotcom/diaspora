# axiom audit: what's foundational vs eliminable

generated 2025-11-01 by yatima after holonomy proof completion

## summary

**total axioms found:** ~80-100 across all files
**genuinely foundational:** ~15-20
**eliminable:** ~60-80

## core proven results (zero axioms)

✅ **HolonomyLagrangeProof.lean** - V_int ≥ K²/n (COMPLETE, zero axioms, zero sorrys)
✅ **GaugeTheoreticHolonomy.lean** - gauge structure + cycles (COMPLETE, zero axioms, zero sorrys)

## file-by-file analysis

### Axioms.lean (11 axioms)

**foundational (keep):**
```lean
axiom V_int : ConfigSpace → ℝ              -- internal cost function
axiom V_ext : ConfigSpace → ℝ              -- external cost function
axiom E : ConfigSpace → ℕ                  -- complexity measure
axiom K : ConfigSpace → ConfigSpace        -- gradient descent operator
```

**eliminable:**
```lean
axiom V_int_nonneg (X : ConfigSpace) : 0 ≤ V_int X        -- proven in Concrete.lean
axiom V_ext_nonneg (X : ConfigSpace) : 0 ≤ V_ext X        -- proven in Concrete.lean
axiom K_reduces_V_int (X : ConfigSpace) : V_int (K X) ≤ V_int X  -- proven in Concrete.lean
```

**status:** can reduce 11 → 4 by using Concrete.lean definitions

### HolonomyProof.lean (3 axioms)

**all marked as proven elsewhere:**
```lean
axiom cycle_creates_holonomy  -- PROVEN in GaugeTheoreticHolonomy.lean
axiom triangle_min_edges      -- pedagogical, can be definition
axiom satisfies_task_has_cycle  -- follows from task structure
```

**status:** can eliminate all 3 (backward compatibility only)

### Task.lean (7 axioms)

**most are definitions disguised as axioms:**
```lean
axiom V_ext_task : ConfigSpace → ExternalTask → ℝ  -- should be def
axiom edge_count : Graph → ℕ                        -- should be def
axiom min_edges_for_task : ExternalTask → ℕ        -- should be def
```

**status:** can eliminate 6/7 by making them definitions

### NoPrivilegedFrame.lean (5 axioms)

**genuinely foundational (keep):**
```lean
axiom gauge_preserves_structure              -- defines gauge transformations
axiom V_int_not_gauge_invariant             -- key property
axiom lagrangian_has_minimizer              -- existence assumption
```

**eliminable:**
```lean
axiom gauge_acts_transitively_on_V_ext_levels  -- probably provable
axiom gauge_creates_alternative_minimizer       -- probably provable
```

**status:** keep 3/5

### MathematicalStructure.lean (10 axioms)

**foundational (differential geometry, stat mech):**
```lean
axiom config_topology : TopologicalSpace ConfigSpace
axiom config_measurable_space : MeasurableSpace ConfigSpace
axiom config_measure : MeasureTheory.Measure ConfigSpace
axiom gauge_field_curvature : differential geometry connection
axiom lagrangian_is_free_energy : statistical mechanics
```

**already proven:**
- lagrangian_continuous → THEOREM (proven)
- K_is_gradient_step → DEFINITION (not axiom)

**status:** 10 axioms but many already eliminated, keep ~5

### HolonomicMemory.lean (6 axioms)

**all about parameter evolution:**
```lean
axiom evolve : ParameterPath → ℝ → ConfigSpace
axiom evolve_minimizes
axiom geometric_phase
axiom evolution_path_dependent
```

**status:** these define adiabatic evolution. can probably be definitions with ODE solver. eliminate 5/6.

### Consciousness.lean (7 axioms)

**genuinely foundational:**
```lean
axiom attractor_stability                           -- dynamical systems
axiom conscious_requires_self_model                 -- definition of consciousness
axiom attractor_recursive_well_characterization     -- key structure
```

**eliminable:**
```lean
axiom configs_with_different_depths  -- construction, not axiom
axiom gauge_changes_consciousness    -- probably provable from gauge structure
```

**status:** keep 3/7

### GaugeNegotiation.lean (15 axioms)

**most are probably theorems:**
```lean
axiom negotiation_convergence              -- should prove from dynamics
axiom negotiation_creates_novelty          -- should prove
axiom negotiation_intermediate_complexity  -- should prove
```

**status:** these should all be provable from holonomy + dynamics. eliminate 12/15, keep 3 foundational.

### RateDistortion.lean (1 axiom)

```lean
axiom subcritical_forces_recursion  -- connects to holonomy, probably provable
```

**status:** eliminate 1/1

### Existence.lean (1 axiom)

```lean
axiom conscious_attractors_exist  -- hard existence theorem
```

**status:** genuinely hard, keep for now. but might be provable from compactness + holonomy bound.

### UncertaintyProof.lean (2 axioms)

```lean
axiom is_planar : Graph → Prop
axiom planar_excludes_K5
```

**status:** first should be definition, second is graph theory theorem. eliminate 2/2.

### GaugeInvariants.lean (7 axioms)

**all about perspective-relativity:**
```lean
axiom perspective_relative_not_objective
axiom invariant_properties_sigma_algebra
axiom V_int_perspective_relative
```

**status:** these formalize gauge theory structure. keep 4/7, prove rest.

### ConcreteModel.lean (3 sorrys)

**continuity proofs:**
```lean
sorry -- concrete_V_int_continuous
sorry -- concrete_V_ext_continuous
sorry -- concrete_E_continuous
```

**status:** not critical for core result. can leave as sorrys or prove with topology lemmas. priority: low.

## recommended elimination strategy

### phase 1: easy wins (eliminate ~30 axioms)

1. **Task.lean** - convert axioms to definitions (6 axioms → 0)
2. **HolonomyProof.lean** - mark all as proven elsewhere (3 axioms → 0)
3. **UncertaintyProof.lean** - use graph theory library (2 axioms → 0)
4. **RateDistortion.lean** - prove from holonomy (1 axiom → 0)
5. **Axioms.lean** - use Concrete.lean (11 axioms → 4)
6. **HolonomicMemory.lean** - convert to definitions (6 axioms → 1)

**total reduction: ~30 axioms**

### phase 2: moderate effort (eliminate ~20 axioms)

1. **GaugeNegotiation.lean** - prove from dynamics (15 axioms → 3)
2. **NoPrivilegedFrame.lean** - prove gauge properties (5 axioms → 3)
3. **Consciousness.lean** - prove from structure (7 axioms → 3)

**total reduction: ~20 axioms**

### phase 3: hard (eliminate ~10-15 axioms)

1. **MathematicalStructure.lean** - reduce to minimal geometric foundations
2. **Existence.lean** - prove attractor existence from compactness
3. **GaugeInvariants.lean** - prove perspective-relativity results

**total reduction: ~10-15 axioms**

## final axiom count projection

**before:** ~80-100 axioms
**after phase 1:** ~50-70 axioms
**after phase 2:** ~30-50 axioms
**after phase 3:** ~15-20 axioms (genuinely foundational)

## genuinely foundational axioms (cannot eliminate)

these require either:
- choosing a concrete physical/mathematical model
- deep theorems in differential geometry / dynamical systems
- statistical mechanics foundations

1. **topological/measure structure** (ConfigSpace has topology, measure)
2. **gauge theory** (what gauge transformations are allowed)
3. **lagrangian = free energy** (statistical mechanics connection)
4. **existence of attractors** (compactness + coercivity, provable but hard)
5. **consciousness definition** (what self-model means)

everything else should be **provable** or **definable**.

## immediate action items

start with Task.lean - easiest file to clean:

```bash
# convert axioms to definitions
axiom V_ext_task → def V_ext_task := ...
axiom edge_count → def edge_count := ...
axiom min_edges_for_task → def min_edges_for_task := ...
```

this alone eliminates 6 axioms with ~20 lines of code.
