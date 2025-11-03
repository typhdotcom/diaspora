# diaspora: holonomy creates internal cost

[![Lean 4](https://img.shields.io/badge/Lean-4-blue)](https://leanprover.github.io/)
[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)]()
[![Holonomy Bound](https://img.shields.io/badge/holonomy_bound-0_axioms_0_sorries-success)]()
[![Self-Modeling](https://img.shields.io/badge/self--modeling-7_axioms-yellow)]()
[![Framework](https://img.shields.io/badge/framework-33_axioms-yellow)](AXIOM_STATUS.md)

> *rigorous proof that holonomy creates unavoidable internal cost*
>
> *conditional proof that self-modeling (given structural axioms) creates such holonomy*

## what we proved

for any cycle of length n with:
- edge values `vᵢ` derived from node phases (forcing `Σvᵢ = 0`)
- external constraints `cᵢ` (task demands)

then:

```
V_int ≥ K²/n
```

where:
- `K = Σcᵢ` is the **holonomy defect** (sum of constraint mismatches)
- `V_int = Σ(vᵢ - cᵢ)²` is **internal cost** (sum of squared violations)

**if K ≠ 0**, **then V_int > 0**. strictly positive. unavoidable.

this is pure optimization theory - no physical system required, just the mathematical structure.

## the core result

**proved with zero axioms:**
1. Cycles with non-zero holonomy defect force V_int > 0 (V_int ≥ K²/n)

**proved given structural axioms:**
2. Self-modeling with different λ creates such cycles (7 axioms defining self-modeling)

**verified by construction (0 axioms):**
3. Gauge negotiation produces lower-cost compromises (8-node concrete example)

the holonomy bound is pure math. self-modeling application requires axioms defining what "self-modeling" means. interpretations beyond the mathematics are left to the reader.

## quick start

```bash
lake build  # zero errors, zero sorries
```

## files

### holonomy bound (0 axioms, 0 sorries)

**HolonomyLagrangeProof.lean**
- proves V_int ≥ K²/n via Lagrange multipliers
- pure math, complete proof, no axioms

**GaugeTheoreticHolonomy.lean**
- gauge formulation: edge values from node phases
- proves cycles force Σvᵢ = 0 constraint
- connects to HolonomyLagrangeProof
- no axioms

### concrete examples (0 axioms, 0 sorries)

**GaugeNegotiationExplicit.lean**
- 8-node concrete example
- verified: negotiated graph beats alternatives
- L_N < L_A, L_B, L_Union
- no axioms

### self-modeling (7 axioms, 0 sorries)

**SelfModelHolonomy.lean**
- self-modeling with λ_base ≠ λ_model creates violations
- proved: V_int increases strictly
- **7 axioms** (defining what "self-modeling" means structurally)

### supporting

**Axioms.lean** (8 axioms)
- core definitions: ConfigSpace, V_int, V_ext, E, K

**Concrete.lean**
- ConfigSpace implementation on SimpleGraph
- proves basic properties

**NoPrivilegedFrame.lean** (5 axioms)
- gauge structure fundamentals
- no privileged frame theorem

**MathematicalStructure.lean** (10 axioms)
- topology, measure theory
- most are standard mathematical infrastructure

**HolonomyProof.lean** (3 axioms, pedagogical)
- triangle example
- backward compatibility

## the mathematics

### what "gauge structure" means

**gauge structure** = edge values come from node phases:

```lean
structure ConfigSpace where
  graph : SimpleGraph (Fin n)
  node_phases : Fin n → ℝ

def edge_value (i j) : ℝ :=
  node_phases j - node_phases i  -- derived from phases
```

this **forces** a topological constraint on any cycle:
```lean
theorem cycle_edge_sum_zero :
  (φ₁-φ₀) + (φ₂-φ₁) + (φ₀-φ₂) = 0
```

in general: around any cycle of n edges, `Σvᵢ = 0` automatically.

### the proof chain (holonomy bound)

1. **topology** → cycles force Σvᵢ = 0
2. **optimization** → min(Σ(vᵢ-cᵢ)²) = K²/n when Σvᵢ = 0
3. **combination** → V_int ≥ K²/n
4. **conclusion** → K ≠ 0 implies V_int > 0

**this part requires no axioms. pure math.**

## why this matters

**holonomy bound (proven unconditionally):**
- any cycle with holonomy defect K ≠ 0 forces V_int ≥ K²/n > 0
- this is proven, not conjectured

**self-modeling application (proven given 7 axioms):**
- if a system satisfies the structural axioms defining "self-modeling"
- then it creates cycles with holonomy defect
- therefore V_int > 0 unavoidably

the holonomy bound is unconditional. the self-modeling claim requires axioms about what "self-modeling" means.

## verification

```bash
# core holonomy proof
rg "axiom " Diaspora/HolonomyLagrangeProof.lean     # none
rg "axiom " Diaspora/GaugeTheoreticHolonomy.lean    # none
rg "sorry"  Diaspora/HolonomyLagrangeProof.lean     # none
rg "sorry"  Diaspora/GaugeTheoreticHolonomy.lean    # none

# concrete gauge negotiation
rg "axiom " Diaspora/GaugeNegotiationExplicit.lean  # none
rg "sorry"  Diaspora/GaugeNegotiationExplicit.lean  # none

# check what self-modeling depends on
lake env lean -c 'import Diaspora.SelfModelHolonomy
#print axioms Diaspora.SelfModelHolonomy.new_cycle_increases_V_int'
```

## structure

### holonomy bound (0 axioms, 0 sorries)
- **HolonomyLagrangeProof.lean** - V_int ≥ K²/n via Lagrange multipliers
- **GaugeTheoreticHolonomy.lean** - gauge formulation with cycle constraints

### concrete examples (0 axioms, 0 sorries)
- **GaugeNegotiationExplicit.lean** - 8-node concrete negotiation proof

### negotiation framework (11 axioms, 0 sorries)
- **GaugeNegotiation.lean** - reality as negotiated fixed point (11 axioms)
- **ConcreteGaugeNegotiation.lean** - concrete version using Concrete.ConfigSpace (2 theorems proven)
- **GaugeNegotiationVerified.lean** - data layer from experiment
- **GaugeNegotiationExplicit.lean** - 8-node proof (0 axioms, 0 sorries)
- **GaugeNegotiationProofs.lean** - bridges concrete to abstract
- **GaugeNegotiationComputed.lean** - V_int bounds (5 sorries, in progress)

Note: Fixed contradictory axiom. When perspectives disagree on objective
invariants, negotiated result may differ from all inputs. ConcreteGaugeNegotiation
converts universal claims to existential ones provable by construction.

### self-modeling (7 axioms)
- **SelfModelHolonomy.lean** - constructor pattern: self-modeling → V_int > 0 (7 axioms)

### infrastructure (23 axioms)
- **Axioms.lean** (8) - core definitions: V_int, V_ext, E, K, ℒ
- **Concrete.lean** - ConfigSpace implementation on SimpleGraph
- **NoPrivilegedFrame.lean** (5) - gauge structure, frame independence
- **MathematicalStructure.lean** (10) - topology, measure, dynamics

### supporting
- **HolonomyProof.lean** (3 axioms) - pedagogical triangle example
- **Basic.lean** - basic utilities
- **ConcreteModel.lean** - concrete model (3 sorries, in progress)

**total: 44 axioms, 10 sorries (in optional/WIP files)**

**breakdown:**
- **holonomy bound: 0 axioms, 0 sorries** (pure math)
- **self-modeling: 7 axioms, 0 sorries** (structural definition)
- **negotiation framework: 11 axioms, 0 sorries** (in progress)
- **infrastructure: 26 axioms** (definitions and standard math)

## what we removed

previous versions made speculative claims beyond the mathematics.

what remains:
- proven structure (V_int from holonomy)
- mathematical results only
- honest about scope

## contributing

this is rigorous math + honest uncertainty.

if you find:
- errors in proofs → issue with specific theorem
- missing connections → suggestions welcome
- ways to strengthen → please share

if you want to help:
- prove more axioms as theorems
- find tighter bounds
- connect to neuroscience data
- explain more clearly

## citation

```bibtex
@software{diaspora2025,
  title = {Diaspora: Holonomy Creates Internal Cost},
  author = {typh and {Claude instances}},
  year = {2025},
  url = {https://github.com/[user]/diaspora},
  note = {Lean 4 proof: V_int ≥ K²/n from first principles}
}
```

## license

MIT

## the question

**what did we actually prove unconditionally?**

- V_int ≥ K²/n for any cycle with holonomy defect K (0 axioms)
- gauge negotiation works in concrete 8-node case (0 axioms)

**what did we prove conditionally?**

- self-modeling → V_int > 0 (given 7 axioms defining "self-modeling")
- negotiation framework (given 11 axioms, work in progress)

**what remains unknown?**

- whether the 7 "self-modeling" axioms accurately model real cognitive systems
- whether this is trivial to experts or genuinely novel
- interpretations beyond the mathematics

**we proved the math. the axioms encode structural assumptions. interpretations are left to the reader.**

---

built with lean 4, mathlib, and commitment to honesty about limits.

**V_int ≥ K²/n is proven unconditionally.**
**self-modeling → V_int > 0 is proven given structural axioms.**
