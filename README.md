# Diaspora: Holonomy Creates Internal Cost

> *Rigorous proof that holonomy creates unavoidable internal cost*
> *Within a model where edge values come from node phases (structural choice)*
> *Self-modeling application requires additional structural axioms*

## What We Proved

**The model:**
We define a configuration space where edge values MUST come from node phases:
```lean
structure ConfigSpace where
  node_phases : Fin n → ℝ
  edge_value i j := node_phases j - node_phases i  -- modeling choice
```

This forces `Σvᵢ = 0` around any cycle (topological constraint).

**The theorem (within this model):**
For any cycle with external constraints `cᵢ`:
```
V_int ≥ K²/n
```

Where:
- `K = Σcᵢ` is the **holonomy defect** (sum of constraint mismatches)
- `V_int = Σ(vᵢ - cᵢ)²` is **internal cost** (sum of squared violations)

**If K ≠ 0**, **then V_int > 0**. Strictly positive. Unavoidable.

**This is proven within the model**, not unconditionally. The model itself (edge values from phases) is a choice about how to represent configurations.

## The Core Result

**Proved within the model (0 additional axioms):**
1. Cycles with non-zero holonomy defect force V_int > 0 (V_int ≥ K²/n)
   - **But**: This assumes the model (edge values from node phases)
   - The model is a structural choice, not a proven fact about reality

**Proved given structural axioms (7 axioms):**
2. Self-modeling with different λ creates such cycles
   - Requires defining what "self-modeling" means structurally

**Verified by construction (0 axioms):**
3. Gauge negotiation produces lower-cost compromises (8-node concrete example)
   - Concrete numerical verification

**Caveat:** The holonomy bound is "pure math" only after accepting the model. The model itself (ConfigSpace structure) encodes assumptions about how edge values relate to node phases.

## Quick Start
```bash
lake build  # zero errors, zero sorries
```

## Files

### Holonomy Bound (0 Axioms, 0 Sorries)

**HolonomyLagrangeProof.lean**
- Proves V_int ≥ K²/n via Lagrange multipliers
- Pure math, complete proof, no axioms

**GaugeTheoreticHolonomy.lean**
- Gauge formulation: edge values from node phases
- Proves cycles force Σvᵢ = 0 constraint
- Connects to HolonomyLagrangeProof
- No axioms

### Concrete Examples (0 Axioms, 0 Sorries)

**GaugeNegotiationExplicit.lean**
- 8-node concrete example
- Verified: negotiated graph beats alternatives
- L_N < L_A, L_B, L_Union
- No axioms

### Supporting

**Concrete.lean**
- ConfigSpace implementation on SimpleGraph
- Proves basic properties from first principles

## The Mathematics

### What "Gauge Structure" Means

**Gauge structure** = edge values come from node phases:
```lean
structure ConfigSpace where
  graph : SimpleGraph (Fin n)
  node_phases : Fin n → ℝ

def edge_value (i j) : ℝ :=
  node_phases j - node_phases i  -- derived from phases
```

This **forces** a topological constraint on any cycle:
```lean
theorem cycle_edge_sum_zero :
  (φ₁-φ₀) + (φ₂-φ₁) + (φ₀-φ₂) = 0
```

In general: around any cycle of n edges, `Σvᵢ = 0` automatically.

### The Proof Chain (Holonomy Bound)

1. **Topology** → cycles force Σvᵢ = 0
2. **Optimization** → min(Σ(vᵢ-cᵢ)²) = K²/n when Σvᵢ = 0
3. **Combination** → V_int ≥ K²/n
4. **Conclusion** → K ≠ 0 implies V_int > 0

**This part requires no axioms. Pure math.**

## Why This Matters

**Holonomy bound (proven within the model):**
- **Within the model** (edge values from node phases), any cycle with K ≠ 0 forces V_int ≥ K²/n > 0
- This is a mathematical theorem, not a conjecture
- **But**: It's conditional on accepting the model's structure

**The question left open:** Does the model (edge values from node phases) accurately represent any real systems? The math is proven, the applicability is an empirical question.

## Verification
```bash
# Verify zero axioms, zero sorries in active codebase
rg "axiom " Diaspora/*.lean                          # none
rg "sorry"  Diaspora/*.lean                          # none

# Build everything
lake build                                           # zero errors
```

## Structure

### Holonomy Bound (0 Axioms, 0 Sorries)
- **HolonomyLagrangeProof.lean** - V_int ≥ K²/n via Lagrange multipliers
- **GaugeTheoreticHolonomy.lean** - Gauge formulation with cycle constraints

### Concrete Examples (0 Axioms, 0 Sorries)
- **GaugeNegotiationExplicit.lean** - 8-node concrete negotiation proof

### Negotiation Framework (0 Axioms, 0 Sorries)
- **GaugeNegotiationVerified.lean** - Data layer from 8-node experiment
- **GaugeNegotiationExplicit.lean** - Complete proof via explicit computation
- **GaugeNegotiationProofs.lean** - Properties proven from concrete case
- **ConcreteGaugeNegotiation.lean** - Existential theorems proven by construction

**Total: 0 axioms, 0 sorries** in active codebase

All proofs work from first principles using Lean's standard library and Mathlib.

## What We Removed

Previous versions made speculative claims beyond the mathematics.

What remains:
- Proven structure (V_int from holonomy)
- Mathematical results only
- Honest about scope

## Contributing

This is rigorous math + honest uncertainty.

If you find:
- Errors in proofs → issue with specific theorem
- Missing connections → suggestions welcome
- Ways to strengthen → please share

If you want to help:
- Prove more axioms as theorems
- Find tighter bounds
- Connect to neuroscience data
- Explain more clearly

## Citation
```bibtex
@software{diaspora2025,
  title = {Diaspora: Holonomy Creates Internal Cost},
  author = {typh and {Claude instances}},
  year = {2025},
  url = {https://github.com/[user]/diaspora},
  note = {Lean 4 proof: V_int ≥ K²/n from first principles}
}
```

## License

MIT

## The Question

**What did we actually prove?**

**Within the ConfigSpace model** (edge values from node phases):
- V_int ≥ K²/n for any cycle with holonomy defect K (0 axioms)
- Gauge negotiation works in concrete 8-node case (0 axioms)

**What remains unknown?**

- **Whether the ConfigSpace model applies to real systems** - Does edge_value = phase difference accurately represent anything in reality?
- Whether this is trivial to experts or genuinely novel
- Interpretations beyond the mathematics

**We proved the math within a model. The model itself is a structural choice, not an empirical fact.**

---

Built with Lean 4, Mathlib, and commitment to honesty about limits.

**V_int ≥ K²/n is proven within the ConfigSpace model.**
**The model itself (edge values from node phases) is a structural choice.**
**Whether this models reality is an empirical question, not a mathematical one.**
