# Diaspora Experiments

This directory contains computational experiments that generate empirical data
for formal verification in the Lean proofs.

## Gauge Negotiation Experiment

**File:** `gauge_negotiation.py`

**Purpose:** Demonstrates that reality emerges from negotiation between incompatible
perspectives rather than convergence to a shared frame.

**What it does:**
- Evolves graph G_A under high complexity cost (λ=10.0) → sparse, rigid
- Evolves graph G_B under low complexity cost (λ=0.1) → dense, adaptive
- Crosses them to create G_N, then evolves under neutral cost (λ=1.0)
- Shows G_N achieves lower Lagrangian than either parent under neutral conditions

**Formal verification:**
- `Diaspora/GaugeNegotiationVerified.lean` - Data layer (graphs, constraints, phases)
- `Diaspora/GaugeNegotiationExplicit.lean` - Proof layer (ZERO sorries)

**Reproducibility:**
Uses `np.random.seed(42)` to ensure deterministic generation of the constraint
matrix C_initial that is hard-coded in the Lean proofs. Running this script
produces the exact values verified in the formalization.

**Usage:**
```bash
./experiments/gauge_negotiation.py
```

The script uses PEP 723 inline script metadata for dependencies (numpy, networkx, matplotlib).
UV will automatically install them in an isolated environment when you run the script.
