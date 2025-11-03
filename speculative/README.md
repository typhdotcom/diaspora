# Speculative and Work-in-Progress

This directory contains exploratory and incomplete work that is not part of the main proof.

## Files

### Axioms.lean
Abstract axiomatization of ConfigSpace. Not used by any active proofs - all concrete proofs work directly from mathematical primitives in Mathlib.

### GaugeNegotiation.lean
Abstract framework for gauge negotiation with 11 axioms. Superseded by concrete construction in main codebase.

### SelfModelHolonomy.lean
Self-modeling framework with 7 axioms. Interesting but not part of core holonomy proof.

### Related files
- PredictiveSelfModel.lean
- SelfAwarenessDynamics.lean
- SelfModelHolonomyRefactored.lean
- ConcreteModel.lean
- GaugeNegotiationComputed.lean

## Status

These files contain interesting ideas but are not maintained as part of the core proof. They may contain sorries, incomplete proofs, or axioms that haven't been proven.

The main codebase in `Diaspora/` contains zero axioms and zero sorries.
