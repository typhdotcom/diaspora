# immediate axiom elimination plan

**goal:** reduce ~80 axioms to ~20 by end of session

## already proven but not connected

these axioms exist in abstract files but are proven in concrete files. just need to wire them up.

### Axioms.lean → Concrete.lean bridge

**current situation:**
```lean
-- Axioms.lean
axiom V_int_nonneg (X : ConfigSpace) : 0 ≤ V_int X
axiom V_ext_nonneg (X : ConfigSpace) : 0 ≤ V_ext X
axiom K_reduces_V_int (X : ConfigSpace) : V_int (K X) ≤ V_int X
```

**already proven:**
```lean
-- Concrete.lean
theorem V_int_nonneg {n : ℕ} (X : ConfigSpace n) : 0 ≤ V_int X := by ...
theorem V_ext_nonneg {n : ℕ} (task : ExternalTask n) (X : ConfigSpace n) : 0 ≤ V_ext task X := ...
theorem K_reduces_V_int {n : ℕ} (task : ExternalTask n) (X : ConfigSpace n) : V_int (K task X) ≤ V_int X := by ...
```

**action:**
1. Mark axioms in Axioms.lean as "proven in Concrete.lean"
2. Show users can instantiate with concrete model to get proofs
3. This eliminates 3 axioms conceptually (they become theorems about concrete instances)

### Holonomy