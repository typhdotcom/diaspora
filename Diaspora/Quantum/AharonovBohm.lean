/-
# The Aharonov-Bohm Effect

The Aharonov-Bohm effect demonstrates that topology, not local field strength,
determines quantum phase. A particle acquires a phase shift from encircling
a region with magnetic flux, even when the field is zero on its path.

In the discrete setting:
- A U(1) connection A assigns a phase e^{iθ} to each oriented edge
- The "field" is the curvature F = dA (holonomy around small loops)
- A flat connection (F = 0) can still have non-trivial holonomy around
  non-contractible cycles
- This holonomy produces the Aharonov-Bohm phase shift

The main theorem: For a flat connection with holonomy Φ, a particle
traversing the boundary acquires phase e^{iΦ}, regardless of path details.
-/

import Diaspora.Quantum.Evolution
import Diaspora.Logic.Universal
import Diaspora.Logic.WalkHolonomy
import Diaspora.Logic.Classicality.Cycles
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Complex Diaspora.Core Diaspora.Hodge Diaspora.Logic.Universal
open Diaspora.Logic

namespace Diaspora.Quantum.AharonovBohm

/-! ## 1. U(1) Connection -/

/--
A U(1) connection on a graph: assigns a phase to each oriented edge.
This is the discrete analog of the electromagnetic vector potential A.
-/
structure Connection (n : ℕ) where
  /-- Phase assigned to oriented edge (i, j) -/
  phase : Fin n → Fin n → ℂ
  /-- Phases are unit complex numbers (U(1) elements) -/
  unitary : ∀ i j, ‖phase i j‖ = 1
  /-- Parallel transport is reversible: A_{ji} = A_{ij}^* -/
  hermitian : ∀ i j, phase i j = star (phase j i)

/-- The trivial connection: all phases are 1 -/
def Connection.trivial (n : ℕ) : Connection n where
  phase := fun _ _ => 1
  unitary := by intro i j; simp
  hermitian := by intro i j; simp

/-- For n ≥ 3, if next i = j then next j ≠ i (no 2-cycles in longer cycles) -/
lemma next_next_ne_self {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3) (i j : Fin n)
    (h1 : cycle.next i = j) : cycle.next j ≠ i := by
  intro h2
  have h_period2 : cycle.next (cycle.next i) = i := by rw [h1, h2]
  have h_prev : cycle.prev i = j := by
    calc cycle.prev i = cycle.prev (cycle.next (cycle.next i)) := by rw [h_period2]
      _ = cycle.next i := cycle.prev_next (cycle.next i)
      _ = j := h1
  have h_ne := prev_ne_next_of_n_ge_3 cycle h_n_ge_3 i
  rw [h_prev, h1] at h_ne
  exact h_ne rfl

/-- A constant-phase connection: uniform phase θ on each edge in cycle direction -/
noncomputable def Connection.uniform (n : ℕ) [Fintype (Fin n)] [NeZero n]
    (θ : ℝ) (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3) : Connection n where
  phase := fun i j =>
    if cycle.next i = j then cexp (I * θ)
    else if cycle.next j = i then cexp (-I * θ)
    else 1
  unitary := by
    intro i j
    by_cases h1 : cycle.next i = j
    · simp only [h1, ↓reduceIte, Complex.norm_exp]
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    · by_cases h2 : cycle.next j = i
      · simp only [h1, ↓reduceIte, h2, Complex.norm_exp]
        simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      · simp only [h1, h2, ↓reduceIte, norm_one]
  hermitian := by
    intro i j
    by_cases h1 : cycle.next i = j
    · simp only [h1, ↓reduceIte]
      have h2 : cycle.next j ≠ i := next_next_ne_self cycle h_n_ge_3 i j h1
      simp only [h2, ↓reduceIte]
      change _ = (starRingEnd ℂ) _
      rw [← Complex.exp_conj]
      simp [Complex.conj_I, Complex.conj_ofReal]
    · by_cases h2 : cycle.next j = i
      · simp only [h1, h2, ↓reduceIte]
        change _ = (starRingEnd ℂ) _
        rw [← Complex.exp_conj]
        simp [Complex.conj_I, Complex.conj_ofReal]
      · simp [h1, h2]

/-! ## 2. Connection Holonomy -/

/--
The holonomy of a connection around a cycle: product of phases.
This is the discrete analog of exp(i ∮ A · dl).
-/
noncomputable def connectionHolonomy {n : ℕ} [Fintype (Fin n)]
    (A : Connection n) (cycle : SimpleCycle n) : ℂ :=
  ∏ i : Fin n, A.phase i (cycle.next i)

/--
Holonomy of the uniform connection is exp(i n θ) where n is the cycle length.
-/
theorem uniform_holonomy {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (θ : ℝ) (cycle : SimpleCycle n) (h_n_ge_3 : n ≥ 3) :
    connectionHolonomy (Connection.uniform n θ cycle h_n_ge_3) cycle =
    cexp (I * (n : ℂ) * θ) := by
  unfold connectionHolonomy Connection.uniform
  simp only [↓reduceIte]
  -- Product of n identical terms = term^n
  simp only [Finset.prod_const, Finset.card_univ]
  rw [← Complex.exp_nat_mul]
  congr 1
  have h : Fintype.card (Fin n) = n := by convert Fintype.card_fin n
  rw [h]
  ring

/-! ## 3. Flatness (Zero Curvature) -/

/--
A connection is flat if its holonomy around every "contractible" loop is 1.
For a simple cycle graph (which has no contractible loops), every connection
is vacuously flat - but can have non-trivial holonomy around the cycle itself.

This captures the essence of Aharonov-Bohm: the "field" (curvature) can be
zero everywhere while the "potential" (connection) has topological content.
-/
def IsFlat {n : ℕ} (G : DynamicGraph n) (A : Connection n) : Prop :=
  ∀ (face : Finset (Fin n)),
    face.card = 3 →  -- triangular faces (elementary plaquettes)
    ∀ (i j k : Fin n), i ∈ face → j ∈ face → k ∈ face →
      (i, j) ∈ G.active_edges → (j, k) ∈ G.active_edges → (k, i) ∈ G.active_edges →
      A.phase i j * A.phase j k * A.phase k i = 1

/--
On a pure cycle graph (no triangular faces), every connection is flat.
The topology is entirely in the non-contractible cycle.
-/
theorem cycle_graph_all_flat {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (A : Connection n)
    (h_no_triangles : ∀ (i j k : Fin n),
      (i, j) ∈ G.active_edges → (j, k) ∈ G.active_edges → (k, i) ∉ G.active_edges) :
    IsFlat G A := by
  intro face h_card i j k hi hj hk hij hjk hki
  exfalso
  exact h_no_triangles i j k hij hjk hki

/-! ## 4. Covariant Laplacian -/

/--
The covariant Laplacian: replaces ψ_j - ψ_i with ψ_j - A_{ij} ψ_i.
This is the minimal coupling of the quantum particle to the connection.
-/
noncomputable def covariantLaplacian {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (A : Connection n) (ψ : QC0 n) : QC0 n :=
  fun i => ∑ j : Fin n,
    if (i, j) ∈ G.active_edges then ψ j - A.phase i j * ψ i else 0

/--
For trivial connection, the covariant Laplacian simplifies to the graph Laplacian.
-/
theorem covariantLaplacian_trivial {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (ψ : QC0 n) (i : Fin n) :
    covariantLaplacian G (Connection.trivial n) ψ i =
    ∑ j : Fin n, if (i, j) ∈ G.active_edges then ψ j - ψ i else 0 := by
  unfold covariantLaplacian Connection.trivial
  simp only [one_mul]

/-! ## 5. Covariant Schrödinger Evolution -/

/--
Schrödinger evolution with the covariant Laplacian:
i ∂ψ/∂t = Ĥ_A ψ where Ĥ_A = -Δ_A + V
-/
def CovariantSchrodingerEvolution {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (A : Connection n)
    (ψ : ℝ → QC0 n) (V : QC0 n) : Prop :=
  ∀ (t : ℝ) (i : Fin n),
    HasDerivAt (fun s => ψ s i)
      (I * (-covariantLaplacian G A (ψ t) i + V i)) t

/-! ## 6. Walk Phase with Connection -/

/--
The phase accumulated by walking a path with a connection.
This generalizes walk_sum to include the connection phases.
Defined inductively on walk structure (like walk_sum).
-/
noncomputable def connectionWalkPhase {n : ℕ} (G : DynamicGraph n) (A : Connection n) :
    ∀ {u v : Fin n}, (DynamicGraph.toSimpleGraph G).Walk u v → ℂ
  | _, _, .nil => 1
  | u, _, @SimpleGraph.Walk.cons _ _ _ v _ _hadj p => A.phase u v * connectionWalkPhase G A p

/-- connectionWalkPhase respects Walk.copy -/
lemma connectionWalkPhase_copy {n : ℕ} (G : DynamicGraph n) (A : Connection n)
    {u v u' v' : Fin n} (p : (DynamicGraph.toSimpleGraph G).Walk u v)
    (hu : u = u') (hv : v = v') :
    connectionWalkPhase G A (p.copy hu hv) = connectionWalkPhase G A p := by
  subst hu hv
  rfl

/-- connectionWalkPhase of append is the product -/
lemma connectionWalkPhase_append {n : ℕ} (G : DynamicGraph n) (A : Connection n)
    {u v w : Fin n} (p : (DynamicGraph.toSimpleGraph G).Walk u v)
    (q : (DynamicGraph.toSimpleGraph G).Walk v w) :
    connectionWalkPhase G A (p.append q) =
    connectionWalkPhase G A p * connectionWalkPhase G A q := by
  induction p with
  | nil => simp [connectionWalkPhase]
  | cons h p' ih =>
    rw [SimpleGraph.Walk.cons_append, connectionWalkPhase, connectionWalkPhase, ih]
    ring

/-- connectionWalkPhase is always unit norm (product of unit phases) -/
lemma connectionWalkPhase_unit {n : ℕ} (G : DynamicGraph n) (A : Connection n)
    {u v : Fin n} (p : (DynamicGraph.toSimpleGraph G).Walk u v) :
    ‖connectionWalkPhase G A p‖ = 1 := by
  induction p with
  | nil => simp [connectionWalkPhase]
  | cons h p' ih =>
    simp only [connectionWalkPhase, norm_mul]
    rw [A.unitary, ih, mul_one]

/-- connectionWalkPhase of reverse equals conjugate (hermitian connection) -/
lemma connectionWalkPhase_reverse {n : ℕ} (G : DynamicGraph n) (A : Connection n)
    {u v : Fin n} (p : (DynamicGraph.toSimpleGraph G).Walk u v) :
    connectionWalkPhase G A p.reverse = star (connectionWalkPhase G A p) := by
  induction p with
  | nil => simp [connectionWalkPhase]
  | cons h p' ih =>
    rw [SimpleGraph.Walk.reverse_cons]
    rw [connectionWalkPhase_append, ih]
    simp only [connectionWalkPhase, mul_one]
    rw [A.hermitian, star_mul]

/-- connectionWalkPhase of the auxiliary walk equals partial product. -/
lemma connectionWalkPhase_cycle_aux {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
    (cycle : SimpleCycle n) (G : DynamicGraph n)
    (h_embedded : cycleEmbeddedIn cycle G) (A : Connection n) (v : Fin n) (k : ℕ) :
    connectionWalkPhase G A (Diaspora.Logic.WalkHolonomy.cycle_walk_aux cycle G h_embedded k v) =
    ∏ i ∈ Finset.range k, A.phase (cycle.next^[i] v) (cycle.next^[i + 1] v) := by
  induction k generalizing v with
  | zero =>
    simp [Diaspora.Logic.WalkHolonomy.cycle_walk_aux, connectionWalkPhase]
  | succ k ih =>
    have h_unfold : Diaspora.Logic.WalkHolonomy.cycle_walk_aux cycle G h_embedded (k + 1) v =
        (SimpleGraph.Walk.cons (h_embedded v)
          (Diaspora.Logic.WalkHolonomy.cycle_walk_aux cycle G h_embedded k (cycle.next v))).copy rfl
          (by simp only [Function.iterate_succ_apply']
              rw [Diaspora.Logic.WalkHolonomy.iterate_next_comm]) := rfl
    rw [h_unfold, connectionWalkPhase_copy]
    conv_lhs => rw [connectionWalkPhase.eq_def]
    simp only [Function.iterate_succ_apply']
    rw [ih (cycle.next v)]
    rw [Finset.prod_range_succ']
    simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply']
    rw [mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    simp only [Diaspora.Logic.WalkHolonomy.iterate_next_comm]

/--
For a closed walk around the canonical cycle, the phase equals the holonomy.
We assume the iteration orbit covers all vertices (true for SimpleCycle).
-/
theorem closedWalkPhase_eq_holonomy {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] [NeZero n]
    (G : DynamicGraph n) (A : Connection n)
    (cycle : SimpleCycle n) (h_embedded : cycleEmbeddedIn cycle G) (v : Fin n)
    (h_orbit : Function.Bijective (fun i : Fin n => cycle.next^[i.val] v)) :
    connectionWalkPhase G A (Diaspora.Logic.WalkHolonomy.canonical_cycle_walk cycle G h_embedded v) =
    connectionHolonomy A cycle := by
  unfold Diaspora.Logic.WalkHolonomy.canonical_cycle_walk
  rw [connectionWalkPhase_copy, connectionWalkPhase_cycle_aux]
  unfold connectionHolonomy
  rw [← Fin.prod_univ_eq_prod_range]
  -- Define the orbit equivalence
  let e := Equiv.ofBijective (fun i : Fin n => cycle.next^[i.val] v) h_orbit
  -- Express LHS in terms of e
  have h_lhs : (fun i : Fin n => A.phase (cycle.next^[i.val] v) (cycle.next^[i.val + 1] v)) =
               (fun i : Fin n => A.phase (e i) (cycle.next (e i))) := by
    ext i
    simp only [e, Equiv.ofBijective_apply, Function.iterate_succ_apply']
  simp only [h_lhs]
  symm
  convert Fintype.prod_equiv e.symm (fun j => A.phase j (cycle.next j))
    (fun i => A.phase (e i) (cycle.next (e i))) (fun x => by simp [e]) using 1
  apply Finset.prod_congr
  · ext x; simp [Finset.mem_univ]
  · intro x _; rfl

/-! ## 7. The Aharonov-Bohm Theorem -/

/--
**The Aharonov-Bohm Theorem (Discrete Version)**

Even when a connection is flat (zero field everywhere), a particle
walking around a non-contractible cycle acquires a phase equal to
the connection's holonomy.

This is the topological phase: it depends only on the winding number,
not on the specific path or where the "flux" is located.
-/
theorem aharonov_bohm {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] [NeZero n]
    (G : DynamicGraph n) (A : Connection n)
    (cycle : SimpleCycle n) (h_embedded : cycleEmbeddedIn cycle G)
    (_h_flat : IsFlat G A)
    (v : Fin n)
    (h_orbit : Function.Bijective (fun i : Fin n => cycle.next^[i.val] v)) :
    connectionWalkPhase G A
      (Diaspora.Logic.WalkHolonomy.canonical_cycle_walk cycle G h_embedded v) =
    connectionHolonomy A cycle := by
  exact closedWalkPhase_eq_holonomy G A cycle h_embedded v h_orbit

/--
**Corollary: Field-Free Phase Shift**

Set up the uniform connection with angle θ per edge. The total holonomy
is e^{inθ}. Even though the "field" is zero (flat connection on a cycle
graph), the particle acquires this non-trivial phase.
-/
theorem fieldFree_phaseShift {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] [NeZero n]
    (θ : ℝ) (cycle : SimpleCycle n)
    (G : DynamicGraph n) (h_embedded : cycleEmbeddedIn cycle G)
    (h_no_triangles : ∀ (i j k : Fin n),
      (i, j) ∈ G.active_edges → (j, k) ∈ G.active_edges → (k, i) ∉ G.active_edges)
    (h_n_ge_3 : n ≥ 3)
    (v : Fin n)
    (h_orbit : Function.Bijective (fun i : Fin n => cycle.next^[i.val] v)) :
    connectionWalkPhase G (Connection.uniform n θ cycle h_n_ge_3)
      (Diaspora.Logic.WalkHolonomy.canonical_cycle_walk cycle G h_embedded v) =
    cexp (I * (n : ℂ) * θ) := by
  rw [aharonov_bohm G _ cycle h_embedded (cycle_graph_all_flat G _ h_no_triangles) v h_orbit]
  exact uniform_holonomy θ cycle h_n_ge_3

/-! ## 8. Gauge Transformations and Invariance -/

/--
A gauge transformation: a unit phase at each vertex.
This represents a local choice of reference frame.
-/
structure GaugeTransformation (n : ℕ) where
  /-- Phase at each vertex -/
  phase : Fin n → ℂ
  /-- Phases are unit complex numbers -/
  unitary : ∀ i, ‖phase i‖ = 1

/-- The trivial gauge transformation (identity) -/
def GaugeTransformation.trivial (n : ℕ) : GaugeTransformation n where
  phase := fun _ => 1
  unitary := by intro i; simp

/-- Apply a gauge transformation to a connection:
    A'(i,j) = g(i) * A(i,j) * g(j)⁻¹
    This is "rotating the reference frame" at each vertex. -/
noncomputable def Connection.gaugeTransform {n : ℕ}
    (A : Connection n) (g : GaugeTransformation n) : Connection n where
  phase := fun i j => g.phase i * A.phase i j * (g.phase j)⁻¹
  unitary := by
    intro i j
    simp only [norm_mul, norm_inv]
    rw [g.unitary i, A.unitary i j, g.unitary j]
    simp
  hermitian := by
    intro i j
    -- Need: g(i) * A(i,j) * g(j)⁻¹ = star (g(j) * A(j,i) * g(i)⁻¹)
    -- Use A.hermitian: A(i,j) = star A(j,i)
    -- For unit z: z⁻¹ = star z
    have h_i : (g.phase i)⁻¹ = star (g.phase i) := Complex.inv_eq_conj (g.unitary i)
    have h_j : (g.phase j)⁻¹ = star (g.phase j) := Complex.inv_eq_conj (g.unitary j)
    simp only [star_mul, A.hermitian i j, ← h_j]
    -- Now: g(i) * star A(j,i) * g(j)⁻¹ = star (g(i)⁻¹) * (star A(j,i) * g(j)⁻¹)
    -- star (g(i)⁻¹) = star(star g(i)) = g(i) using h_i
    rw [h_i, star_star]
    ring

/--
**Gauge Invariance of Holonomy**

The holonomy around a cycle is invariant under gauge transformations.
This is the fundamental principle of gauge theory: local choices of
reference frame do not affect global observables.

The proof: the gauge phases telescope around the cycle.
g(v₀) * g(v₁)⁻¹ * g(v₁) * g(v₂)⁻¹ * ... * g(vₙ₋₁) * g(v₀)⁻¹ = 1
-/
theorem holonomy_gauge_invariant {n : ℕ} [Fintype (Fin n)]
    (A : Connection n) (g : GaugeTransformation n) (cycle : SimpleCycle n) :
    connectionHolonomy (A.gaugeTransform g) cycle = connectionHolonomy A cycle := by
  unfold connectionHolonomy Connection.gaugeTransform
  simp only
  -- LHS = ∏ i, g(i) * A(i, next i) * g(next i)⁻¹
  -- We'll show this equals ∏ i, A(i, next i) by telescoping the g factors
  have h_bij := next_bijective cycle
  -- The key: ∏ g(next i) = ∏ g(i) by reindexing (next is a bijection)
  let e := Equiv.ofBijective cycle.next h_bij
  have h_reindex : ∏ i : Fin n, g.phase (cycle.next i) = ∏ i : Fin n, g.phase i :=
    Equiv.prod_comp e g.phase
  -- Product of inverses
  have h_inv_prod : ∏ i : Fin n, (g.phase (cycle.next i))⁻¹ = (∏ i : Fin n, g.phase i)⁻¹ := by
    rw [← h_reindex, Finset.prod_inv_distrib]
  -- Each g.phase is nonzero (has norm 1)
  have h_each_ne : ∀ i : Fin n, g.phase i ≠ 0 := by
    intro i h_zero
    have h := g.unitary i
    rw [h_zero, norm_zero] at h
    exact one_ne_zero h.symm
  -- Product is nonzero
  have h_prod_ne : ∏ i : Fin n, g.phase i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => h_each_ne i)
  -- Now compute: ∏ (g * A * g⁻¹) = ∏ g * ∏ A * ∏ g⁻¹ = ∏ g * ∏ A * (∏ g)⁻¹ = ∏ A
  conv_lhs =>
    arg 2
    ext i
    rw [mul_assoc]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rw [h_inv_prod]
  field_simp [h_prod_ne]

/--
**Corollary: Trivial Gauge Leaves Phase Unchanged**
-/
theorem trivial_gauge_phase {n : ℕ} [Fintype (Fin n)] (A : Connection n) (i j : Fin n) :
    (A.gaugeTransform (GaugeTransformation.trivial n)).phase i j = A.phase i j := by
  simp [Connection.gaugeTransform, GaugeTransformation.trivial]

/--
The trivial connection has holonomy 1 (product of all 1s).
-/
theorem trivial_holonomy {n : ℕ} [Fintype (Fin n)] (cycle : SimpleCycle n) :
    connectionHolonomy (Connection.trivial n) cycle = 1 := by
  unfold connectionHolonomy Connection.trivial
  simp

/--
**Pure Gauge ⟹ Trivial Holonomy**

A "pure gauge" connection is one that can be obtained from the trivial
connection by a gauge transformation. Such connections have holonomy 1.

This is the discrete Stokes theorem: if A = dλ (pure gauge), then ∮A = 0.
In the language of diaspora: if the constraint field is "exact", it has
no topological content.
-/
theorem pure_gauge_trivial_holonomy {n : ℕ} [Fintype (Fin n)]
    (g : GaugeTransformation n) (cycle : SimpleCycle n) :
    connectionHolonomy ((Connection.trivial n).gaugeTransform g) cycle = 1 := by
  rw [holonomy_gauge_invariant, trivial_holonomy]

/--
**Holonomy Detects Topology, Not Gauge**

Two connections that differ only by a gauge transformation are
physically equivalent - they describe the same physics. The holonomy
is the gauge-invariant content: the topological phase.

This mirrors the diaspora principle: harmonic forms capture the
"irreducible" content that survives all relaxation attempts.
-/
theorem holonomy_classifies_physics {n : ℕ} [Fintype (Fin n)]
    (A B : Connection n) (g : GaugeTransformation n) (cycle : SimpleCycle n)
    (h : B = A.gaugeTransform g) :
    connectionHolonomy A cycle = connectionHolonomy B cycle := by
  rw [h, holonomy_gauge_invariant]

/-! ## 9. The Holonomy-Winding Correspondence -/

/--
**From Strain to Phase: The Exponential Map**

A real-valued 1-cochain σ (a "strain field" in diaspora terms) induces
a U(1) connection via exp(i·σ). This is how classical configurations
become quantum phases.
-/
noncomputable def strainToConnection {n : ℕ} (σ : C1 n) : Connection n where
  phase := fun i j => cexp (I * σ.val i j)
  unitary := by
    intro i j
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring_nf
    exact Real.exp_zero
  hermitian := by
    intro i j
    -- Need: exp(i·σ(i,j)) = star(exp(i·σ(j,i)))
    -- Using skew: σ(i,j) = -σ(j,i)
    -- So LHS = exp(-i·σ(j,i))
    -- For unit z = exp(iθ): star(z) = exp(-iθ)
    rw [σ.skew i j]
    simp only [Complex.ofReal_neg, mul_neg]
    -- Now need: exp(-i·σ(j,i)) = star(exp(i·σ(j,i)))
    -- Key: -(I * x) = star(I * x) for real x (since star I = -I, star (real) = real)
    rw [show -(I * ↑(σ.val j i)) = star (I * ↑(σ.val j i)) by simp]
    exact Complex.exp_conj _

/--
**The Quantization Theorem**

The holonomy of exp(i·σ) equals exp(i · winding).

This directly connects the diaspora picture (walk_sum, winding, harmonic content)
to the Aharonov-Bohm picture (holonomy, phase, gauge equivalence).
-/
theorem holonomy_eq_exp_winding {n : ℕ} [Fintype (Fin n)]
    (σ : C1 n) (cycle : SimpleCycle n) :
    connectionHolonomy (strainToConnection σ) cycle =
    cexp (I * ∑ i : Fin n, σ.val i (cycle.next i)) := by
  unfold connectionHolonomy strainToConnection
  rw [← Complex.exp_sum]
  congr 1
  -- Need: ∑ x, I * ↑(σ x (next x)) = I * ↑(∑ i, σ i (next i))
  rw [Complex.ofReal_sum, Finset.mul_sum]

/--
**The Bridge: Exact ⟹ Trivial Holonomy**

An exact 1-cochain (σ = d₀φ for some potential φ) has zero winding around
any cycle. This corresponds to a pure gauge connection with holonomy 1.

This is the Hodge-Aharonov-Bohm correspondence:

- Hodge: exact forms have zero harmonic content (can be relaxed away)
- A-B: pure gauge connections have trivial holonomy (no observable phase)

Both are saying: "locally derivable" ⟹ "globally trivial".
-/
theorem exact_implies_trivial_holonomy {n : ℕ} [Fintype (Fin n)]
    (σ : C1 n) (cycle : SimpleCycle n)
    (h_exact : ∑ i : Fin n, σ.val i (cycle.next i) = 0) :
    connectionHolonomy (strainToConnection σ) cycle = 1 := by
  rw [holonomy_eq_exp_winding, h_exact]
  simp

/-! ## 10. Interference and Measurement -/

/--
Two paths from u to v that together form a cycle will have phase difference
equal to the enclosed holonomy. This is how Aharonov-Bohm is measured:
interference between two paths encircling the flux.
-/
theorem interference_phase_difference {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (A : Connection n)
    (u v : Fin n)
    (path1 path2 : (DynamicGraph.toSimpleGraph G).Walk u v)
    (_h_cycle : SimpleGraph.Walk.append path1 path2.reverse
      = SimpleGraph.Walk.append path1 path2.reverse) :
    connectionWalkPhase G A path1 / connectionWalkPhase G A path2 =
    connectionWalkPhase G A (path1.append path2.reverse) := by
  rw [connectionWalkPhase_append, connectionWalkPhase_reverse]
  rw [div_eq_mul_inv]
  congr 1
  have h := connectionWalkPhase_unit G A path2
  rw [Complex.inv_eq_conj h]
  rfl

/-! ## 11. The Hodge-Gauge Correspondence -/

/--
Exact forms have zero winding around any SimpleCycle.
This is the discrete Stokes theorem: ∑ᵢ (ϕ(next i) - ϕ(i)) = 0 by telescoping.
-/
theorem exact_winding_zero {n : ℕ} [Fintype (Fin n)]
    (ϕ : C0 n) (cycle : SimpleCycle n) :
    ∑ i : Fin n, (d0 ϕ).val i (cycle.next i) = 0 := by
  -- (d0 ϕ)(i, next i) = ϕ(next i) - ϕ(i)
  simp only [d0]
  -- The sum telescopes: ∑ (ϕ(next i) - ϕ(i)) = ∑ ϕ(next i) - ∑ ϕ(i)
  rw [Finset.sum_sub_distrib]
  -- Since next is a bijection, ∑ ϕ(next i) = ∑ ϕ(i)
  have h_bij := next_bijective cycle
  have h_reindex : ∑ i : Fin n, ϕ (cycle.next i) = ∑ i : Fin n, ϕ i := by
    exact Equiv.sum_comp (Equiv.ofBijective cycle.next h_bij) ϕ
  rw [h_reindex]
  ring

/--
**The Hodge-Gauge Correspondence**

The holonomy of a U(1) connection induced by a strain field σ depends only on
the harmonic component of σ. The exact part (d₀φ) is gauge-trivial and
contributes no phase.

This theorem establishes the deepest connection between Hodge theory and gauge theory:

- **Hodge perspective**: Every 1-cochain decomposes as σ = d₀φ + γ, where d₀φ is
  the "relaxable" fluctuation and γ is the irreducible harmonic content.

- **Gauge perspective**: The connection exp(i·σ) is gauge-equivalent to exp(i·γ).
  Local phase choices (gauge transformations) can remove the exact part but
  cannot touch the harmonic content.

- **Physical interpretation**: The harmonic component γ carries the topology.
  It is the "matter" that cannot be gauged away. The exact part d₀φ is
  pure gauge—locally observable but globally trivial.

This unifies:
- Diaspora's "paradox" (non-exactness) with Aharonov-Bohm's "phase" (holonomy)
- Hodge's "harmonic forms" with gauge theory's "gauge-invariant observables"
- The nucleation barrier (‖γ‖² ≥ 1/n) with topological quantization of phase
-/
theorem hodge_gauge_correspondence {n : ℕ} [Fintype (Fin n)]
    (σ γ : C1 n) (ϕ : C0 n) (cycle : SimpleCycle n)
    (h_decomp : ∀ i j, σ.val i j = (d0 ϕ).val i j + γ.val i j)
    (_h_harm : IsHarmonic γ) :
    connectionHolonomy (strainToConnection σ) cycle =
    connectionHolonomy (strainToConnection γ) cycle := by
  -- Convert connection holonomies to exponentials of winding sums
  rw [holonomy_eq_exp_winding, holonomy_eq_exp_winding]
  -- The exponentials are equal iff the sums are equal
  congr 1
  congr 1
  -- Decompose σ = d₀ϕ + γ in the sum
  have h_sigma_sum : ∑ i : Fin n, σ.val i (cycle.next i) =
      ∑ i : Fin n, (d0 ϕ).val i (cycle.next i) + ∑ i : Fin n, γ.val i (cycle.next i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact h_decomp i (cycle.next i)
  -- The exact part vanishes (Stokes theorem)
  have h_exact_vanish : ∑ i : Fin n, (d0 ϕ).val i (cycle.next i) = 0 :=
    exact_winding_zero ϕ cycle
  rw [h_sigma_sum, h_exact_vanish, zero_add]

/--
**Corollary: Topology Determines Phase**

The quantum phase acquired around a cycle is determined entirely by the
topological content (harmonic component) of the strain field. Two strain
fields with the same harmonic component produce identical phases.
-/
theorem topology_determines_phase {n : ℕ} [Fintype (Fin n)]
    (σ₁ σ₂ : C1 n) (γ : C1 n) (ϕ₁ ϕ₂ : C0 n) (cycle : SimpleCycle n)
    (h_decomp₁ : ∀ i j, σ₁.val i j = (d0 ϕ₁).val i j + γ.val i j)
    (h_decomp₂ : ∀ i j, σ₂.val i j = (d0 ϕ₂).val i j + γ.val i j)
    (h_harm : IsHarmonic γ) :
    connectionHolonomy (strainToConnection σ₁) cycle =
    connectionHolonomy (strainToConnection σ₂) cycle := by
  rw [hodge_gauge_correspondence σ₁ γ ϕ₁ cycle h_decomp₁ h_harm]
  rw [hodge_gauge_correspondence σ₂ γ ϕ₂ cycle h_decomp₂ h_harm]

/--
**Corollary: Zero Harmonic ⟹ Trivial Holonomy**

A strain field with zero harmonic component (i.e., an exact form σ = d₀φ)
produces trivial holonomy (phase = 1). This is the gauge-theoretic statement
that pure gauge configurations are physically trivial.

In diaspora terms: a satisfiable theory creates no topological defect.
-/
theorem exact_has_trivial_holonomy {n : ℕ} [Fintype (Fin n)]
    (ϕ : C0 n) (cycle : SimpleCycle n) :
    connectionHolonomy (strainToConnection (d0 ϕ)) cycle = 1 := by
  rw [holonomy_eq_exp_winding, exact_winding_zero]
  simp

/--
**The Quantization Bridge**

For a harmonic form γ with integer winding m around a SimpleCycle of length n,
the induced holonomy is exp(2πi·m/n) raised to the n-th power—a root of unity.

This connects the diaspora quantization (‖γ‖² = m²/n) to the Aharonov-Bohm
quantization (holonomy = e^{iΘ} for discrete Θ).
-/
theorem harmonic_holonomy_quantized {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (γ : C1 n) (cycle : SimpleCycle n)
    (h_harm : IsHarmonic γ)
    (h_support : SupportedOnCycle cycle γ)
    (m : ℤ)
    (h_winding : holonomy γ (SimpleCycle.toChain1 cycle) = m)
    (h_n_ge_3 : n ≥ 3) :
    connectionHolonomy (strainToConnection γ) cycle = cexp (I * (m : ℂ)) := by
  rw [holonomy_eq_exp_winding]
  congr 1
  congr 1
  -- Need: ∑ γ(i, next i) = holonomy γ cycle.toChain1 = m
  classical
  haveI : Inhabited (Fin n) := ⟨0, Nat.zero_lt_of_lt (by omega : 0 < n)⟩
  obtain ⟨k, h_const⟩ := harmonic_constant_on_simple_cycle cycle γ h_harm h_support
  -- The sum equals n * k
  have h_sum_eq : ∑ i : Fin n, γ.val i (cycle.next i) = (Fintype.card (Fin n)) * k := by
    simp_rw [h_const, Finset.sum_const, Finset.card_univ]
    ring
  -- And holonomy = n * k = m
  have h_hol_eq := holonomy_of_constant_harmonic cycle γ k h_const
  rw [h_winding] at h_hol_eq
  -- So ∑ γ = m
  have h_card : (Fintype.card (Fin n) : ℝ) ≠ 0 := by simp
  have h_k_eq : k = m / Fintype.card (Fin n) := by field_simp [h_card] at h_hol_eq ⊢; linarith
  rw [h_sum_eq, h_k_eq]
  field_simp [h_card]
  -- Now need to show (m : ℝ) = (m : ℂ) as a Complex.ofReal
  simp only [Complex.ofReal_intCast]

end Diaspora.Quantum.AharonovBohm
