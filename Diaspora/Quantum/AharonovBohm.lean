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

/-! ## 8. Interference and Measurement -/

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

end Diaspora.Quantum.AharonovBohm
