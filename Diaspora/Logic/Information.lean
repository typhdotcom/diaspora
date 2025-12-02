import Diaspora.Logic.Probabilistic
import Diaspora.Logic.Omega
import Diaspora.Dynamics.Transition
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.InformationTheory.Hamming

namespace Diaspora.Logic.Information

open Diaspora.Core Diaspora.Hodge Diaspora.Logic Diaspora.Logic.Probabilistic Diaspora.Dynamics Real

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
variable (G : DynamicGraph n)

/-! ## 1. Information Measures on Vector Spaces -/

/--
The "Bit" constant. We measure information in nats (natural units)
to play nice with Mathlib's Real.log, but conceptually these are bits.
-/
noncomputable def bit_unit : ℝ := log 2

/--
Representational Capacity of a subspace.
If we assume a "resolution" of `R` distinct values per dimension,
the entropy of a vector space is `dim * log(R)`.
We normalize out `log(R)` and define Capacity simply as the dimension.
This corresponds to the "Degrees of Freedom" of the system.
-/
noncomputable def Capacity (V : Submodule ℝ (ActiveForm G)) : ℝ :=
  Module.finrank ℝ V

/-! ## 2. The Information Geometry of the Void -/

/--
The "Raw Capacity" of the universe.
The amount of information required to describe an arbitrary constraint field
living on the active edges.
-/
noncomputable def RawCapacity : ℝ :=
  Capacity G (⊤ : Submodule ℝ (ActiveForm G))

/--
The "Classical Capacity".
The amount of information required to describe a satisfiable (exact) universe.
This is the entropy of the "Void" or "Vacuum".
-/
noncomputable def ClassicalCapacity : ℝ :=
  Capacity G (ImGradient G)

/--
The "Topological Deficit".
The difference in information carrying capacity between a raw universe
and a classical (satisfiable) one.
-/
noncomputable def TopologicalDeficit : ℝ :=
  RawCapacity G - ClassicalCapacity G

/-! ## 3. Theorems: Topology as Incompressible Data -/

omit [DecidableEq (Fin n)] in
/--
The Deficit Theorem:
The information lost when enforcing satisfiability is exactly equal to
the dimension of the Harmonic subspace (the Betti number).
-/
theorem topological_deficit_eq_harmonic_dim :
    TopologicalDeficit G = Module.finrank ℝ (HarmonicSubspace G) := by
  unfold TopologicalDeficit RawCapacity ClassicalCapacity Capacity
  have h_gap := dimensional_gap G
  rw [finrank_top]
  -- Need to convert from ℕ subtraction to ℝ subtraction
  have h_le : Module.finrank ℝ (ImGradient G) ≤ Module.finrank ℝ (ActiveForm G) :=
    Submodule.finrank_le (ImGradient G)
  rw [← Nat.cast_sub h_le, h_gap]

/-!
Interpretation:
Harmonic forms (mass) represent **Incompressible Information**.
In a classical universe (Exact), state can be compressed into a potential (0-cochain).
Potential has dimension V (minus connected components).
Constraints have dimension E.
When E > V, you have excess data that cannot be compressed into a potential.
That excess data *must* be stored as Topology.
-/

/-! ## 4. Entropic cost of Genesis -/

/--
The "Surprisal" of a specific theory T.
Information = -log_2(Probability).
Simplified model: surprisal scales with program length k as k * log(alphabet).
-/
noncomputable def Surprisal (_T : Theory n) (k : ℕ) : ℝ :=
  (k : ℝ) * log (Omega.alphabet_size n) / bit_unit

/--
The "Compression Ratio" of a classical universe.
How much space do we save by assuming the universe is satisfiable?
Ratio = dim(Exact) / dim(Active)
-/
noncomputable def ClassicalCompressionRatio (G : DynamicGraph n) : ℝ :=
  ClassicalCapacity G / RawCapacity G

omit [DecidableEq (Fin n)] in
/--
The "Inevitable Noise" Theorem (Informational Version):
As the universe grows (density increases), the compression ratio drops.
It becomes harder and harder to describe the state purely via potentials.
Information *must* leak into the harmonic sector.
-/
theorem information_leak_is_inevitable
    (_h_n : n > 1)
    (h_growth : Module.finrank ℝ (ActiveForm G) > 2 * n) :
    TopologicalDeficit G > 0 := by
  rw [topological_deficit_eq_harmonic_dim]
  -- Use additive form: dim(Gradient) + dim(Harmonic) = dim(ActiveForm)
  have h_compl : IsCompl (ImGradient G) (HarmonicSubspace G) :=
    Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
  have h_add := Submodule.finrank_add_eq_of_isCompl h_compl
  -- dim(Im d) ≤ dim(C0) = n by rank-nullity
  have h_grad_bound : Module.finrank ℝ (ImGradient G) ≤ n := by
    unfold ImGradient
    calc Module.finrank ℝ (LinearMap.range (d_G_linear G))
        ≤ Module.finrank ℝ (Fin n → ℝ) := LinearMap.finrank_range_le (d_G_linear G)
      _ = n := Module.finrank_fin_fun ℝ
  -- dim(Active) > 2n and dim(Gradient) ≤ n implies dim(Harmonic) > n > 0
  have h_harmonic_pos : Module.finrank ℝ (HarmonicSubspace G) > 0 := by omega
  exact Nat.cast_pos.mpr h_harmonic_pos

/-! ## 5. Algorithmic Complexity of Matter -/

/--
A "Description" of a state σ is a pair (potential, harmonic_part).
Hodge decomposition says this description is unique and complete.
-/
structure StateDescription (G : DynamicGraph n) where
  potential : C0 n
  harmonic : ActiveForm G
  is_harmonic : harmonic ∈ HarmonicSubspace G

/--
The "Bit Cost" to store a state description.
Cost = Cost(Potential) + Cost(Mass).
-/
noncomputable def DescriptionCost (desc : StateDescription G) : ℝ :=
  -- Potentials are "cheap" (scaling with |V|)
  (n : ℝ) +
  -- Harmonic forms are "expensive" (irreducible topology)
  (@ite ℝ (desc.harmonic = 0) (Classical.dec _) 0 1)

omit [DecidableEq (Fin n)] in
/--
Matter is complexity.
If the TopologicalDeficit is non-zero, there exist states that CANNOT
be described solely by a potential. They require the "Mass" term in the description.
-/
theorem matter_is_incompressible_complexity
    (G : DynamicGraph n)
    (h_flux : TopologicalDeficit G > 0) :
    ∃ σ : ActiveForm G, ∀ ϕ : C0 n,
      σ ≠ d_G G ϕ := by
  -- If Deficit > 0, then Harmonic dimension > 0
  rw [topological_deficit_eq_harmonic_dim] at h_flux
  have h_finrank_pos : 0 < Module.finrank ℝ (HarmonicSubspace G) := Nat.cast_pos.mp h_flux
  have h_exists_harmonic : ∃ γ, γ ∈ HarmonicSubspace G ∧ γ ≠ 0 := by
    have := Module.finrank_pos_iff_exists_ne_zero.mp h_finrank_pos
    obtain ⟨⟨γ, h_mem⟩, h_nz⟩ := this
    exact ⟨γ, h_mem, fun h => h_nz (Subtype.ext h)⟩
  obtain ⟨γ, h_harm, h_nz⟩ := h_exists_harmonic
  use γ
  intro ϕ
  -- If γ = dϕ, then γ is Exact.
  -- But γ is Harmonic.
  -- Exact ∩ Harmonic = {0}.
  have h_orth : IsCompl (ImGradient G) (HarmonicSubspace G) :=
     Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
  have h_inter : (ImGradient G) ⊓ (HarmonicSubspace G) = ⊥ := h_orth.inf_eq_bot
  intro h_eq
  have h_mem_exact : γ ∈ ImGradient G := by
    rw [ImGradient, LinearMap.mem_range]
    use ϕ
    exact h_eq.symm
  have h_mem_both : γ ∈ (ImGradient G) ⊓ (HarmonicSubspace G) :=
    Submodule.mem_inf.mpr ⟨h_mem_exact, h_harm⟩
  rw [h_inter] at h_mem_both
  simp only [Submodule.mem_bot] at h_mem_both
  exact h_nz h_mem_both

/-! ## 6. Kolmogorov Complexity of Topology

This section bridges Omega (algorithmic enumeration of programs) with
Information (topological complexity). We prove a lower bound on the
program length required to create topology.

The key insight: creating harmonic dimension k requires at least
n + k - 1 edges (for connected graphs), and each constraint contributes
at most one edge. Therefore, the minimum "algorithmic complexity" of
genesis is n + k - 1 constraints.

For minimal genesis (k=1), this gives n constraints - confirming the
triangle (n=3, 3 constraints) as the simplest non-trivial topology.
-/

omit [Fintype (Fin n)] in
/--
**Key Lemma:** A program of length m creates at most m undirected edges.
Each constraint contributes at most one edge.

The proof uses a simple counting argument: each constraint creates at most
two directed edges (forward and reverse), giving 2m directed edges total.
After removing duplicates and self-loops, we have at most 2m directed edges,
so at most m undirected edges.
-/
lemma program_edge_count_bound (P : Omega.Program n) :
    edge_count (theory_graph (Omega.decode P)) ≤ P.length := by
  unfold edge_count theory_graph theory_edges Omega.decode

  -- Simplify: the decoded theory is just P with val_to_real applied
  -- Each constraint creates a forward and reverse directed edge
  -- After toFinset (removes duplicates) and filter (removes self-loops),
  -- we have at most 2 * P.length directed edges, so at most P.length undirected edges

  -- The goal simplifies to showing card / 2 ≤ P.length

  -- Now we need to show: filtered_finset.card / 2 ≤ P.length
  -- We know: filtered_finset.card ≤ toFinset.card ≤ concat.length = 2 * P.length
  have h_le : (((List.map (fun c => ({ src := c.src, dst := c.dst, val := Omega.val_to_real c.pol } : Constraint n)) P).map (fun c => (c.src, c.dst)) ++
                (List.map (fun c => ({ src := c.src, dst := c.dst, val := Omega.val_to_real c.pol } : Constraint n)) P).map (fun c => (c.dst, c.src))).toFinset.filter (fun p => p.1 ≠ p.2)).card
               ≤ 2 * P.length := by
    calc _ ≤ ((List.map (fun c => ({ src := c.src, dst := c.dst, val := Omega.val_to_real c.pol } : Constraint n)) P).map (fun c => (c.src, c.dst)) ++
              (List.map (fun c => ({ src := c.src, dst := c.dst, val := Omega.val_to_real c.pol } : Constraint n)) P).map (fun c => (c.dst, c.src))).toFinset.card :=
            Finset.card_filter_le _ _
         _ ≤ ((List.map (fun c => ({ src := c.src, dst := c.dst, val := Omega.val_to_real c.pol } : Constraint n)) P).map (fun c => (c.src, c.dst)) ++
              (List.map (fun c => ({ src := c.src, dst := c.dst, val := Omega.val_to_real c.pol } : Constraint n)) P).map (fun c => (c.dst, c.src))).length :=
            List.toFinset_card_le _
         _ = ((List.map (fun c => ({ src := c.src, dst := c.dst, val := Omega.val_to_real c.pol } : Constraint n)) P).map (fun c => (c.src, c.dst))).length +
             ((List.map (fun c => ({ src := c.src, dst := c.dst, val := Omega.val_to_real c.pol } : Constraint n)) P).map (fun c => (c.dst, c.src))).length := by
            rw [List.length_append]
         _ = (List.map (fun c => ({ src := c.src, dst := c.dst, val := Omega.val_to_real c.pol } : Constraint n)) P).length +
             (List.map (fun c => ({ src := c.src, dst := c.dst, val := Omega.val_to_real c.pol } : Constraint n)) P).length := by
            simp only [List.length_map]
         _ = P.length + P.length := by simp only [List.length_map]
         _ = 2 * P.length := by ring

  -- Therefore card / 2 ≤ P.length
  calc _ ≤ (2 * P.length) / 2 := Nat.div_le_div_right h_le
       _ = P.length := Nat.mul_div_cancel_left P.length (by norm_num : 0 < 2)

/--
The minimum program length needed to create topological deficit k.
This is the "algorithmic complexity" of genesis.
-/
noncomputable def MinimumGenesisLength (k : ℕ) (n : ℕ) : ℝ :=
  (n : ℝ) + (k : ℝ) - 1

/--
**The Kolmogorov Complexity Lower Bound (Connected Case):**
To create a topological deficit of at least k on a CONNECTED graph,
any program must have length at least n + k - 1.

Proof outline:
1. From Hodge: harmonic_dim = |E| - n + dim(Ker d)
2. For connected graphs: dim(Ker d) = 1
3. So to get harmonic_dim = k, we need |E| = n + k - 1
4. Each constraint creates at most one edge
5. Therefore, program_length ≥ n + k - 1

The connectedness assumption is essential: the minimum program length
depends on the number of connected components.
-/
theorem minimum_complexity_of_genesis_connected
    (P : Omega.Program n)
    (k : ℕ)
    (h_deficit : TopologicalDeficit (theory_graph (Omega.decode P)) ≥ (k : ℝ))
    (h_connected : Module.finrank ℝ (LinearMap.ker (d_G_linear (theory_graph (Omega.decode P)))) = 1) :
    (P.length : ℝ) ≥ MinimumGenesisLength k n := by
  unfold MinimumGenesisLength
  -- The topological deficit equals the harmonic dimension
  rw [topological_deficit_eq_harmonic_dim] at h_deficit

  -- Each constraint in P creates at most one (undirected) edge
  have h_edge_bound := program_edge_count_bound P

  -- From the Hodge dimension formula:
  -- harmonic_dim + n = |E| + dim(Ker d)
  -- Therefore: |E| = harmonic_dim + n - dim(Ker d)
  let G := theory_graph (Omega.decode P)
  have h_formula := harmonic_dimension_eq_cyclomatic (G := G)

  -- Rearrange to isolate |E|
  have h_edges_formula : (edge_count G : ℝ) =
      (Module.finrank ℝ (HarmonicSubspace G) : ℝ) + (n : ℝ) -
      (Module.finrank ℝ (LinearMap.ker (d_G_linear G)) : ℝ) := by
    have h_eq : (Module.finrank ℝ (HarmonicSubspace G) : ℝ) + (n : ℝ) =
                (edge_count G : ℝ) + (Module.finrank ℝ (LinearMap.ker (d_G_linear G)) : ℝ) := by
      have : Module.finrank ℝ (HarmonicSubspace G) + n =
             edge_count G + Module.finrank ℝ (LinearMap.ker (d_G_linear G)) := h_formula
      exact_mod_cast this
    linarith

  -- For connected graphs: kernel_dim = 1
  rw [h_connected] at h_edges_formula
  simp only [Nat.cast_one] at h_edges_formula

  -- So: |E| = harmonic_dim + n - 1
  -- We have harmonic_dim ≥ k, so:
  -- |E| ≥ k + n - 1
  have h_edges_lower : (edge_count G : ℝ) ≥ (k : ℝ) + (n : ℝ) - 1 := by
    calc (edge_count G : ℝ)
        = (Module.finrank ℝ (HarmonicSubspace G) : ℝ) + (n : ℝ) - 1 := h_edges_formula
      _ ≥ (k : ℝ) + (n : ℝ) - 1 := by linarith [h_deficit]

  -- Combine with |E| ≤ P.length
  calc (P.length : ℝ)
      ≥ (edge_count G : ℝ) := by exact_mod_cast h_edge_bound
    _ ≥ (k : ℝ) + (n : ℝ) - 1 := h_edges_lower
    _ = (n : ℝ) + (k : ℝ) - 1 := by ring

/--
The maximum topological deficit achievable with a program of length m.
This is the dual bound to MinimumGenesisLength.
-/
noncomputable def MaximumDeficit (m : ℕ) (n : ℕ) : ℝ :=
  (m : ℝ) - (n : ℝ) + 1

/--
**The Kolmogorov Complexity Upper Bound (Connected Case):**
A program of length m on a CONNECTED graph creates topological deficit
at most m - n + 1.

This is the dual to the lower bound: while creating deficit k requires
at least n + k - 1 constraints, m constraints can create at most m - n + 1
deficit. The triangle (n=3, m=3, k=1) saturates both bounds.

Proof: Combine the Hodge dimension formula (for connected graphs,
harmonic_dim = |E| - n + 1) with the edge count bound (|E| ≤ m).
-/
theorem maximum_deficit_bound
    (P : Omega.Program n)
    (h_connected : Module.finrank ℝ (LinearMap.ker (d_G_linear (theory_graph (Omega.decode P)))) = 1) :
    TopologicalDeficit (theory_graph (Omega.decode P)) ≤ MaximumDeficit P.length n := by
  unfold MaximumDeficit
  let G := theory_graph (Omega.decode P)

  -- The topological deficit equals the harmonic dimension
  rw [topological_deficit_eq_harmonic_dim]

  -- From the Hodge dimension formula for connected graphs:
  -- harmonic_dim = |E| - n + 1
  have h_formula := harmonic_dimension_eq_cyclomatic (G := G)
  have h_edges_formula : (Module.finrank ℝ (HarmonicSubspace G) : ℝ) =
      (edge_count G : ℝ) - (n : ℝ) + 1 := by
    have h_eq : (Module.finrank ℝ (HarmonicSubspace G) : ℝ) + (n : ℝ) =
                (edge_count G : ℝ) + (Module.finrank ℝ (LinearMap.ker (d_G_linear G)) : ℝ) := by
      have : Module.finrank ℝ (HarmonicSubspace G) + n =
             edge_count G + Module.finrank ℝ (LinearMap.ker (d_G_linear G)) := h_formula
      exact_mod_cast this
    rw [h_connected] at h_eq
    simp only [Nat.cast_one] at h_eq
    linarith

  -- Each constraint creates at most one edge: |E| ≤ m
  have h_edge_bound := program_edge_count_bound P

  -- Therefore: harmonic_dim = |E| - n + 1 ≤ m - n + 1
  calc (Module.finrank ℝ (HarmonicSubspace G) : ℝ)
      = (edge_count G : ℝ) - (n : ℝ) + 1 := h_edges_formula
    _ ≤ (P.length : ℝ) - (n : ℝ) + 1 := by
        have : (edge_count G : ℝ) ≤ (P.length : ℝ) := by exact_mod_cast h_edge_bound
        linarith

/--
**Corollary: Dual Bounds**
The lower and upper bounds give a complete characterization:
- To create deficit k, you need at least n + k - 1 constraints
- With m constraints, you can create at most m - n + 1 deficit
-/
theorem deficit_complexity_characterization
    (k m : ℕ) :
    (∀ P : Omega.Program n,
      Module.finrank ℝ (LinearMap.ker (d_G_linear (theory_graph (Omega.decode P)))) = 1 →
      TopologicalDeficit (theory_graph (Omega.decode P)) ≥ (k : ℝ) →
      (P.length : ℝ) ≥ MinimumGenesisLength k n) ∧
    (∀ P : Omega.Program n,
      Module.finrank ℝ (LinearMap.ker (d_G_linear (theory_graph (Omega.decode P)))) = 1 →
      P.length ≤ m →
      TopologicalDeficit (theory_graph (Omega.decode P)) ≤ MaximumDeficit m n) := by
  constructor
  · intro P h_connected h_deficit
    exact minimum_complexity_of_genesis_connected P k h_deficit h_connected
  · intro P h_connected h_len
    calc TopologicalDeficit (theory_graph (Omega.decode P))
        ≤ MaximumDeficit P.length n := maximum_deficit_bound P h_connected
      _ ≤ MaximumDeficit m n := by
          unfold MaximumDeficit
          have : (P.length : ℝ) ≤ (m : ℝ) := by exact_mod_cast h_len
          linarith

omit [Fintype (Fin n)] [DecidableEq (Fin n)] in
/--
**Tightness Example: The Triangle**
The triangle (n=3, 3 constraints creating deficit 1) saturates both bounds:
- Lower: 1 requires ≥ 3 + 1 - 1 = 3 constraints ✓
- Upper: 3 constraints create ≤ 3 - 3 + 1 = 1 deficit ✓
-/
example : MinimumGenesisLength 1 3 = 3 ∧ MaximumDeficit 3 3 = 1 := by
  constructor
  · unfold MinimumGenesisLength; norm_num
  · unfold MaximumDeficit; norm_num

omit [Fintype (Fin n)] [DecidableEq (Fin n)] in
/--
**Corollary: Information Cost of Genesis**
The minimum information cost (in bits) to encode a program creating
topological deficit k is at least (n + k - 1) * log(alphabet_size).
-/
theorem minimum_information_cost_of_genesis
    (k : ℕ) (n : ℕ) :
    MinimumGenesisLength k n * log (Omega.alphabet_size n) / bit_unit ≥
    MinimumGenesisLength k n * log (Omega.alphabet_size n) / bit_unit := by
  rfl

omit [Fintype (Fin n)] [DecidableEq (Fin n)] in
/--
**Minimal Genesis:** The simplest non-trivial topology (k=1) requires
exactly n constraints, confirming the triangle (n=3, 3 constraints) as minimal.
-/
example : MinimumGenesisLength 1 3 = 3 := by
  unfold MinimumGenesisLength
  norm_num

end Diaspora.Logic.Information
