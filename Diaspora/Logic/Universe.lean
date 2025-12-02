import Diaspora.Logic.Theory
import Diaspora.Logic.Information
import Diaspora.Hodge.Decomposition
import Diaspora.Hodge.Harmonic
import Diaspora.Dynamics.Strain
import Diaspora.Dynamics.Transition

namespace Diaspora.Logic

open Diaspora.Core Diaspora.Hodge Diaspora.Logic Diaspora.Logic.Information Diaspora.Dynamics

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-! # The Unified Theory of Diaspora

This file demonstrates the "Grand Unification" of the project.
It proves that in this universe, **Matter is not a primitive.**

Matter is the physical symptom of a logical contradiction.
Gravity (Strain) is the system's attempt to resolve that contradiction.
-/

/--
A `Universe` is a bundle of:
1. A Logic (Constraints)
2. A Geometry (Graph)
3. A State (Potential)
-/
structure Universe (n : ℕ) where
  -- The Logic Layer
  T : Theory n
  consistent : LocallyConsistent T

  -- The Physical Layer (The State)
  ϕ : C0 n

-- The Geometry Layer (Derived from Logic)
def Universe.G (U : Universe n) : DynamicGraph n := theory_graph U.T
noncomputable def Universe.σ (U : Universe n) : ActiveForm U.G := realize U.T

/-! ## 1. The Logical Origin (Inconsistency) -/

/--
We start with a "Paradox": A set of constraints that are locally valid
but globally impossible.
-/
def IsParadox (U : Universe n) : Prop :=
  ¬ Satisfiable U.T

/-! ## 2. The Informational Consequence (Deficit) -/

/--
Theorem: Paradox creates an Information Deficit.
If the universe contains a paradox, it forces the geometry to contain
incompressible data (Topological Deficit > 0).
-/
theorem paradox_implies_deficit
    (U : Universe n)
    (h_paradox : IsParadox U) :
    TopologicalDeficit U.G > 0 := by
  -- 1. Paradox implies non-trivial Harmonic Subspace
  have h_topo := inconsistency_implies_topology U.T U.consistent h_paradox
  obtain ⟨γ, h_gamma_mem, h_gamma_nz⟩ := h_topo

  -- 2. Non-trivial Harmonic Subspace implies Positive Dimension
  have h_dim_pos : Module.finrank ℝ (HarmonicSubspace U.G) > 0 := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    use ⟨γ, h_gamma_mem⟩
    intro h_eq_zero
    apply h_gamma_nz
    exact Subtype.ext_iff.mp h_eq_zero

  -- 3. Dimension equals Information Deficit
  rw [topological_deficit_eq_harmonic_dim]
  exact Nat.cast_pos.mpr h_dim_pos

/-! ## 3. The Physical Manifestation (Mass) -/

/--
"Matter" is the harmonic component of the constraint field.
It is the error term that remains after the potential ϕ has done its best.
-/
noncomputable def matter_content (U : Universe n) : ActiveForm U.G :=
  (hodge_decomposition_graph U.G U.σ).choose_spec.choose

/--
Theorem: Paradox creates Matter.
If the universe is a paradox, the matter content is non-zero.
-/
theorem paradox_creates_mass
    (U : Universe n)
    (h_paradox : IsParadox U) :
    matter_content U ≠ 0 := by
  -- Unfold the definition of matter_content
  unfold matter_content

  -- Extract the Hodge decomposition: σ = dφ + γ
  let φ := (hodge_decomposition_graph U.G U.σ).choose
  let γ := (hodge_decomposition_graph U.G U.σ).choose_spec.choose
  have h_decomp := (hodge_decomposition_graph U.G U.σ).choose_spec.choose_spec.left
  have h_harmonic := (hodge_decomposition_graph U.G U.σ).choose_spec.choose_spec.right.left

  -- Proof by contradiction
  by_contra h_no_mass

  -- If γ = 0, then σ = dφ (exact form)
  have h_exact : U.σ ∈ ImGradient U.G := by
    rw [ImGradient, LinearMap.mem_range]
    use φ
    show d_G_linear U.G φ = U.σ
    simp only [d_G_linear, LinearMap.coe_mk, AddHom.coe_mk]
    rw [h_decomp, h_no_mass, add_zero]

  -- If σ is exact, T is satisfiable (The Bridge Theorem)
  have h_sat := (satisfiable_iff_exact_on_graph U.T U.consistent).mpr h_exact
  exact h_paradox h_sat

/-! ## 4. The Dynamical Consequence (Gravity/Strain) -/

/--
"Strain" is the local tension on edges caused by the failure to satisfy constraints.
This is the "Energy" of the system.
-/
noncomputable def total_strain_energy (U : Universe n) : ℝ :=
  dynamic_strain_energy U.G U.ϕ U.σ.val

/--
Theorem: Matter creates Gravity.
If there is matter (paradox), there *must* be strain in the system,
no matter how we tune the potential ϕ. The paradox exerts a physical force.

Physical interpretation: The harmonic component γ represents "irreducible frustration"
that cannot be relaxed away. Even at the optimal potential (minimum energy state),
the system must carry strain energy ‖γ‖² > 0.
-/
theorem matter_creates_gravity
    (U : Universe n)
    (h_paradox : IsParadox U) :
    total_strain_energy U > 0 := by
  unfold total_strain_energy

  -- Extract the matter content (harmonic component) and optimal potential from Hodge decomposition
  let φ_opt := (hodge_decomposition_graph U.G U.σ).choose
  let γ := matter_content U
  have h_decomp := (hodge_decomposition_graph U.G U.σ).choose_spec.choose_spec.left
  have h_harmonic := (hodge_decomposition_graph U.G U.σ).choose_spec.choose_spec.right.left
  have h_mass := paradox_creates_mass U h_paradox

  -- Apply the irreducible strain theorem:
  -- Since γ ≠ 0, there exists E_min > 0 such that energy ≥ E_min for all ϕ
  -- In particular, energy at U.ϕ ≥ E_min > 0
  have h_floor := harmonic_component_gives_energy_floor U.G U.σ φ_opt γ h_decomp h_harmonic h_mass
  obtain ⟨E_min, h_pos, h_bound⟩ := h_floor
  calc total_strain_energy U
    _ = dynamic_strain_energy U.G U.ϕ U.σ.val := rfl
    _ ≥ E_min := h_bound U.ϕ
    _ > 0 := h_pos

/-! ## 5. The Grand Unification -/

/--
**The Diaspora Correspondence**

This theorem summarizes the entire project.
It traces the causal chain from Logical Contradiction to Physical Strain.

1. **Logic:** A contradiction exists (`IsParadox`).
2. **Information:** This forces an information deficit (`TopologicalDeficit`).
3. **Topology:** This deficit manifests as a non-trivial Betti number.
4. **Mass:** This topology traps a non-zero harmonic form (`matter_content`).
5. **Gravity:** This mass generates irreducible strain (`total_strain_energy`).

We are living in the stress fracture of a logical inconsistency.
-/
theorem the_diaspora_correspondence
    (U : Universe n) :
    IsParadox U →
    (TopologicalDeficit U.G > 0) ∧
    (matter_content U ≠ 0) ∧
    (total_strain_energy U > 0) := by
  intro h_paradox
  constructor
  · exact paradox_implies_deficit U h_paradox
  · constructor
    · exact paradox_creates_mass U h_paradox
    · exact matter_creates_gravity U h_paradox

end Diaspora.Logic
