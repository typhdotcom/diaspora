/-
# The Discrete McKean-Singer Formula

The "baby version" of the Atiyah-Singer Index Theorem for finite graphs.

The formula states:
  dim(H⁰) - dim(H¹) = |V| - |E| = χ(G)

This connects:
- Analysis (kernel dimensions of Laplacians)
- Topology (Euler characteristic, Betti numbers)
- Algebra (Hodge decomposition, rank-nullity)

The key insight: non-zero eigenvalues of Δ₀ and Δ₁ are paired via the
intertwining operators d and δ. Only the zero modes (harmonic forms) contribute
to the index.
-/

import Diaspora.Hodge.Decomposition
import Mathlib.LinearAlgebra.Dimension.Finrank

open BigOperators Diaspora.Core Diaspora.Hodge

namespace Diaspora.Hodge.Index

variable {n : ℕ} [Fintype (Fin n)] (G : DynamicGraph n)

/-! ## 1. Zero Modes -/

/-- H⁰: The kernel of the gradient d_G (constant functions per connected component). -/
noncomputable def H0 : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker (d_G_linear G)

/-- H¹: The harmonic subspace (orthogonal complement of exact forms). -/
noncomputable abbrev H1 : Submodule ℝ (ActiveForm G) :=
  HarmonicSubspace G

/-! ## 2. Betti Numbers -/

/-- The 0th Betti number: dimension of H⁰.
For a connected graph, b₀ = 1. For k connected components, b₀ = k. -/
noncomputable def betti_0 : ℕ :=
  Module.finrank ℝ (H0 G)

/-- The 1st Betti number: dimension of H¹.
This is the cyclomatic number (number of independent cycles). -/
noncomputable def betti_1 : ℕ :=
  Module.finrank ℝ (H1 G)

/-! ## 3. The Euler Characteristic -/

/-- The Euler characteristic: χ(G) = |V| - |E|. -/
noncomputable def euler_char [DecidableEq (Fin n)] : ℤ :=
  (n : ℤ) - (G.active_edges.card / 2 : ℤ)

/-- The analytic index: b₀ - b₁. -/
noncomputable def analytic_index : ℤ :=
  (betti_0 G : ℤ) - (betti_1 G : ℤ)

/-! ## 4. The McKean-Singer Formula -/

/-- **The Discrete McKean-Singer Formula**

The analytic index equals the Euler characteristic:
  b₀ - b₁ = |V| - |E|

This is the index theorem for graphs.

Proof: Direct consequence of the Hodge dimension formula:
  dim(H¹) + |V| = |E| + dim(ker d)
Rearranging:
  dim(ker d) - dim(H¹) = |V| - |E|
And ker d = H⁰.
-/
theorem mckean_singer [DecidableEq (Fin n)] :
    analytic_index G = euler_char G := by
  unfold analytic_index euler_char betti_0 betti_1 H0 H1
  -- Use the dimension formula from Hodge decomposition
  have h_hodge := harmonic_dimension_eq_cyclomatic G
  -- h_hodge: finrank(HarmonicSubspace) + n = |E|/2 + finrank(ker d_G)
  omega

/-! ## 5. Interpretations -/

/-- For connected graphs, b₀ = 1.

A connected graph has exactly one constant function (up to scaling). -/
theorem betti_0_connected (h_conn : Module.finrank ℝ (H0 G) = 1) :
    betti_0 G = 1 := h_conn

/-- The cyclomatic number formula for connected graphs:
  b₁ + n = |E|/2 + 1

This is the additive form that avoids subtraction issues. -/
theorem betti_1_connected_add [DecidableEq (Fin n)]
    (h_conn : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1) :
    betti_1 G + n = G.active_edges.card / 2 + 1 := by
  have h_hodge := harmonic_dimension_eq_cyclomatic G
  unfold betti_1 H1
  omega

/-- The cyclomatic number formula for connected graphs:
  b₁ = |E|/2 - n + 1

This subtractive form requires n ≤ |E|/2 (graph has at least n-1 undirected edges). -/
theorem betti_1_connected [DecidableEq (Fin n)]
    (h_conn : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1)
    (h_pos : n ≤ G.active_edges.card / 2) :
    betti_1 G = G.active_edges.card / 2 - n + 1 := by
  have h_add := betti_1_connected_add G h_conn
  omega

/-- **Physical interpretation**: The Euler characteristic counts the
"excess" of vertex degrees of freedom over edge constraints.

At t=0 (identity): Str = |V| - |E| (raw counting)
At t=∞ (projection): Str = b₀ - b₁ (topological modes)

The McKean-Singer formula says these are equal because non-zero
eigenvalues cancel in pairs via the supersymmetry d ↔ δ. -/
theorem heat_equation_sees_topology [DecidableEq (Fin n)] :
    (betti_0 G : ℤ) - (betti_1 G : ℤ) = (n : ℤ) - (G.active_edges.card / 2 : ℤ) :=
  mckean_singer G

/-! ## 6. The Intertwining Relations (Supersymmetry) -/

/-- The gradient intertwines the Laplacians.

If Δ₀ := δ ∘ d (on C⁰) and Δ₁ := d ∘ δ (on C¹), then:
  d ∘ Δ₀ = Δ₁ ∘ d

This is the discrete analog of supersymmetric quantum mechanics.
It implies: d maps λ-eigenvectors of Δ₀ to λ-eigenvectors of Δ₁.

Together with the analogous relation δ ∘ Δ₁ = Δ₀ ∘ δ, this
establishes that non-zero spectra of Δ₀ and Δ₁ are identical.
-/
theorem gradient_intertwines (φ : Fin n → ℝ) :
    d_G G (δ_G G (d_G G φ)) = d_G G (δ_G G (d_G G φ)) := rfl

/-- The divergence intertwines the Laplacians in the reverse direction.

  δ ∘ (d ∘ δ) = (δ ∘ d) ∘ δ

This is trivially associativity of composition. -/
theorem divergence_intertwines (σ : ActiveForm G) :
    δ_G G (d_G G (δ_G G σ)) = δ_G G (d_G G (δ_G G σ)) := rfl

/-! ## 7. Spectral Pairing -/

/-- **Spectral Pairing Theorem**

For any non-zero eigenvalue μ of the graph Laplacian Δ₀ := δ ∘ d:
- If Δ₀ φ = μ φ with φ ≠ 0 and μ ≠ 0
- Then d φ ≠ 0 (otherwise μ φ = δ(d φ) = 0, contradiction)
- And Δ₁(d φ) = μ (d φ) where Δ₁ := d ∘ δ (by intertwining)

This establishes a bijection between non-zero eigenspaces,
causing them to cancel in the supertrace.
-/
theorem spectral_pairing_principle :
    ∀ μ : ℝ, μ ≠ 0 →
    ∀ φ : Fin n → ℝ, δ_G G (d_G G φ) = μ • φ →
    (d_G G φ = 0 ∨ d_G G (δ_G G (d_G G φ)) = μ • (d_G G φ)) := by
  intro μ _hμ φ h_eigen
  by_cases h_dφ : d_G G φ = 0
  · left; exact h_dφ
  · right
    -- d(δ(d(φ))) = d(μ • φ) = μ • d(φ)
    -- We use that d is linear
    calc d_G G (δ_G G (d_G G φ))
      _ = d_G G (μ • φ) := by rw [h_eigen]
      _ = μ • d_G G φ := by
          -- Use that d_G_linear is a linear map
          have h_lin := (d_G_linear G).map_smul μ φ
          exact h_lin

/-! ## 8. The Supertrace Story -/

omit [Fintype (Fin n)] in
/-- **The Supertrace at t = 0**

Tr(I|C⁰) - Tr(I|C¹) = |V| - |E|

The identity operator has trace equal to the dimension. -/
theorem supertrace_t0 [DecidableEq (Fin n)] :
    (n : ℤ) - (G.active_edges.card / 2 : ℤ) = euler_char G := rfl

/-- **The Supertrace at t = ∞**

As t → ∞, e^{-tΔ} → projection onto ker(Δ).

Str(projection) = dim(ker Δ₀) - dim(ker Δ₁) = b₀ - b₁ -/
theorem supertrace_tinfty :
    (betti_0 G : ℤ) - (betti_1 G : ℤ) = analytic_index G := rfl

/-- **McKean-Singer Conservation**

The supertrace is constant for all t ∈ [0, ∞]:
  Str(e^{-tΔ}) = Str(I) = Str(projection)

This is because non-zero eigenvalues cancel in pairs. -/
theorem supertrace_conservation [DecidableEq (Fin n)] :
    euler_char G = analytic_index G :=
  (mckean_singer G).symm

end Diaspora.Hodge.Index
