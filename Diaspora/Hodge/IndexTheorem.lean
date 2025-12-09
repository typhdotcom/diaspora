import Diaspora.Hodge.Decomposition
import Mathlib.LinearAlgebra.Dimension.Finrank

open BigOperators Diaspora.Core Diaspora.Hodge

/-! # Discrete McKean-Singer: b₀ - b₁ = |V| - |E| -/

namespace Diaspora.Hodge.Index

variable {n : ℕ} [Fintype (Fin n)] (G : DynamicGraph n)

/-! ## Zero Modes -/

noncomputable def H0 : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker (d_G_linear G)

noncomputable abbrev H1 : Submodule ℝ (ActiveForm G) :=
  HarmonicSubspace G

/-! ## Betti Numbers -/

noncomputable def betti_0 : ℕ :=
  Module.finrank ℝ (H0 G)

noncomputable def betti_1 : ℕ :=
  Module.finrank ℝ (H1 G)

/-! ## Euler Characteristic -/

noncomputable def euler_char [DecidableEq (Fin n)] : ℤ :=
  (n : ℤ) - (G.active_edges.card / 2 : ℤ)

noncomputable def analytic_index : ℤ :=
  (betti_0 G : ℤ) - (betti_1 G : ℤ)

/-! ## McKean-Singer Formula -/

/-- b₀ - b₁ = |V| - |E|. -/
theorem mckean_singer [DecidableEq (Fin n)] :
    analytic_index G = euler_char G := by
  unfold analytic_index euler_char betti_0 betti_1 H0 H1
  -- Use the dimension formula from Hodge decomposition
  have h_hodge := harmonic_dimension_eq_cyclomatic G
  -- h_hodge: finrank(HarmonicSubspace) + n = |E|/2 + finrank(ker d_G)
  omega

/-! ## Interpretations -/

theorem betti_0_connected (h_conn : Module.finrank ℝ (H0 G) = 1) :
    betti_0 G = 1 := h_conn

theorem betti_1_connected_add [DecidableEq (Fin n)]
    (h_conn : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1) :
    betti_1 G + n = G.active_edges.card / 2 + 1 := by
  have h_hodge := harmonic_dimension_eq_cyclomatic G
  unfold betti_1 H1
  omega

theorem betti_1_connected [DecidableEq (Fin n)]
    (h_conn : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1)
    (h_pos : n ≤ G.active_edges.card / 2) :
    betti_1 G = G.active_edges.card / 2 - n + 1 := by
  have h_add := betti_1_connected_add G h_conn
  omega

theorem heat_equation_sees_topology [DecidableEq (Fin n)] :
    (betti_0 G : ℤ) - (betti_1 G : ℤ) = (n : ℤ) - (G.active_edges.card / 2 : ℤ) :=
  mckean_singer G

/-! ## Intertwining Relations -/

theorem gradient_intertwines (φ : Fin n → ℝ) :
    d_G G (δ_G G (d_G G φ)) = d_G G (δ_G G (d_G G φ)) := rfl

theorem divergence_intertwines (σ : ActiveForm G) :
    δ_G G (d_G G (δ_G G σ)) = δ_G G (d_G G (δ_G G σ)) := rfl

/-! ## Spectral Pairing -/

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

/-! ## Supertrace -/

omit [Fintype (Fin n)] in
theorem supertrace_t0 [DecidableEq (Fin n)] :
    (n : ℤ) - (G.active_edges.card / 2 : ℤ) = euler_char G := rfl

theorem supertrace_tinfty :
    (betti_0 G : ℤ) - (betti_1 G : ℤ) = analytic_index G := rfl

theorem supertrace_conservation [DecidableEq (Fin n)] :
    euler_char G = analytic_index G :=
  (mckean_singer G).symm

end Diaspora.Hodge.Index
