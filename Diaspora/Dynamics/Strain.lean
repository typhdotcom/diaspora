/-
# Topology Change

When edge strain exceeds a threshold, the edge breaks, changing the graph topology.
Strain energy that cannot be absorbed by local potentials becomes topological.
-/

import Diaspora.Hodge.Harmonic
import Diaspora.Core.Phase

open BigOperators Diaspora.Core Diaspora.Hodge

namespace Diaspora.Dynamics

/-! ## Structural Limits -/

/-- Maximum strain an edge can sustain before breaking -/
def BreakingThreshold := ℝ

/-- Strain on a single edge -/
noncomputable def edge_strain {n : ℕ} (ϕ : C0 n) (σ : C1 n) (i j : Fin n) : ℝ :=
  ((d0 ϕ).val i j - σ.val i j)^2

/-! ## Phase-Field Strain -/

/-- Phase strain: accounts for cyclic boundary conditions.
    Measures frustration on an edge in the phase field. -/
noncomputable def phase_edge_strain {n k : ℕ} [NeZero k]
    (ϕ : PC0 n k) (σ : PC1 n k) (i j : Fin n) : ℝ :=
  let delta := (pd0 ϕ).val i j - σ.val i j
  (geodesic_dist delta 0 : ℝ)^2

/-! ## Strain Localization -/

/--
If total strain is high, some edge must have high strain (pigeonhole principle).
-/
theorem strain_must_localize {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (ϕ : C0 n) (σ : C1 n) (C_max : ℝ)
    (h_total : norm_sq (Diaspora.Core.residual ϕ σ) > (1/2) * (Fintype.card (Fin n))^2 * C_max) :
  ∃ i j : Fin n, edge_strain ϕ σ i j > C_max := by
  by_contra h_none
  push_neg at h_none

  have h_sum_bound : ∑ i : Fin n, ∑ j : Fin n, edge_strain ϕ σ i j ≤
                     ∑ i : Fin n, ∑ j : Fin n, C_max := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    exact h_none i j

  have h_card : ∑ i : Fin n, ∑ j : Fin n, C_max = (Fintype.card (Fin n))^2 * C_max := by
    rw [Finset.sum_const, Finset.card_univ, Finset.sum_const, Finset.card_univ]
    ring

  have h_norm : norm_sq (Diaspora.Core.residual ϕ σ) =
                (1/2) * ∑ i : Fin n, ∑ j : Fin n, edge_strain ϕ σ i j := by
    unfold norm_sq inner_product_C1 Diaspora.Core.residual edge_strain
    simp only [d0]
    congr 1; congr 1
    ext i; congr 1; ext j
    ring

  have h_half_bound : (1/2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n, edge_strain ϕ σ i j ≤
                      (1/2) * ((Fintype.card (Fin n))^2 * C_max) := by
    rw [← h_card]
    apply mul_le_mul_of_nonneg_left h_sum_bound
    norm_num
  rw [← h_norm] at h_half_bound
  linarith

/-! ## Gauge Invariance of Holonomy -/

/--
External observers measuring holonomy see only the harmonic component γ.
Local details (the exact part dϕ) vanish on cycles by Stokes' theorem.
-/
theorem holonomy_sees_only_harmonic {n : ℕ} [Fintype (Fin n)]
    (σ : C1 n) (cycle : Chain1 n)
    (h_cycle : Chain1.IsCycle cycle) :
  ∃ γ : C1 n, IsHarmonic γ ∧ holonomy σ cycle = holonomy γ cycle := by
  obtain ⟨γ, h_harm, ϕ, _, h_holonomy⟩ := holonomy_factor_through_harmonic σ
  exact ⟨γ, h_harm, h_holonomy cycle h_cycle⟩

/-! ## Topological Defect Formation -/

/--
When residual strain exceeds the threshold, localization forces some edge to break.
The resulting topology contains a non-trivial harmonic component:
- Energy: ||γ||² (irreducible frustration)
- Topological charge: winding number m
- Observable via holonomy, independent of local gauge choices
-/
theorem topological_defect_formation
    {n : ℕ} [Fintype (Fin n)] [NeZero n]
    (σ : C1 n) (C_max : ℝ) (h_pos : C_max > 0)
    (ϕ_opt : C0 n)
    (h_min : ∀ ϕ', norm_sq (Diaspora.Core.residual ϕ_opt σ) ≤ norm_sq (Diaspora.Core.residual ϕ' σ))
    (h_frustration : norm_sq (Diaspora.Core.residual ϕ_opt σ) > (1/2) * (Fintype.card (Fin n))^2 * C_max) :
  (∃ i j : Fin n, edge_strain ϕ_opt σ i j > C_max)
  ∧
  (∃ γ : C1 n, IsHarmonic γ ∧ norm_sq γ > 0)
  ∧
  (∀ cycle : Chain1 n, Chain1.IsCycle cycle →
    ∃ γ : C1 n, IsHarmonic γ ∧ holonomy σ cycle = holonomy γ cycle) := by
  constructor
  · exact strain_must_localize ϕ_opt σ C_max h_frustration
  constructor
  · obtain ⟨ϕ, γ, h_decomp, h_harm, _⟩ := hodge_decomposition σ
    use γ, h_harm

    by_contra h_zero
    push_neg at h_zero

    have h_norm_nonneg : norm_sq γ ≥ 0 := by
      unfold norm_sq inner_product_C1
      apply mul_nonneg
      · norm_num
      · apply Finset.sum_nonneg; intro i _
        apply Finset.sum_nonneg; intro j _
        exact mul_self_nonneg _
    have h_gamma_zero : norm_sq γ = 0 := by linarith

    have h_resid_eq : ∀ i j, (Diaspora.Core.residual ϕ σ).val i j = -γ.val i j := by
      intro i j
      unfold Diaspora.Core.residual
      have := h_decomp i j
      linarith

    have h_resid_norm : norm_sq (Diaspora.Core.residual ϕ σ) = norm_sq γ := by
      unfold norm_sq inner_product_C1
      congr 1; congr 1
      ext i; congr 1; ext j
      rw [h_resid_eq]
      ring

    have h_opt_resid : norm_sq (Diaspora.Core.residual ϕ_opt σ) ≤ norm_sq (Diaspora.Core.residual ϕ σ) := h_min ϕ

    rw [h_resid_norm, h_gamma_zero] at h_opt_resid
    have h_card_pos : (1/2) * (Fintype.card (Fin n))^2 * C_max > 0 := by
      apply mul_pos
      · apply mul_pos
        · norm_num
        · apply sq_pos_of_ne_zero
          simp
      · exact h_pos
    linarith

  · intro cycle h_cycle
    exact holonomy_sees_only_harmonic σ cycle h_cycle

end Diaspora.Dynamics
