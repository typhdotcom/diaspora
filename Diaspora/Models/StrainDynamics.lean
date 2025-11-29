import Diaspora.Models.WeightedStrain
import Diaspora.Dynamics.Plasticity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic

open BigOperators Diaspora.Core Diaspora.Hodge Diaspora.Dynamics Diaspora.Logic Diaspora.Models

namespace Diaspora.Models

/-! ## 1. Analytical Solution for the Bundle -/

/--
Optimal potential difference `x = ϕ(1) - ϕ(0)` for any weight distribution.
The graph is a parallel circuit.
- `W_H`: Total weight of the heavy edges (0↔1).
- `W_L`: Total effective weight of the light paths.
-/
noncomputable def optimal_potential_diff (W_H W_L : ℝ) : ℝ :=
  10 * W_H / (W_H + W_L)

/--
The strain on light edges given the optimal potential.
Strain = (x - 0)²
-/
noncomputable def light_strain (W_H W_L : ℝ) : ℝ :=
  (optimal_potential_diff W_H W_L)^2

/--
The strain on heavy edges given the optimal potential.
Strain = (x - 10)²
-/
noncomputable def heavy_strain (W_H W_L : ℝ) : ℝ :=
  (optimal_potential_diff W_H W_L - 10)^2

/-! ## 2. Strain Asymmetry -/

/--
Theorem: If the heavy edge dominates (W_H > W_L), light edges experience higher strain.
This is the precondition for differential growth under Hebbian plasticity.
-/
theorem dominance_causes_strain_asymmetry (W_H W_L : ℝ)
    (h_pos : W_H > 0 ∧ W_L > 0)
    (h_dominance : W_H > W_L) :
    light_strain W_H W_L > heavy_strain W_H W_L := by
  unfold light_strain heavy_strain optimal_potential_diff
  -- We want to prove (10 * W_H / Sum)² > (10 * W_H / Sum - 10)²
  -- The key insight: LHS = (10 W_H / Sum)², RHS = (-10 W_L / Sum)²
  -- So we need |10 W_H / Sum| > |10 W_L / Sum|, i.e., W_H > W_L
  have h_sum_pos : W_H + W_L > 0 := add_pos h_pos.1 h_pos.2
  rw [gt_iff_lt, sq_lt_sq]
  -- Now goal: |10 * W_H / (W_H + W_L) - 10| < |10 * W_H / (W_H + W_L)|
  have h_eq : 10 * W_H / (W_H + W_L) - 10 = -(10 * W_L / (W_H + W_L)) := by field_simp; ring
  rw [h_eq, abs_neg]
  have h1 : 0 < 10 * W_H / (W_H + W_L) := div_pos (by linarith) h_sum_pos
  have h2 : 0 < 10 * W_L / (W_H + W_L) := div_pos (by linarith) h_sum_pos
  rw [abs_of_pos h1, abs_of_pos h2]
  -- Goal: 10 * W_L / (W_H + W_L) < 10 * W_H / (W_H + W_L)
  gcongr

/--
Theorem: Hebbian plasticity favors the strained.
If we apply one step of plasticity, the *unnormalized* weight of light edges grows
faster than heavy edges when the heavy edge is dominant.
-/
theorem hebbian_favors_strained (W_H W_L : ℝ) (η : ℝ)
    (h_pos : W_H > 0 ∧ W_L > 0)
    (h_eta : η > 0)
    (h_dominance : W_H > W_L) :
    let S_L := light_strain W_H W_L
    let S_H := heavy_strain W_H W_L
    let growth_L := η * S_L
    let growth_H := η * S_H
    growth_L > growth_H := by
  intro S_L S_H growth_L growth_H
  have h_strain := dominance_causes_strain_asymmetry W_H W_L h_pos h_dominance
  dsimp [growth_L, growth_H, S_L, S_H]
  gcongr

/--
Theorem: Weight ratio correction.
The ratio of light weight to heavy weight increases after a plasticity step.
ratio_new > ratio_old
-/
theorem ratio_correction (w_h w_l : ℝ) (η : ℝ)
    (h_pos : w_h > 0 ∧ w_l > 0)
    (h_eta : η > 0)
    (h_dominance : w_h > w_l) -- Individual heavy edges are heavier than light edges
    (h_agg_dominance : (2 * w_h) > (12 * w_l)) :
    let W_H := 2 * w_h
    let W_L := 12 * w_l
    let S_L := light_strain W_H W_L
    let S_H := heavy_strain W_H W_L
    (w_l + η * S_L) / (w_h + η * S_H) > w_l / w_h := by
  intro W_H W_L S_L S_H
  -- (w_l + η S_l) / (w_h + η S_h) > w_l / w_h
  -- Cross multiply (all positive):
  -- w_h(w_l + η S_l) > w_l(w_h + η S_h)
  -- w_h w_l + η w_h S_l > w_l w_h + η w_l S_h
  -- η w_h S_l > η w_l S_h
  -- w_h S_l > w_l S_h
  have h_sh_nonneg : S_H ≥ 0 := sq_nonneg _
  have h_denom1_pos : w_h + η * S_H > 0 := by nlinarith
  have h_denom2_pos : w_h > 0 := h_pos.1
  rw [gt_iff_lt, div_lt_div_iff₀ h_denom2_pos h_denom1_pos]
  -- Goal: w_l * (w_h + η * S_H) < (w_l + η * S_L) * w_h
  ring_nf
  -- Goal: w_h * w_l + w_l * η * S_H < w_h * w_l + w_h * η * S_L
  -- Simplifies to: w_l * η * S_H < w_h * η * S_L
  have h_strain := dominance_causes_strain_asymmetry W_H W_L ⟨by linarith, by linarith⟩ h_agg_dominance
  -- We need: w_l * S_H < w_h * S_L
  have h_sl_pos : S_L > 0 := lt_of_le_of_lt h_sh_nonneg h_strain
  have h_key : w_l * S_H < w_h * S_L := by
    calc w_l * S_H ≤ w_l * S_L := mul_le_mul_of_nonneg_left (le_of_lt h_strain) (le_of_lt h_pos.2)
      _ < w_h * S_L := by gcongr
  nlinarith

end Diaspora.Models
