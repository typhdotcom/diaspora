import Diaspora.Logic.Probabilistic
import Diaspora.Logic.Foundations
import Diaspora.Models.Void

namespace Diaspora.Logic.Limit

open Diaspora.Core Diaspora.Hodge Diaspora.Logic

/-! # The Big Bang Theorem -/

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-! ## 1. The Topology-Logic Dictionary -/

/-- The first Betti number (cyclomatic complexity). -/
noncomputable def bettiOne (G : DynamicGraph n) : ℕ :=
  Module.finrank ℝ (HarmonicSubspace G)

/-- Number of undirected edges. -/
noncomputable def edgeCount (G : DynamicGraph n) : ℕ :=
  G.active_edges.card / 2

/-- A universe is "topologically complex" if it has cycles. -/
def IsComplex (G : DynamicGraph n) : Prop :=
  bettiOne G > 0

omit [DecidableEq (Fin n)] in
/-- Complex ↔ ¬Classical. -/
theorem complex_iff_not_classical (G : DynamicGraph n) :
    IsComplex G ↔ ¬ IsClassical G := by
  simp only [IsComplex, IsClassical, bettiOne]
  omega

/-! ## 2. Universe Growth Dynamics -/

/--
A UniverseSequence is a growing family of graphs indexed by ℕ.
Each G_n lives on Fin n vertices.
-/
structure UniverseSequence where
  /-- The graph at stage n (on Fin n vertices) -/
  graph : (n : ℕ) → [Fintype (Fin n)] → [DecidableEq (Fin n)] → DynamicGraph n

/-- Edge growth rate at stage n. -/
noncomputable def edgeGrowthRate (seq : UniverseSequence) (n : ℕ)
    [Fintype (Fin n)] [DecidableEq (Fin n)] : ℕ :=
  edgeCount (seq.graph n)

/-- Additive superlinear growth: |E| - n → ∞. -/
def HasAdditiveGrowth (seq : UniverseSequence) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ [Fintype (Fin n)] [DecidableEq (Fin n)],
    edgeGrowthRate seq n > n + k

/-- Multiplicative superlinear growth: |E|/n → ∞. -/
def HasMultiplicativeGrowth (seq : UniverseSequence) : Prop :=
  ∀ C : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ [Fintype (Fin n)] [DecidableEq (Fin n)],
    edgeGrowthRate seq n > C * n

/-! ## 3. The Complexity Threshold -/

/-- When edges exceed vertices, Genesis is guaranteed. -/
theorem complexity_threshold {m : ℕ} [NeZero m] [Fintype (Fin m)] [DecidableEq (Fin m)]
    (G : DynamicGraph m)
    (h_conn : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1)
    (h_edges : edgeCount G ≥ m) :
    IsComplex G := by
  unfold IsComplex bettiOne
  have h_observer : Models.HasObserver G := h_edges
  exact Models.observer_creates_mass G h_observer h_conn

/-! ## 4. The Probability of Classicality -/

/-- Classical probability: dim(ImGradient)/dim(ActiveForm). -/
noncomputable def classicalRatio {m : ℕ} [Fintype (Fin m)] [DecidableEq (Fin m)]
    (G : DynamicGraph m) : ℝ :=
  if Module.finrank ℝ (ActiveForm G) = 0 then 1
  else Module.finrank ℝ (ImGradient G) / Module.finrank ℝ (ActiveForm G)

/-- Classical ratio ≤ 1. -/
theorem classicalRatio_le_one {m : ℕ} [Fintype (Fin m)] [DecidableEq (Fin m)]
    (G : DynamicGraph m) : classicalRatio G ≤ 1 := by
  unfold classicalRatio
  split_ifs with h
  · exact le_refl 1
  · have h_pos : (0 : ℝ) < Module.finrank ℝ (ActiveForm G) := by
      simp only [Nat.cast_pos]
      exact Nat.pos_of_ne_zero h
    have h_le : Module.finrank ℝ (ImGradient G) ≤ Module.finrank ℝ (ActiveForm G) := by
      exact Submodule.finrank_le (ImGradient G)
    exact (div_le_one h_pos).mpr (Nat.cast_le.mpr h_le)

/-- Classical ratio < 1 for complex graphs. -/
theorem classicalRatio_decreases_with_topology {m : ℕ}
    [Fintype (Fin m)] [DecidableEq (Fin m)] (G : DynamicGraph m)
    (h_complex : IsComplex G) :
    classicalRatio G < 1 := by
  unfold classicalRatio
  split_ifs with h
  · exfalso
    simp only [IsComplex, bettiOne] at h_complex
    have h_harm_zero : Module.finrank ℝ (HarmonicSubspace G) = 0 := by
      have h_harm_le := Submodule.finrank_le (HarmonicSubspace G)
      omega
    omega
  · have h_gap := Probabilistic.dimensional_gap G
    have h_harm_pos : Module.finrank ℝ (HarmonicSubspace G) > 0 := h_complex
    have h_strict : Module.finrank ℝ (ImGradient G) < Module.finrank ℝ (ActiveForm G) := by
      omega
    have h_pos : (0 : ℝ) < Module.finrank ℝ (ActiveForm G) := by
      simp only [Nat.cast_pos]; exact Nat.pos_of_ne_zero h
    exact (div_lt_one h_pos).mpr (Nat.cast_lt.mpr h_strict)

/-! ## 5. The Inevitable Genesis Theorem -/

/-- Classical ratio is non-negative. -/
lemma classicalRatio_nonneg {m : ℕ} [Fintype (Fin m)] [DecidableEq (Fin m)]
    (G : DynamicGraph m) : 0 ≤ classicalRatio G := by
  unfold classicalRatio
  split_ifs
  · exact zero_le_one
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- For connected graphs with edges, classicalRatio ≤ n/|E|. -/
lemma classicalRatio_bound {m : ℕ} [Fintype (Fin m)] [DecidableEq (Fin m)]
    (G : DynamicGraph m)
    (h_conn : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1)
    (h_edges : edgeCount G > 0) :
    classicalRatio G ≤ (m : ℝ) / edgeCount G := by
  unfold classicalRatio edgeCount at *
  -- From edgeCount > 0, deduce card ≥ 2 (since card/2 > 0 implies card ≥ 2)
  have h_card_ge_2 : G.active_edges.card ≥ 2 := by
    by_contra h_lt
    push_neg at h_lt
    interval_cases G.active_edges.card <;> simp_all
  -- By rank-nullity: dim(ImGradient) = m - 1
  have h_rank_nullity := LinearMap.finrank_range_add_finrank_ker (d_G_linear G)
  simp only [Module.finrank_fin_fun] at h_rank_nullity
  rw [← ImGradient, h_conn] at h_rank_nullity
  have h_ImGrad : Module.finrank ℝ (ImGradient G) = m - 1 := by omega
  have h_Active := active_form_dimension G
  split_ifs with h
  · -- dim(ActiveForm) = 0 contradicts h_edges
    rw [h_Active] at h
    omega
  · -- (m-1)/|E| ≤ m/|E|
    rw [h_ImGrad, h_Active]
    have h_pos : (0 : ℝ) < G.active_edges.card / 2 := by
      apply div_pos (Nat.cast_pos.mpr (by omega : G.active_edges.card > 0)) (by norm_num)
    gcongr
    omega

/-- Big Bang (Weak): superlinear growth ⟹ eventually complex. -/
theorem eventual_genesis (seq : UniverseSequence)
    (h_growth : HasAdditiveGrowth seq)
    (h_conn : ∀ n [Fintype (Fin n)] [DecidableEq (Fin n)],
              Module.finrank ℝ (LinearMap.ker (d_G_linear (seq.graph n))) = 1) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ [NeZero n] [Fintype (Fin n)] [DecidableEq (Fin n)],
      IsComplex (seq.graph n) := by
  obtain ⟨N, hN⟩ := h_growth 0
  use max N 1
  intro n hn_ge _ _ _
  have hn_ge_N : n ≥ N := le_of_max_le_left hn_ge
  have h_edges := hN n hn_ge_N
  simp only [edgeGrowthRate, add_zero] at h_edges
  exact complexity_threshold (seq.graph n) (h_conn n) (Nat.le_of_lt h_edges)

/-- Big Bang (Strong): as n → ∞, classicalRatio → 0. -/
theorem inevitable_genesis (seq : UniverseSequence)
    (h_growth : HasMultiplicativeGrowth seq)
    (h_conn : ∀ n [Fintype (Fin n)] [DecidableEq (Fin n)],
              Module.finrank ℝ (LinearMap.ker (d_G_linear (seq.graph n))) = 1) :
    Filter.Tendsto
      (fun n => @classicalRatio n ⟨Fintype.elems, Fintype.complete⟩
                  (fun _ _ => Classical.propDecidable _) (seq.graph n))
      Filter.atTop
      (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let C := Nat.ceil (1/ε) + 1
  have hC_pos : (C : ℝ) > 0 := by simp [C]; positivity
  have hC_inv : (C : ℝ)⁻¹ < ε := by
    have h1 : (Nat.ceil (1/ε) : ℝ) ≥ 1/ε := Nat.le_ceil (1/ε)
    have h2 : (C : ℝ) > 1/ε := by
      calc (C : ℝ) = (Nat.ceil (1/ε) : ℝ) + 1 := by simp [C]
        _ ≥ 1/ε + 1 := by linarith
        _ > 1/ε := by linarith
    calc (C : ℝ)⁻¹ < (1/ε)⁻¹ := inv_strictAnti₀ (by positivity) h2
       _ = ε := by field_simp
  obtain ⟨N, hN⟩ := h_growth C
  use max N 1
  intro n hn
  have hn_ge_N : n ≥ N := le_of_max_le_left hn
  have hn_pos : 0 < n := Nat.pos_of_ne_zero (fun h => by omega)
  have h_edges := hN n hn_ge_N
  have h_E_pos : edgeGrowthRate seq n > 0 := by
    calc edgeGrowthRate seq n > C * n := h_edges
       _ ≥ C * 1 := by gcongr; omega
       _ > 0 := by simp [C]
  have h_ratio_lt : classicalRatio (seq.graph n) < ε :=
    calc classicalRatio (seq.graph n)
        ≤ (n : ℝ) / edgeGrowthRate seq n := classicalRatio_bound _ (h_conn n) h_E_pos
      _ < n / (C * n) := by
          apply div_lt_div_of_pos_left (Nat.cast_pos.mpr hn_pos)
          · positivity
          · rw [← Nat.cast_mul]; exact (Nat.cast_lt (α := ℝ)).mpr h_edges
      _ = (C : ℝ)⁻¹ := by field_simp
      _ < ε := hC_inv
  rw [Real.dist_0_eq_abs]
  have h_nonneg := classicalRatio_nonneg (seq.graph n)
  refine abs_lt.mpr ⟨?_, h_ratio_lt⟩
  calc -ε < 0 := neg_neg_iff_pos.mpr hε
    _ ≤ classicalRatio (seq.graph n) := h_nonneg

end Diaspora.Logic.Limit
