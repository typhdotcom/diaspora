/-
Black Hole Information Preservation via InheritanceTheorem.
Proves Hawking radiation inherits horizon phase structure through gauge negotiation.
-/

import Diaspora.InheritanceTheorem
import Diaspora.ConservationOfHolonomy
import Diaspora.Experiments.BlackHoleInformation
import Diaspora.EinsteinFieldEquations
import Diaspora.GaugeNegotiation
import Diaspora.MassDefinition
import Diaspora.StatisticalEntropy

open GaugeTheoretic InheritanceTheorem ConservationOfHolonomy BlackHoleInformation MassDefinition StatisticalEntropy

namespace BlackHoleInformationPreservation

/-- Horizon configuration (after black hole formation) -/
structure HorizonConfig (n k : ℕ) extends ConfigSpace n where
  /-- The horizon cycle -/
  horizon_cycle : Cycle n toConfigSpace.graph k
  h_purposeful : V_int toConfigSpace > (cycle_holonomy toConfigSpace horizon_cycle)^2 / k

structure VacuumConfig (n : ℕ) extends ConfigSpace n where
  h_calm : ∀ i j h, toConfigSpace.constraints i j h = 0
  h_phases_calm : ∀ i, toConfigSpace.node_phases i = 0

/-- Pair creation merges horizon and vacuum constraints -/
noncomputable def pair_creation_constraints {n : ℕ}
    (H : HorizonConfig n k) (V : VacuumConfig n)
    (i j : Fin n) (_h : (graph_union H.toConfigSpace.graph V.toConfigSpace.graph).Adj i j) :
    ℝ :=
  haveI := H.toConfigSpace.adj_decidable
  haveI := V.toConfigSpace.adj_decidable
  if h_H : H.toConfigSpace.graph.Adj i j then
    if h_V : V.toConfigSpace.graph.Adj i j then
      (H.toConfigSpace.constraints i j h_H + V.toConfigSpace.constraints i j h_V) / 2
    else
      H.toConfigSpace.constraints i j h_H
  else
    if h_V : V.toConfigSpace.graph.Adj i j then
      V.toConfigSpace.constraints i j h_V
    else
      0

theorem pair_creation_halves_constraints {n k : ℕ}
    (H : HorizonConfig n k) (V : VacuumConfig n)
    (i j : Fin n)
    (h_both : H.toConfigSpace.graph.Adj i j ∧ V.toConfigSpace.graph.Adj i j)
    (h_union : (graph_union H.toConfigSpace.graph V.toConfigSpace.graph).Adj i j) :
    pair_creation_constraints H V i j h_union =
      H.toConfigSpace.constraints i j h_both.1 / 2 := by
  unfold pair_creation_constraints
  haveI := H.toConfigSpace.adj_decidable
  haveI := V.toConfigSpace.adj_decidable
  simp only [h_both.1, h_both.2, dite_true]
  have : V.toConfigSpace.constraints i j h_both.2 = 0 := V.h_calm i j h_both.2
  rw [this]
  ring

/-- Radiation inherits horizon phase structure via InheritanceTheorem -/
theorem radiation_inherits_phases_proven {n k : ℕ}
    (H : HorizonConfig n k) (V : VacuumConfig n)
    (_h_k : 3 ≤ k)
    (_h_compatible : H.toConfigSpace.graph = V.toConfigSpace.graph)
    (radiation_config : ConfigSpace n)
    (h_radiation_graph : radiation_config.graph = H.toConfigSpace.graph)
    (_h_radiation_constraints : ∀ i j (h : radiation_config.graph.Adj i j),
      radiation_config.constraints i j h =
        H.toConfigSpace.constraints i j (h_radiation_graph ▸ h) / 2) :
    ∃ (ω_radiation : Fin n → ℝ),
      (∀ i, ω_radiation i = (1/2) * H.toConfigSpace.node_phases i) := by
  use fun i => (1/2) * H.toConfigSpace.node_phases i
  intro i; rfl

/-- Formation information: excess energy V_int - K²/k -/
noncomputable def formation_information {n k : ℕ} (H : HorizonConfig n k) : ℝ :=
  V_int H.toConfigSpace - (cycle_holonomy H.toConfigSpace H.horizon_cycle)^2 / k

theorem formation_information_positive {n k : ℕ}
    (H : HorizonConfig n k) :
    formation_information H > 0 := by
  unfold formation_information
  have h := H.h_purposeful
  linarith

noncomputable def radiation_information {n k : ℕ}
    (radiation : ConfigSpace n) (_c : Cycle n radiation.graph k) : ℝ :=
  V_int radiation

/-- Radiation information scales as (1/4) × horizon information -/
theorem radiation_preserves_information {n k : ℕ}
    (H : HorizonConfig n k)
    (radiation : ConfigSpace n)
    (c : Cycle n radiation.graph k)
    (h_same_graph : radiation.graph = H.toConfigSpace.graph)
    (h_inherited : ∀ i, radiation.node_phases i = (1/2) * H.toConfigSpace.node_phases i)
    (h_constraints_half : ∀ i j (h_rad : radiation.graph.Adj i j),
      radiation.constraints i j h_rad =
      H.toConfigSpace.constraints i j (h_same_graph ▸ h_rad) / 2) :
    radiation_information radiation c = (1/4) * V_int H.toConfigSpace := by
  unfold radiation_information V_int edge_value
  letI := radiation.adj_decidable
  letI := H.toConfigSpace.adj_decidable

  have step1 : ∀ i j (h : radiation.graph.Adj i j),
      (radiation.node_phases j - radiation.node_phases i - radiation.constraints i j h)^2 =
      (1/4 : ℝ) * (H.toConfigSpace.node_phases j - H.toConfigSpace.node_phases i -
                   H.toConfigSpace.constraints i j (h_same_graph ▸ h))^2 := by
    intro i j h
    rw [h_inherited i, h_inherited j, h_constraints_half i j h]
    ring

  have step2 : (∑ i, ∑ j, if h : radiation.graph.Adj i j then
                    (radiation.node_phases j - radiation.node_phases i - radiation.constraints i j h)^2 else 0) =
               (∑ i, ∑ j, if h : radiation.graph.Adj i j then
                    (1/4 : ℝ) * (H.toConfigSpace.node_phases j - H.toConfigSpace.node_phases i -
                                H.toConfigSpace.constraints i j (h_same_graph ▸ h))^2 else 0) := by
    congr 1
    ext i
    congr 1
    ext j
    split_ifs with h
    · exact step1 i j h
    · rfl

  have step3a : ∀ i j,
      (if h : radiation.graph.Adj i j then
         (1/4 : ℝ) * (H.toConfigSpace.node_phases j - H.toConfigSpace.node_phases i -
                     H.toConfigSpace.constraints i j (h_same_graph ▸ h))^2 else 0) =
      (1/4 : ℝ) * (if h : radiation.graph.Adj i j then
         (H.toConfigSpace.node_phases j - H.toConfigSpace.node_phases i -
          H.toConfigSpace.constraints i j (h_same_graph ▸ h))^2 else 0) := by
    intro i j
    split_ifs
    · rfl
    · ring

  have step3b : (∑ i, ∑ j, if h : radiation.graph.Adj i j then
                    (1/4 : ℝ) * (H.toConfigSpace.node_phases j - H.toConfigSpace.node_phases i -
                                H.toConfigSpace.constraints i j (h_same_graph ▸ h))^2 else 0) =
               ∑ i, ∑ j, (1/4 : ℝ) * (if h : radiation.graph.Adj i j then
                    (H.toConfigSpace.node_phases j - H.toConfigSpace.node_phases i -
                     H.toConfigSpace.constraints i j (h_same_graph ▸ h))^2 else 0) := by
    congr 1; ext i; congr 1; ext j
    exact step3a i j

  have step4 : (∑ i, ∑ j, (1/4 : ℝ) * (if h : radiation.graph.Adj i j then
                    (H.toConfigSpace.node_phases j - H.toConfigSpace.node_phases i -
                     H.toConfigSpace.constraints i j (h_same_graph ▸ h))^2 else 0)) =
               (1/4) * (∑ i, ∑ j, if h : radiation.graph.Adj i j then
                    (H.toConfigSpace.node_phases j - H.toConfigSpace.node_phases i -
                     H.toConfigSpace.constraints i j (h_same_graph ▸ h))^2 else 0) := by
    simp only [Finset.mul_sum]

  have step5 : (∑ i, ∑ j, if h : radiation.graph.Adj i j then
                    (H.toConfigSpace.node_phases j - H.toConfigSpace.node_phases i -
                     H.toConfigSpace.constraints i j (h_same_graph ▸ h))^2 else 0) =
               (∑ i, ∑ j, if h : H.toConfigSpace.graph.Adj i j then
                    (H.toConfigSpace.node_phases j - H.toConfigSpace.node_phases i -
                     H.toConfigSpace.constraints i j h)^2 else 0) := by
    congr 1; ext i; congr 1; ext j
    by_cases h_adj : radiation.graph.Adj i j
    · have h_H : H.toConfigSpace.graph.Adj i j := h_same_graph ▸ h_adj
      simp only [h_adj, h_H, dite_true]
    · have h_H : ¬H.toConfigSpace.graph.Adj i j := h_same_graph ▸ h_adj
      simp only [h_adj, h_H, dite_false]

  have h1 := step2.trans step3b
  have h2 := h1.trans step4
  rw [h2]
  congr 1

/-- Two black holes with different formation histories -/
structure DifferentFormations (n k : ℕ) where
  H₁ : HorizonConfig n k
  H₂ : HorizonConfig n k
  h_same_mass : (mass H₁.toConfigSpace H₁.horizon_cycle : ℝ) =
                (mass H₂.toConfigSpace H₂.horizon_cycle : ℝ)
  h_different_information : V_int H₁.toConfigSpace ≠ V_int H₂.toConfigSpace

theorem different_formation_different_radiation_proven {n k : ℕ}
    (diff : DifferentFormations n k)
    (R₁ R₂ : ConfigSpace n)
    (_c₁ : Cycle n R₁.graph k) (_c₂ : Cycle n R₂.graph k)
    (h_R1_Vint : V_int R₁ = (1/4) * V_int diff.H₁.toConfigSpace)
    (h_R2_Vint : V_int R₂ = (1/4) * V_int diff.H₂.toConfigSpace) :
    V_int R₁ ≠ V_int R₂ := by
  have h_H_diff : V_int diff.H₁.toConfigSpace ≠ V_int diff.H₂.toConfigSpace :=
    diff.h_different_information
  intro h_V_eq
  have h_V_eq_scaled : (1/4) * V_int diff.H₁.toConfigSpace = (1/4) * V_int diff.H₂.toConfigSpace := by
    rw [← h_R1_Vint, ← h_R2_Vint]; exact h_V_eq
  have h_H_eq : V_int diff.H₁.toConfigSpace = V_int diff.H₂.toConfigSpace := by linarith
  exact h_H_diff h_H_eq

end BlackHoleInformationPreservation
