/-
Gauge Negotiation: Proofs

Bridges concrete 8-node examples to general theorems.
-/

import Diaspora.GaugeNegotiationVerified
import Diaspora.GaugeNegotiationExplicit

namespace Diaspora.GaugeNegotiationProofs

open GaugeNegotiationVerified
open GaugeNegotiationExplicit

/-! ## Edge Count Verification -/

/-- G_A has 20 edges -/
theorem G_A_edge_count : G_A.edgeCount = 20 := by
  decide

/-- G_B has 37 edges -/
theorem G_B_edge_count : G_B.edgeCount = 37 := by
  decide

/-- G_N has 34 edges -/
theorem G_N_edge_count : G_N.edgeCount = 34 := by
  decide

/-- G_Union has 43 edges -/
theorem G_Union_edge_count : G_Union.edgeCount = 43 := by
  decide

/-! ## Novelty -/

theorem G_N_ne_G_A : G_N ≠ G_A := by
  intro h
  have h_count : G_N.edgeCount = G_A.edgeCount := by rw [h]
  rw [G_N_edge_count, G_A_edge_count] at h_count
  norm_num at h_count

theorem G_N_ne_G_B : G_N ≠ G_B := by
  intro h
  have h_count : G_N.edgeCount = G_B.edgeCount := by rw [h]
  rw [G_N_edge_count, G_B_edge_count] at h_count
  norm_num at h_count
theorem negotiation_creates_novelty_concrete :
    G_N ≠ G_A ∧ G_N ≠ G_B :=
  ⟨G_N_ne_G_A, G_N_ne_G_B⟩

/-! ## Intermediate Complexity -/

theorem negotiation_intermediate_complexity_concrete :
    min G_A.edgeCount G_B.edgeCount ≤ G_N.edgeCount ∧
    G_N.edgeCount ≤ G_A.edgeCount + G_B.edgeCount := by
  constructor
  · rw [G_A_edge_count, G_B_edge_count, G_N_edge_count]
    norm_num
  · rw [G_A_edge_count, G_B_edge_count, G_N_edge_count]
    norm_num

/-! ## Convergence -/
theorem G_N_is_local_minimum :
    L_N_explicit < L_A_explicit ∧
    L_N_explicit < L_B_explicit ∧
    L_N_explicit < L_Union_explicit :=
  ⟨negotiation_beats_A_explicit,
   negotiation_beats_B_explicit,
   negotiation_beats_Union_explicit⟩

end Diaspora.GaugeNegotiationProofs
