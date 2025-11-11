/-
Gauge Negotiation: Explicit Arithmetic

Explicit computation of V_int for each graph by writing out every edge.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Diaspora.GaugeNegotiationVerified

namespace Diaspora.GaugeNegotiationExplicit

open GaugeNegotiationVerified

/-! ## Explicit V_int -/
def edge_cost (i j : Fin 8) (phases : Fin 8 → ℝ) : ℝ :=
  let edge_val := phases j - phases i
  let violation := edge_val - C_initial i j
  violation ^ 2
def V_int_G_N_explicit : ℝ :=
  edge_cost 0 1 phases_G_N +
  edge_cost 0 2 phases_G_N +
  edge_cost 0 3 phases_G_N +
  edge_cost 0 5 phases_G_N +
  edge_cost 0 6 phases_G_N +
  edge_cost 1 2 phases_G_N +
  edge_cost 1 3 phases_G_N +
  edge_cost 1 4 phases_G_N +
  edge_cost 1 6 phases_G_N +
  edge_cost 1 7 phases_G_N +
  edge_cost 2 0 phases_G_N +
  edge_cost 2 7 phases_G_N +
  edge_cost 3 0 phases_G_N +
  edge_cost 3 1 phases_G_N +
  edge_cost 3 2 phases_G_N +
  edge_cost 3 6 phases_G_N +
  edge_cost 3 7 phases_G_N +
  edge_cost 4 3 phases_G_N +
  edge_cost 5 0 phases_G_N +
  edge_cost 5 2 phases_G_N +
  edge_cost 5 4 phases_G_N +
  edge_cost 6 0 phases_G_N +
  edge_cost 6 2 phases_G_N +
  edge_cost 6 3 phases_G_N +
  edge_cost 6 4 phases_G_N +
  edge_cost 6 5 phases_G_N +
  edge_cost 6 7 phases_G_N +
  edge_cost 7 0 phases_G_N +
  edge_cost 7 2 phases_G_N +
  edge_cost 7 3 phases_G_N +
  edge_cost 7 4 phases_G_N
def V_int_G_A_explicit : ℝ :=
  edge_cost 0 1 phases_G_A +
  edge_cost 0 2 phases_G_A +
  edge_cost 0 6 phases_G_A +
  edge_cost 1 2 phases_G_A +
  edge_cost 1 6 phases_G_A +
  edge_cost 2 0 phases_G_A +
  edge_cost 2 3 phases_G_A +
  edge_cost 2 6 phases_G_A +
  edge_cost 4 1 phases_G_A +
  edge_cost 4 2 phases_G_A +
  edge_cost 4 6 phases_G_A +
  edge_cost 4 7 phases_G_A +
  edge_cost 5 1 phases_G_A +
  edge_cost 5 2 phases_G_A +
  edge_cost 6 1 phases_G_A +
  edge_cost 6 3 phases_G_A +
  edge_cost 6 7 phases_G_A +
  edge_cost 7 0 phases_G_A +
  edge_cost 7 2 phases_G_A
def V_int_G_B_explicit : ℝ :=
  edge_cost 0 1 phases_G_B +
  edge_cost 0 2 phases_G_B +
  edge_cost 0 3 phases_G_B +
  edge_cost 0 5 phases_G_B +
  edge_cost 0 6 phases_G_B +
  edge_cost 1 2 phases_G_B +
  edge_cost 1 3 phases_G_B +
  edge_cost 1 4 phases_G_B +
  edge_cost 1 6 phases_G_B +
  edge_cost 1 7 phases_G_B +
  edge_cost 2 0 phases_G_B +
  edge_cost 2 7 phases_G_B +
  edge_cost 3 1 phases_G_B +
  edge_cost 3 2 phases_G_B +
  edge_cost 3 6 phases_G_B +
  edge_cost 3 7 phases_G_B +
  edge_cost 4 3 phases_G_B +
  edge_cost 5 0 phases_G_B +
  edge_cost 5 1 phases_G_B +
  edge_cost 5 2 phases_G_B +
  edge_cost 5 4 phases_G_B +
  edge_cost 6 0 phases_G_B +
  edge_cost 6 2 phases_G_B +
  edge_cost 6 3 phases_G_B +
  edge_cost 6 4 phases_G_B +
  edge_cost 6 5 phases_G_B +
  edge_cost 6 7 phases_G_B +
  edge_cost 7 0 phases_G_B +
  edge_cost 7 2 phases_G_B +
  edge_cost 7 3 phases_G_B +
  edge_cost 7 4 phases_G_B +
  edge_cost 7 5 phases_G_B
def V_int_G_Union_explicit : ℝ :=
  edge_cost 0 1 phases_G_Union +
  edge_cost 0 2 phases_G_Union +
  edge_cost 0 3 phases_G_Union +
  edge_cost 0 5 phases_G_Union +
  edge_cost 0 6 phases_G_Union +
  edge_cost 1 2 phases_G_Union +
  edge_cost 1 3 phases_G_Union +
  edge_cost 1 4 phases_G_Union +
  edge_cost 1 5 phases_G_Union +
  edge_cost 1 6 phases_G_Union +
  edge_cost 1 7 phases_G_Union +
  edge_cost 2 0 phases_G_Union +
  edge_cost 2 1 phases_G_Union +
  edge_cost 2 3 phases_G_Union +
  edge_cost 2 5 phases_G_Union +
  edge_cost 2 6 phases_G_Union +
  edge_cost 2 7 phases_G_Union +
  edge_cost 3 0 phases_G_Union +
  edge_cost 3 1 phases_G_Union +
  edge_cost 3 2 phases_G_Union +
  edge_cost 3 4 phases_G_Union +
  edge_cost 3 6 phases_G_Union +
  edge_cost 3 7 phases_G_Union +
  edge_cost 4 0 phases_G_Union +
  edge_cost 4 2 phases_G_Union +
  edge_cost 4 3 phases_G_Union +
  edge_cost 4 6 phases_G_Union +
  edge_cost 4 7 phases_G_Union +
  edge_cost 5 1 phases_G_Union +
  edge_cost 5 2 phases_G_Union +
  edge_cost 5 3 phases_G_Union +
  edge_cost 5 4 phases_G_Union +
  edge_cost 5 7 phases_G_Union +
  edge_cost 6 0 phases_G_Union +
  edge_cost 6 1 phases_G_Union +
  edge_cost 6 2 phases_G_Union +
  edge_cost 6 3 phases_G_Union +
  edge_cost 6 4 phases_G_Union +
  edge_cost 6 5 phases_G_Union +
  edge_cost 6 7 phases_G_Union +
  edge_cost 7 0 phases_G_Union +
  edge_cost 7 2 phases_G_Union +
  edge_cost 7 3 phases_G_Union +
  edge_cost 7 4 phases_G_Union +
  edge_cost 7 5 phases_G_Union +
  edge_cost 7 6 phases_G_Union
def L_N_explicit : ℝ := V_int_G_N_explicit + V_ext_G_N + 31
def L_A_explicit : ℝ := V_int_G_A_explicit + V_ext_G_A + 19
def L_B_explicit : ℝ := V_int_G_B_explicit + V_ext_G_B + 32
def L_Union_explicit : ℝ := V_int_G_Union_explicit + V_ext_G_Union + 39

/-! ## Proofs -/

theorem negotiation_beats_A_explicit : L_N_explicit < L_A_explicit := by
  unfold L_N_explicit L_A_explicit
  unfold V_int_G_N_explicit V_int_G_A_explicit
  unfold edge_cost
  unfold V_ext_G_N V_ext_G_A V_ext pi_over_2 pi_over_4
  unfold phases_G_N phases_G_A C_initial
  norm_num

theorem negotiation_beats_B_explicit : L_N_explicit < L_B_explicit := by
  unfold L_N_explicit L_B_explicit
  unfold V_int_G_N_explicit V_int_G_B_explicit
  unfold edge_cost
  unfold V_ext_G_N V_ext_G_B V_ext pi_over_2 pi_over_4
  unfold phases_G_N phases_G_B C_initial
  norm_num

theorem negotiation_beats_Union_explicit : L_N_explicit < L_Union_explicit := by
  unfold L_N_explicit L_Union_explicit
  unfold V_int_G_N_explicit V_int_G_Union_explicit
  unfold edge_cost
  unfold V_ext_G_N V_ext_G_Union V_ext pi_over_2 pi_over_4
  unfold phases_G_N phases_G_Union C_initial
  norm_num

theorem gauge_negotiation_verified :
    L_N_explicit < L_A_explicit ∧
    L_N_explicit < L_B_explicit ∧
    L_N_explicit < L_Union_explicit := by
  exact ⟨negotiation_beats_A_explicit, negotiation_beats_B_explicit,
         negotiation_beats_Union_explicit⟩

end Diaspora.GaugeNegotiationExplicit
