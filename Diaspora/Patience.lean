/-
# Patience Saves the Universe

Temperature in Diaspora = τ_relax / τ_break

This file proves that "False Vacua" are artifacts of non-adiabatic evolution:
breaking edges faster than potentials can relax.

When the system is allowed to relax (T → 0, adiabatic limit), the harmonic
component γ correctly identifies the globally optimal edge to break.
-/

import Diaspora.FalseVacuum
import Diaspora.MetricDeception

namespace DiscreteHodge

open BigOperators

/--
When potentials relax to their optimal configuration before evaluating stress,
the strain profile inverts, identifying edge (1,3) as the weak point.
-/
theorem patience_saves_the_universe :
  let σ := trap_sigma
  let ϕ_relaxed := trap_phi
  let strain_trap := edge_strain ϕ_relaxed σ 1 2
  let strain_smart := edge_strain ϕ_relaxed σ 1 3
  strain_smart > strain_trap := by
  unfold edge_strain trap_phi trap_sigma d0
  simp
  norm_num

/--
Without relaxation: edge (1,2) has higher strain.
With relaxation: edge (1,3) has higher strain.
-/
theorem strain_reversal :
  let σ := trap_sigma
  let ϕ_zero : C0 n_theta := fun _ => 0
  let ϕ_opt := trap_phi
  (edge_strain ϕ_zero σ 1 2 > edge_strain ϕ_zero σ 1 3) ∧
  (edge_strain ϕ_opt σ 1 3 > edge_strain ϕ_opt σ 1 2) := by
  constructor
  · unfold edge_strain trap_sigma d0
    simp
    norm_num
  · exact patience_saves_the_universe

/--
At α = 4/19, both edges have equal strain.
-/
theorem temperature_crossover :
  let σ := trap_sigma
  let α := (4:ℝ)/19
  let ϕ_partial := fun i => α * trap_phi i
  edge_strain ϕ_partial σ 1 2 = edge_strain ϕ_partial σ 1 3 := by
  unfold edge_strain trap_sigma trap_phi d0
  simp
  norm_num

end DiscreteHodge
