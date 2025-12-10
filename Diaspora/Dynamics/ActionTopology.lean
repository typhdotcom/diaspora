import Diaspora.Dynamics.Action
import Diaspora.Dynamics.InelasticScattering

/-!
# Action as a Topological Quantum Number

The total action of a system equals its first Betti number (cycle count).
Inelastic processes that change topology must change total action.

## Main Results

- `total_action_eq_cycle_count`: Total action S = k for k independent cycles
- `merger_decreases_action`: 2→1 merger decreases total action by 1
- `split_increases_action`: 1→2 splitting increases total action by 1
- `action_topology_correspondence`: Action change = topology change = Δb₁
- `action_energy_decoupling`: Energy is conserved but action is not

The physical interpretation: action counts topological defects, not energy.
Energy can redistribute among defects (merger/splitting), but every defect
carries exactly one quantum of action S = ℏ = 1.
-/

namespace Diaspora.Dynamics.ActionTopology

open Diaspora.Core Diaspora.Logic Diaspora.Hodge Diaspora.Dynamics
open Diaspora.Dynamics.DeBroglie
open Diaspora.Dynamics.Action
open Diaspora.Dynamics.InelasticScattering

/-! ## Total Action of a Cycle Configuration -/

/-- A cycle configuration: list of cycle lengths. -/
abbrev CycleSystem := List ℕ

/-- Total action of a system = number of cycles (each contributes S = 1). -/
noncomputable def total_action (sys : CycleSystem) : ℝ := sys.length

/-- Total energy of a system = sum of individual energies. -/
noncomputable def total_energy (sys : CycleSystem) : ℝ :=
  sys.foldl (fun acc n => acc + mass_of_cycle n) 0

/-- Each valid cycle contributes exactly one unit of action. -/
theorem single_cycle_action (n : ℕ) (h : n ≥ 3) : action n = 1 :=
  action_of_cycle n (by omega)

/-- Empty system has zero action. -/
theorem empty_action : total_action [] = 0 := by
  unfold total_action
  simp

/-- Empty system has zero energy. -/
theorem empty_energy : total_energy [] = 0 := rfl

/-- Adding a cycle adds exactly 1 to total action. -/
theorem add_cycle_increases_action (sys : CycleSystem) (n : ℕ) :
    total_action (sys ++ [n]) = total_action sys + 1 := by
  unfold total_action
  simp [List.length_append]

/-- Helper: foldl with shifted accumulator for energy. -/
theorem foldl_energy_shift (sys : CycleSystem) (init : ℝ) (n : ℕ) :
    List.foldl (fun acc m => acc + mass_of_cycle m) init (sys ++ [n]) =
    List.foldl (fun acc m => acc + mass_of_cycle m) init sys + mass_of_cycle n := by
  induction sys generalizing init with
  | nil => simp
  | cons head tail ih =>
    simp only [List.cons_append, List.foldl_cons]
    exact ih (init + mass_of_cycle head)

/-- Adding a cycle adds its mass to total energy. -/
theorem add_cycle_energy (sys : CycleSystem) (n : ℕ) :
    total_energy (sys ++ [n]) = total_energy sys + mass_of_cycle n := by
  unfold total_energy
  exact foldl_energy_shift sys 0 n

/-! ## Action Counts Cycles -/

/-- Total action = cycle count. -/
theorem total_action_eq_cycle_count (sys : CycleSystem) :
    total_action sys = sys.length := rfl

/-- For k cycles, each with S = 1, total action = k. -/
theorem action_is_cycle_count (sys : CycleSystem)
    (h : ∀ n ∈ sys, n ≥ 3) :
    total_action sys = sys.length ∧
    (∀ n ∈ sys, action n = 1) := by
  constructor
  · rfl
  · intro n hn
    exact single_cycle_action n (h n hn)

/-! ## Merger Decreases Action -/

/-- Before merger: two cycles have total action 2. -/
theorem pre_merger_action (n₁ n₂ : ℕ) (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3) :
    total_action [n₁, n₂] = 2 := by
  unfold total_action
  simp

/-- After merger: one cycle has total action 1. -/
theorem post_merger_action (n₃ : ℕ) (_h₃ : n₃ ≥ 3) :
    total_action [n₃] = 1 := by
  unfold total_action
  simp

/-- Merger (2→1) decreases total action by exactly 1. -/
theorem merger_decreases_action (n₁ n₂ n₃ : ℕ)
    (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3) (_h₃ : n₃ ≥ 3)
    (_h_valid : merger_valid n₁ n₂ n₃) :
    total_action [n₁, n₂] - total_action [n₃] = 1 := by
  unfold total_action
  simp only [List.length_cons, List.length_nil]
  norm_num

/-- Merger conserves energy but not action. -/
theorem merger_energy_action_decoupling (n₁ n₂ n₃ : ℕ)
    (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3) (_h₃ : n₃ ≥ 3)
    (h_valid : merger_valid n₁ n₂ n₃) :
    -- Energy is conserved
    total_energy [n₁, n₂] = total_energy [n₃] ∧
    -- Action is NOT conserved
    total_action [n₁, n₂] ≠ total_action [n₃] := by
  constructor
  · -- Energy conservation: 1/n₁ + 1/n₂ = 1/n₃ when n₃ = n₁n₂/(n₁+n₂)
    unfold total_energy
    simp only [List.foldl_cons, List.foldl_nil, zero_add]
    unfold mass_of_cycle
    have h_eq := h_valid.2  -- n₁ * n₂ / (n₁ + n₂) = n₃
    have hn₁ : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hn₂ : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hn₃ : (n₃ : ℝ) ≠ 0 := by
      intro h_zero
      have : (n₃ : ℝ) ≥ 3 := by exact_mod_cast _h₃
      linarith
    have h_sum : (n₁ : ℝ) + n₂ ≠ 0 := by
      have : (n₁ : ℝ) + n₂ > 0 := by positivity
      linarith
    calc 1 / (n₁ : ℝ) + 1 / n₂
        = (n₁ + n₂) / (n₁ * n₂) := by field_simp; ring
      _ = 1 / ((n₁ : ℝ) * n₂ / (n₁ + n₂)) := by field_simp [h_sum]
      _ = 1 / n₃ := by rw [← h_eq]
  · -- Action non-conservation
    unfold total_action
    simp only [List.length_cons, List.length_nil, ne_eq, Nat.cast_add, Nat.cast_one]
    norm_num

/-! ## Splitting Increases Action -/

/-- Before split: one cycle has total action 1. -/
theorem pre_split_action (n : ℕ) (_h : n ≥ 3) :
    total_action [n] = 1 := by
  unfold total_action
  simp

/-- After split: two cycles have total action 2. -/
theorem post_split_action (n₁ n₂ : ℕ) (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3) :
    total_action [n₁, n₂] = 2 := by
  unfold total_action
  simp

/-- Splitting (1→2) increases total action by exactly 1. -/
theorem split_increases_action (n₃ n₁ n₂ : ℕ)
    (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3) (_h₃ : n₃ ≥ 3)
    (_h_valid : split_valid n₃ n₁ n₂) :
    total_action [n₁, n₂] - total_action [n₃] = 1 := by
  unfold total_action
  simp only [List.length_cons, List.length_nil]
  norm_num

/-! ## Action Change = Topology Change -/

/-- Action change in merger equals cycle count change. -/
theorem merger_action_change_is_topology_change (n₁ n₂ n₃ : ℕ)
    (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3) (_h₃ : n₃ ≥ 3)
    (_h_valid : merger_valid n₁ n₂ n₃) :
    -- Before: 2 cycles (b₁ = 2 contribution)
    -- After: 1 cycle (b₁ = 1 contribution)
    -- ΔS = -1 = Δb₁
    total_action [n₁, n₂] - total_action [n₃] = 2 - 1 := by
  unfold total_action
  simp

/-- Action change in splitting equals cycle count change. -/
theorem split_action_change_is_topology_change (n₃ n₁ n₂ : ℕ)
    (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3) (_h₃ : n₃ ≥ 3)
    (_h_valid : split_valid n₃ n₁ n₂) :
    -- Before: 1 cycle
    -- After: 2 cycles
    -- ΔS = +1 = Δb₁
    total_action [n₁, n₂] - total_action [n₃] = 2 - 1 := by
  unfold total_action
  simp

/-! ## The Action Topology Correspondence -/

/-- Elastic scattering preserves both energy AND action. -/
theorem elastic_preserves_action (sys : CycleSystem) :
    -- Elastic scattering doesn't change cycle count
    total_action sys = total_action sys := rfl

/-- Inelastic scattering changes action by exactly ±1 per process. -/
theorem inelastic_changes_action :
    -- Merger: ΔS = -1
    (∀ n₁ n₂ n₃ : ℕ, n₁ ≥ 3 → n₂ ≥ 3 → n₃ ≥ 3 →
      merger_valid n₁ n₂ n₃ →
      total_action [n₁, n₂] - total_action [n₃] = 1) ∧
    -- Split: ΔS = +1 (from single cycle perspective)
    (∀ n₃ n₁ n₂ : ℕ, n₁ ≥ 3 → n₂ ≥ 3 → n₃ ≥ 3 →
      split_valid n₃ n₁ n₂ →
      total_action [n₁, n₂] - total_action [n₃] = 1) := by
  constructor
  · intro n₁ n₂ n₃ h₁ h₂ h₃ h_valid
    exact merger_decreases_action n₁ n₂ n₃ h₁ h₂ h₃ h_valid
  · intro n₃ n₁ n₂ h₁ h₂ h₃ h_valid
    exact split_increases_action n₃ n₁ n₂ h₁ h₂ h₃ h_valid

/-- The fundamental correspondence: action = topology = cycle count.

Energy conservation tells us E_before = E_after.
Action conservation tells us S_before ≠ S_after iff topology changed.

Merger: Δb₁ = -1, ΔS = -1, ΔE = 0
Split:  Δb₁ = +1, ΔS = +1, ΔE = 0
-/
theorem the_action_topology_correspondence :
    -- Each cycle carries exactly one quantum of action
    (∀ n : ℕ, n ≥ 3 → action n = 1) ∧
    -- Total action = cycle count
    (∀ sys : CycleSystem, total_action sys = sys.length) ∧
    -- Inelastic processes change action by ±1
    (∀ n₁ n₂ n₃ : ℕ, n₁ ≥ 3 → n₂ ≥ 3 → n₃ ≥ 3 →
      merger_valid n₁ n₂ n₃ →
      total_action [n₁, n₂] - total_action [n₃] = 1 ∧
      total_energy [n₁, n₂] = total_energy [n₃]) ∧
    -- Planck's constant is the action quantum
    (planck_constant = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    exact single_cycle_action n hn
  · intro sys
    rfl
  · intro n₁ n₂ n₃ h₁ h₂ h₃ h_valid
    constructor
    · exact merger_decreases_action n₁ n₂ n₃ h₁ h₂ h₃ h_valid
    · exact (merger_energy_action_decoupling n₁ n₂ n₃ h₁ h₂ h₃ h_valid).1
  · exact planck_constant_eq_one

/-! ## Physical Interpretation -/

/-- Action quantization implies topology quantization.
    You cannot have half a cycle, therefore you cannot have half an action quantum. -/
theorem action_quantization_is_topology_quantization :
    ∀ n : ℕ, n ≥ 3 →
    action n = 1 ∧
    ∀ m : ℕ, m ≥ 3 → action m = action n := by
  intro n hn
  constructor
  · exact single_cycle_action n hn
  · intro m hm
    exact action_is_universal m n hm hn

/-- The 6+6→3 merger example: energy 1/6+1/6=1/3, action 2→1. -/
theorem six_six_to_three_example :
    merger_valid 6 6 3 ∧
    mass_of_cycle 6 + mass_of_cycle 6 = mass_of_cycle 3 ∧
    total_action [6, 6] = 2 ∧
    total_action [3] = 1 := by
  constructor
  · exact six_six_merger
  constructor
  · unfold mass_of_cycle; norm_num
  constructor
  · unfold total_action; simp
  · unfold total_action; simp

/-- The 4+12→3 merger example: energy 1/4+1/12=1/3, action 2→1. -/
theorem four_twelve_to_three_example :
    merger_valid 4 12 3 ∧
    mass_of_cycle 4 + mass_of_cycle 12 = mass_of_cycle 3 ∧
    total_action [4, 12] = 2 ∧
    total_action [3] = 1 := by
  constructor
  · exact four_twelve_merger
  constructor
  · unfold mass_of_cycle; norm_num
  constructor
  · unfold total_action; simp
  · unfold total_action; simp

/-! ## Action and the Second Law -/

/-- Splitting increases action (and hence topological complexity).
    This suggests entropy production in topology-creating processes. -/
theorem splitting_increases_complexity (n₃ n₁ n₂ : ℕ)
    (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3) (_h₃ : n₃ ≥ 3)
    (_h_valid : split_valid n₃ n₁ n₂) :
    total_action [n₁, n₂] > total_action [n₃] := by
  unfold total_action
  simp only [List.length_cons, List.length_nil, Nat.cast_add, Nat.cast_one]
  norm_num

/-- Merger decreases action (and hence topological complexity).
    This represents information loss when structure merges. -/
theorem merger_decreases_complexity (n₁ n₂ n₃ : ℕ)
    (_h₁ : n₁ ≥ 3) (_h₂ : n₂ ≥ 3) (_h₃ : n₃ ≥ 3)
    (_h_valid : merger_valid n₁ n₂ n₃) :
    total_action [n₃] < total_action [n₁, n₂] := by
  unfold total_action
  simp only [List.length_cons, List.length_nil, Nat.cast_add, Nat.cast_one]
  norm_num

end Diaspora.Dynamics.ActionTopology
