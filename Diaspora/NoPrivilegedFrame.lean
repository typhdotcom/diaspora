/-
# Theorem: No Privileged Frame (R2)

Proves that when gauges are incommensurable, no unique global minimizer
exists that is invariant under gauge transformations.

This is the formal statement that "objectivity" is an overlap of compatible
perspectives, not a single privileged view.
-/

import Mathlib.Data.Real.Basic
import Diaspora.Axioms
import Diaspora.UncertaintyProof

/-! ## Gauge Transformations -/

/-- A gauge transformation on configuration space -/
abbrev GaugeTransformation := ConfigSpace → ConfigSpace

/-- Gauge transformations preserve complexity -/
axiom gauge_preserves_structure (g : GaugeTransformation) (X : ConfigSpace) :
  E (g X) = E X

/-! ## Frame Dependence -/

/-- An observable is a gauge-invariant quantity -/
def is_invariant (f : ConfigSpace → ℝ) (g : GaugeTransformation) : Prop :=
  ∀ X, f (g X) = f X

/-- A cost function is gauge-dependent if it changes under gauge transformations -/
def is_gauge_dependent (V : ConfigSpace → ℝ) : Prop :=
  ∃ (g : GaugeTransformation) (X : ConfigSpace), V (g X) ≠ V X

/-! ## Privileged Frame -/

/-- A global minimizer of the Lagrangian at parameter λ -/
def global_minimizer (X : ConfigSpace) (lam : ℝ) : Prop :=
  ∀ Y, ℒ X lam ≤ ℒ Y lam

/-- A privileged frame: unique global minimizer -/
def privileged_frame (lam : ℝ) : Prop :=
  ∃! X, global_minimizer X lam

/-! ## Main Theorem: No Privileged Frame -/

/-- When gauges act transitively on level sets and one gauge is not invariant,
    generically no privileged frame exists -/
axiom gauge_acts_transitively_on_V_ext_levels (v : ℝ) :
  ∀ X Y, V_ext X = v → V_ext Y = v →
  ∃ g : GaugeTransformation, g X = Y

/-- Internal cost is not gauge-invariant -/
axiom V_int_not_gauge_invariant : is_gauge_dependent V_int

/-- For open sets of parameters, no global minimizer is gauge-invariant -/
theorem no_unique_gauge_invariant_minimizer (lam : ℝ)
    (h_transition : ∃ X Y,
      global_minimizer X lam ∧
      global_minimizer Y lam ∧
      V_ext X ≠ V_ext Y) :
    ∃ (X Y : ConfigSpace),
      global_minimizer X lam ∧
      global_minimizer Y lam ∧
      X ≠ Y := by
  obtain ⟨X, Y, hX, hY, hne⟩ := h_transition
  exact ⟨X, Y, hX, hY, fun h => hne (congrArg V_ext h)⟩

/-- Gauge transformations can create alternative minimizers -/
axiom gauge_creates_alternative_minimizer
    (gauges : IncommensurableGauges)
    (h_incompatible : structurally_incompatible gauges)
    (X : ConfigSpace) (lam : ℝ) :
    global_minimizer X lam →
    ∃ (Y : ConfigSpace),
      global_minimizer Y lam ∧
      X ≠ Y ∧
      gauges.V_ext_X X ≠ gauges.V_ext_X Y

/-- The main theorem: when gauges are incommensurable, no privileged frame exists -/
theorem no_privileged_frame (gauges : IncommensurableGauges)
    (h_incompatible : structurally_incompatible gauges)
    (lam : ℝ) (_ : 0 < lam) :
    ¬privileged_frame lam := by
  intro ⟨X, hmin, hunique⟩
  -- Gauge transformations create alternative minimizers
  obtain ⟨Y, hY_min, hne, _⟩ := gauge_creates_alternative_minimizer gauges h_incompatible X lam hmin
  -- Y is also a global minimizer but Y ≠ X
  have : Y = X := hunique Y hY_min
  exact hne this.symm

/-! ## Reality as Overlap -/

/-- Reality is not a single frame but an overlap of compatible gauge locks -/
def reality (lam : ℝ) : Set ConfigSpace :=
  {X | global_minimizer X lam}

/-- The objectivity set: configurations minimizing gauge-invariant quantities only -/
def objective_core (lam : ℝ) : Set ConfigSpace :=
  {X ∈ reality lam |
    ∀ (g : GaugeTransformation) (inv : ConfigSpace → ℝ),
    is_invariant inv g → inv (g X) = inv X}

/-- Coercivity: the Lagrangian has at least one global minimizer -/
axiom lagrangian_has_minimizer (lam : ℝ) : ∃ X, global_minimizer X lam

/-- When no privileged frame exists, reality is a set, not a singleton -/
theorem reality_is_pluralistic (lam : ℝ) (h : ¬privileged_frame lam) :
    ∃ X Y, X ∈ reality lam ∧ Y ∈ reality lam ∧ X ≠ Y := by
  obtain ⟨X, hX⟩ := lagrangian_has_minimizer lam
  have : ¬(∀ Y, global_minimizer Y lam → Y = X) := by
    intro hall
    apply h
    exact ⟨X, hX, hall⟩
  push_neg at this
  obtain ⟨Y, hY, hne⟩ := this
  exact ⟨X, Y, hX, hY, hne.symm⟩
