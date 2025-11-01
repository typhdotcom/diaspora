/-
# D3 + R1: Gauge Invariants and Objectivity

Formalizes the distinction between objective (gauge-invariant) and
perspective-relative (gauge-dependent) properties.

Objectivity = statements about invariants under gauge transformations.
Everything else is perspective-relative.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Diaspora.Axioms
import Diaspora.NoPrivilegedFrame

/-! ## Gauge Invariants -/

/-- The set of all gauge-invariant observables -/
def GaugeInvariants : Set (ConfigSpace → ℝ) :=
  {f | ∀ (g : GaugeTransformation) (X : ConfigSpace), f (g X) = f X}

/-- An observable is objective iff it's gauge-invariant -/
def is_objective (f : ConfigSpace → ℝ) : Prop :=
  f ∈ GaugeInvariants

/-- An observable is perspective-relative iff it's not gauge-invariant -/
def is_perspective_relative (f : ConfigSpace → ℝ) : Prop :=
  ¬is_objective f

/-! ## Basic Properties of Invariants -/

/-- Constant functions are invariant -/
theorem const_is_invariant (c : ℝ) :
    is_objective (fun _ => c) := by
  intro g X
  rfl

/-- Complexity E is gauge-invariant -/
theorem E_is_invariant :
    is_objective (fun X => (E X : ℝ)) := by
  intro g X
  simp [gauge_preserves_structure]

/-- Sum of invariants is invariant -/
theorem sum_invariants_invariant (f₁ f₂ : ConfigSpace → ℝ)
    (h₁ : is_objective f₁) (h₂ : is_objective f₂) :
    is_objective (fun X => f₁ X + f₂ X) := by
  intro g X
  simp [h₁ g X, h₂ g X]

/-- Scalar multiple of invariant is invariant -/
theorem scalar_mult_invariant (f : ConfigSpace → ℝ) (c : ℝ)
    (h : is_objective f) :
    is_objective (fun X => c * f X) := by
  intro g X
  simp [h g X]

/-! ## Structure of Invariants -/

/-- The gauge invariants form a vector space of observables -/
theorem invariants_form_subspace :
    is_objective (fun _ => 0) ∧
    (∀ f₁ f₂, is_objective f₁ → is_objective f₂ →
      is_objective (fun X => f₁ X + f₂ X)) ∧
    (∀ f c, is_objective f → is_objective (fun X => c * f X)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact const_is_invariant 0
  · exact sum_invariants_invariant
  · exact scalar_mult_invariant

/-! ## Objectivity Theorem (R1) -/

/-- A statement is objective iff it only refers to gauge-invariant quantities -/
def objective_statement (P : ConfigSpace → Prop) : Prop :=
  ∀ (g : GaugeTransformation) (X : ConfigSpace), P X ↔ P (g X)

/-- Objective statements are stable across gauge transformations -/
theorem objective_stable (P : ConfigSpace → Prop) (h : objective_statement P) :
    ∀ (g₁ g₂ : GaugeTransformation) (X : ConfigSpace),
    P (g₁ X) ↔ P (g₂ X) := by
  intro g₁ g₂ X
  have h₁ := h g₁ X
  have h₂ := h g₂ X
  constructor
  · intro hp
    have : P X := h₁.2 hp
    exact h₂.1 this
  · intro hp
    have : P X := h₂.2 hp
    exact h₁.1 this

/-- If a property depends on a perspective-relative observable, it's not objective -/
axiom perspective_relative_not_objective (f : ConfigSpace → ℝ)
    (h : is_perspective_relative f)
    (P : ConfigSpace → Prop)
    (h_depends : ∃ X Y, f X ≠ f Y ∧ P X ≠ P Y) :
    ¬objective_statement P

/-! ## Characterization via Invariants -/

/-- The set of gauge-invariant properties forms a σ-algebra -/
axiom invariant_properties_sigma_algebra :
    ∃ (Ω : Set (ConfigSpace → Prop)),
    -- Contains the trivial property
    (fun _ => True) ∈ Ω ∧
    -- Closed under complement
    (∀ P ∈ Ω, (fun X => ¬P X) ∈ Ω) ∧
    -- Closed under countable unions
    (∀ (Ps : ℕ → ConfigSpace → Prop),
      (∀ n, Ps n ∈ Ω) →
      (fun X => ∃ n, Ps n X) ∈ Ω) ∧
    -- Exactly the objective statements
    (∀ P, P ∈ Ω ↔ objective_statement P)

/-! ## Examples: What's Objective vs Perspective-Relative -/

/-- Internal cost V_int is typically perspective-relative -/
axiom V_int_perspective_relative :
    is_perspective_relative V_int

/-- External cost V_ext can be perspective-relative -/
axiom V_ext_can_be_perspective_relative :
    ∃ (gauges : IncommensurableGauges),
    is_perspective_relative gauges.V_ext_X

/-- The Lagrangian at a given λ can vary under gauge transformations -/
axiom lagrangian_objectivity_varies (lam : ℝ) :
    ∃ (g : GaugeTransformation) (X : ConfigSpace),
    ℒ (g X) lam ≠ ℒ X lam

/-! ## The Core Insight: Objectivity as Overlap -/

/-- A quantity is objective iff all gauge-transformed versions agree -/
theorem objectivity_is_unanimous_agreement (f : ConfigSpace → ℝ) :
    is_objective f ↔
    ∀ (X : ConfigSpace) (g₁ g₂ : GaugeTransformation),
    f (g₁ X) = f (g₂ X) := by
  constructor
  · intro hobj X g₁ g₂
    have h₁ : f (g₁ X) = f X := hobj g₁ X
    have h₂ : f (g₂ X) = f X := hobj g₂ X
    exact h₁.trans h₂.symm
  · intro h g X
    have : f (g X) = f (id X) := h X g id
    simp at this
    exact this

/-- Reality (the set of gauge locks) is the maximal objective overlap -/
theorem reality_is_maximal_objective_overlap (lam : ℝ) :
    ∀ X ∈ reality lam,
    ∀ (f : ConfigSpace → ℝ),
    is_objective f →
    (∀ Y ∈ reality lam, f X = f Y) ∨
    (∃ Y ∈ reality lam, f X ≠ f Y) := by
  intro X _ f _
  by_cases h : ∀ Y ∈ reality lam, f X = f Y
  · left; exact h
  · right
    push_neg at h
    exact h

/-! ## Philosophical Translation -/

/-- Objectivity = what all perspectives agree on -/
theorem objectivity_def (f : ConfigSpace → ℝ) :
    is_objective f ↔
    (∀ g : GaugeTransformation, is_invariant f g) := by
  rfl

/-- Everything not objective is perspective-relative -/
theorem perspective_relative_def (f : ConfigSpace → ℝ) :
    is_perspective_relative f ↔
    ∃ (g : GaugeTransformation) (X : ConfigSpace), f (g X) ≠ f X := by
  unfold is_perspective_relative is_objective GaugeInvariants
  simp
