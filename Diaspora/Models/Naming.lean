import Diaspora.Core.Calculus
import Diaspora.Hodge.Decomposition
import Diaspora.Logic.Classicality.Basic
import Diaspora.Logic.Limit
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Models/Naming.lean: Topological Indistinguishability and Symmetry Breaking

This file models the distinction between hypothetical external stimuli and
internal references to them.

"Naming" is modeled as the creation of an internal "symbol" node and an edge
connecting it to a specific external node. This action creates a cycle.

We prove:
1. **Pre-naming symmetry**: An automorphism exists swapping the stimuli.
2. **Post-naming asymmetry**: Adding the "naming" link breaks the symmetry
   (different vertex degrees) and creates non-trivial harmonic content.
-/

namespace Diaspora.Models.Naming

open Diaspora.Core Diaspora.Hodge Diaspora.Logic

-------------------------------------------------------------------------------
-- Section 1: The Pre-Naming State (Star Graph)
-------------------------------------------------------------------------------

abbrev V_pre := Fin 3
def P : V_pre := 0
def S1 : V_pre := 1
def S2 : V_pre := 2

/-- Star graph: P connected to both S1 and S2. -/
def G_pre : DynamicGraph 3 where
  active_edges := {(0, 1), (1, 0), (0, 2), (2, 0)}
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> decide
  no_loops := by intro i; fin_cases i <;> decide

/-- The kernel of d_G for the star graph is 1-dimensional (constant functions). -/
lemma G_pre_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear G_pre)) = 1 := by
  let one : Fin 3 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear G_pre) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G G_pre one).val.val i j = 0
    unfold d_G one
    simp only [G_pre, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear G_pre) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      -- In a star graph, edge (0,1) connects center to leaf 1
      -- and edge (0,2) connects center to leaf 2
      -- If dφ = 0, then φ(1) = φ(0) and φ(2) = φ(0)
      have h1 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ G_pre.active_edges := by simp [G_pre]
        have h_zero : (d_G G_pre φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero
        simp only [h_edge, ↓reduceIte] at h_zero
        linarith
      have h2 : φ 2 = φ 0 := by
        have h_edge : (0, 2) ∈ G_pre.active_edges := by simp [G_pre]
        have h_zero : (d_G G_pre φ).val.val 0 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 2
          exact this
        unfold d_G at h_zero
        simp only [h_edge, ↓reduceIte] at h_zero
        linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h1, h2]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- The pre-naming graph has trivial harmonic subspace. -/
theorem G_pre_is_classical : IsClassical G_pre := by
  unfold IsClassical
  have h_dim := harmonic_dimension_eq_cyclomatic G_pre
  have h_edges : G_pre.active_edges.card / 2 = 2 := by native_decide
  rw [h_edges, G_pre_kernel_dim] at h_dim
  omega

/-- The swap map that exchanges S1 and S2 fixing P. -/
def swap_stimuli : Equiv.Perm V_pre := Equiv.swap S1 S2

/-- The swap map is a valid graph automorphism. -/
theorem swap_is_automorphism :
    ∀ (u v : V_pre), (u, v) ∈ G_pre.active_edges ↔
                     (swap_stimuli u, swap_stimuli v) ∈ G_pre.active_edges := by
  intro u v
  simp only [G_pre, swap_stimuli, S1, S2, Equiv.swap_apply_def]
  fin_cases u <;> fin_cases v <;> decide

-------------------------------------------------------------------------------
-- Section 2: The Naming Action (Adds a Cycle)
-------------------------------------------------------------------------------

abbrev V_named := Fin 4
def P' : V_named := 0
def M' : V_named := 1
def S1' : V_named := 2
def S2' : V_named := 3

/-- Named graph: P-M-S1 forms a cycle, S2 is a pendant vertex. -/
def G_named : DynamicGraph 4 where
  active_edges := {(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0), (1, 2), (2, 1)}
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> decide
  no_loops := by intro i; fin_cases i <;> decide

/-- The kernel of d_G for the named graph is 1-dimensional. -/
lemma G_named_kernel_dim : Module.finrank ℝ (LinearMap.ker (d_G_linear G_named)) = 1 := by
  let one : Fin 4 → ℝ := fun _ => 1
  have h_one_in_ker : one ∈ LinearMap.ker (d_G_linear G_named) := by
    rw [LinearMap.mem_ker]
    ext i j
    show (d_G G_named one).val.val i j = 0
    unfold d_G one
    simp only [G_named, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    split_ifs <;> ring
  have h_ker_eq_span : LinearMap.ker (d_G_linear G_named) = Submodule.span ℝ {one} := by
    apply le_antisymm
    · intro φ h_ker
      rw [LinearMap.mem_ker] at h_ker
      -- Use edges to show φ is constant
      have h_01 : φ 1 = φ 0 := by
        have h_edge : (0, 1) ∈ G_named.active_edges := by simp [G_named]
        have h_zero : (d_G G_named φ).val.val 0 1 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 1
          exact this
        unfold d_G at h_zero
        simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h_02 : φ 2 = φ 0 := by
        have h_edge : (0, 2) ∈ G_named.active_edges := by simp [G_named]
        have h_zero : (d_G G_named φ).val.val 0 2 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 2
          exact this
        unfold d_G at h_zero
        simp only [h_edge, ↓reduceIte] at h_zero; linarith
      have h_03 : φ 3 = φ 0 := by
        have h_edge : (0, 3) ∈ G_named.active_edges := by simp [G_named]
        have h_zero : (d_G G_named φ).val.val 0 3 = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val h_ker)) 0 3
          exact this
        unfold d_G at h_zero
        simp only [h_edge, ↓reduceIte] at h_zero; linarith
      rw [Submodule.mem_span_singleton]
      use φ 0
      ext i; fin_cases i <;> simp [one, h_01, h_02, h_03]
    · rw [Submodule.span_singleton_le_iff_mem]; exact h_one_in_ker
  rw [h_ker_eq_span, finrank_span_singleton]
  intro h; have : (1 : ℝ) = 0 := congr_fun h 0; norm_num at this

/-- The naming action creates exactly one cycle. Betti number = 1. -/
theorem G_named_betti_one : Limit.bettiOne G_named = 1 := by
  unfold Limit.bettiOne
  have h_dim := harmonic_dimension_eq_cyclomatic G_named
  have h_edges : G_named.active_edges.card / 2 = 4 := by native_decide
  rw [h_edges, G_named_kernel_dim] at h_dim
  omega

-------------------------------------------------------------------------------
-- Section 3: Post-Naming Asymmetry
-------------------------------------------------------------------------------

/-- S1' has 2 outgoing edges in G_named. -/
theorem degree_S1_eq_two : (G_named.active_edges.filter (fun p => p.1 = S1')).card = 2 := by
  native_decide

/-- S2' has 1 outgoing edge in G_named. -/
theorem degree_S2_eq_one : (G_named.active_edges.filter (fun p => p.1 = S2')).card = 1 := by
  native_decide

/-- The stimuli are distinguishable: no degree-preserving automorphism can swap them. -/
theorem stimuli_are_distinguishable
    (φ : Equiv.Perm V_named)
    (h_auto : ∀ u v, (u, v) ∈ G_named.active_edges ↔ (φ u, φ v) ∈ G_named.active_edges)
    (_h_fix_P : φ P' = P')
    (_h_fix_M : φ M' = M') :
    φ S1' ≠ S2' := by
  intro h_swap
  -- Automorphisms preserve out-degree (count of edges from a vertex)
  have h_deg_pres : (G_named.active_edges.filter (fun p => p.1 = S1')).card =
                    (G_named.active_edges.filter (fun p => p.1 = φ S1')).card := by
    apply Finset.card_bij (fun p _ => (φ p.1, φ p.2))
    · intro ⟨a, b⟩ h
      simp only [Finset.mem_filter] at h ⊢
      exact ⟨(h_auto a b).mp h.1, by rw [h.2]⟩
    · intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (φ.injective h.1) (φ.injective h.2)
    · intro ⟨a, b⟩ h
      simp only [Finset.mem_filter] at h
      refine ⟨(φ.symm a, φ.symm b), ?_, ?_⟩
      · simp only [Finset.mem_filter]
        refine ⟨(h_auto _ _).mpr (by simp [h.1]), ?_⟩
        calc φ.symm a = φ.symm (φ S1') := by rw [h.2]
             _ = S1' := φ.symm_apply_apply _
      · simp only [Equiv.apply_symm_apply]
  rw [h_swap, degree_S1_eq_two, degree_S2_eq_one] at h_deg_pres
  omega

/-- Hodge interpretation: A harmonic form exists that distinguishes S1 from S2. -/
theorem exists_harmonic_discriminator :
    ∃ γ : HarmonicSubspace G_named,
    (γ.val.val.val M' S1' ≠ 0) ∧
    (∀ v, γ.val.val.val S2' v = 0) := by
  -- Dehn twist on cycle P(0)-M(1)-S1(2)-P: value 1/3 on forward edges
  let γ_val : C1 4 := {
    val := fun i j =>
      if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then 1/3
      else if (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 1) ∨ (i = 0 ∧ j = 2) then -1/3
      else 0
    skew := by intro i j; fin_cases i <;> fin_cases j <;> simp <;> norm_num
  }
  have h_active : ∀ i j, (i, j) ∉ G_named.active_edges → γ_val.val i j = 0 := by
    intro i j h_not
    simp only [G_named, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or] at h_not
    fin_cases i <;> fin_cases j <;> simp_all [γ_val]
  let γ_active : ActiveForm G_named := ⟨γ_val, h_active⟩
  have h_harm : γ_active ∈ HarmonicSubspace G_named := by
    rw [HarmonicSubspace, Submodule.mem_orthogonal]
    intro dφ h_dφ
    rw [ImGradient, LinearMap.mem_range] at h_dφ
    obtain ⟨φ, rfl⟩ := h_dφ
    -- Inner product ⟨dφ, γ⟩ = 0 by Stokes: cycle sum telescopes
    show Diaspora.Core.ActiveForm.inner (d_G_linear G_named φ) γ_active = 0
    unfold Diaspora.Core.ActiveForm.inner inner_product_C1
    rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four,
        Fin.sum_univ_four, Fin.sum_univ_four]
    simp only [d_G_linear, d_G, LinearMap.coe_mk, AddHom.coe_mk, γ_active, γ_val, G_named,
               Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    simp only [show (0 : Fin 4) = 1 ↔ False by decide, show (0 : Fin 4) = 2 ↔ False by decide,
               show (0 : Fin 4) = 3 ↔ False by decide, show (1 : Fin 4) = 0 ↔ False by decide,
               show (1 : Fin 4) = 2 ↔ False by decide, show (1 : Fin 4) = 3 ↔ False by decide,
               show (2 : Fin 4) = 0 ↔ False by decide, show (2 : Fin 4) = 1 ↔ False by decide,
               show (2 : Fin 4) = 3 ↔ False by decide, show (3 : Fin 4) = 0 ↔ False by decide,
               show (3 : Fin 4) = 1 ↔ False by decide, show (3 : Fin 4) = 2 ↔ False by decide,
               and_true, or_false, and_false, ite_true, ite_false, or_true]
    ring
  use ⟨γ_active, h_harm⟩
  constructor
  · simp only [M', S1', γ_active, γ_val]; norm_num
  · intro v; simp only [S2', γ_active, γ_val]; fin_cases v <;> simp

end Diaspora.Models.Naming
