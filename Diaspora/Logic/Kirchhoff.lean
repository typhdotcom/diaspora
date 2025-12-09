import Diaspora.Logic.Genesis
import Diaspora.Logic.Classicality
import Diaspora.Logic.WalkHolonomy
import Diaspora.Hodge.Twist
import Mathlib.Tactic.FieldSimp

namespace Diaspora.Logic.Kirchhoff

open Diaspora.Core Diaspora.Hodge Diaspora.Logic.Genesis Diaspora.Logic.Omega
open Diaspora.Logic.Universal Diaspora.Logic.WalkHolonomy

/-! ## 1. The Standard Triangle Cycle -/

/-- The standard cycle on 3 vertices: 0 → 1 → 2 → 0 -/
def triangle_cycle : SimpleCycle 3 where
  next := ![1, 2, 0]
  prev := ![2, 0, 1]
  next_injective := by decide
  prev_injective := by decide
  next_prev := by intro i; fin_cases i <;> rfl
  prev_next := by intro i; fin_cases i <;> rfl
  connected := fun i j => by
    -- Exhaustive case analysis on Fin 3 × Fin 3
    rcases i with ⟨iv, hi⟩
    rcases j with ⟨jv, hj⟩
    interval_cases iv <;> interval_cases jv <;>
      (first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩)

/-! ## 2. Core Properties -/

lemma triangle_next_0 : triangle_cycle.next 0 = 1 := rfl
lemma triangle_next_1 : triangle_cycle.next 1 = 2 := rfl
lemma triangle_next_2 : triangle_cycle.next 2 = 0 := rfl

lemma triangle_prev_0 : triangle_cycle.prev 0 = 2 := rfl
lemma triangle_prev_1 : triangle_cycle.prev 1 = 0 := rfl
lemma triangle_prev_2 : triangle_cycle.prev 2 = 1 := rfl

/-- The triangle cycle is embedded in the genesis theory graph -/
lemma triangle_embedded_in_genesis :
    cycleEmbeddedIn triangle_cycle (theory_graph (decode rotational_program)) := by
  intro i
  simp only [theory_graph, theory_edges, decode_genesis, Finset.mem_filter,
             List.mem_toFinset, List.mem_append, List.mem_map, ne_eq]
  fin_cases i
  · -- i = 0: edge (0, 1)
    constructor
    · left; exact ⟨{ src := 0, dst := 1, val := 1 }, by simp, rfl⟩
    · decide
  · -- i = 1: edge (1, 2)
    constructor
    · left; exact ⟨{ src := 1, dst := 2, val := 1 }, by simp, rfl⟩
    · decide
  · -- i = 2: edge (2, 0)
    constructor
    · left; exact ⟨{ src := 2, dst := 0, val := 1 }, by simp, rfl⟩
    · decide

/-! ## 3. Raw Flux Values -/

/-- Helper: raw_flux gives 1 on edge (0, 1) -/
lemma raw_flux_01 : raw_flux (decode rotational_program) 0 1 = 1 := by
  unfold raw_flux find_constraint
  simp only [decode_genesis, List.find?]
  rfl

/-- Helper: raw_flux gives 1 on edge (1, 2) -/
lemma raw_flux_12 : raw_flux (decode rotational_program) 1 2 = 1 := by
  unfold raw_flux find_constraint
  simp only [decode_genesis, List.find?]
  rfl

/-- Helper: raw_flux gives 1 on edge (2, 0) -/
lemma raw_flux_20 : raw_flux (decode rotational_program) 2 0 = 1 := by
  unfold raw_flux find_constraint
  simp only [decode_genesis, List.find?]
  rfl

/-- raw_flux gives 1 on all forward edges of the triangle -/
lemma raw_flux_genesis_forward (i : Fin 3) :
    raw_flux (decode rotational_program) i (triangle_cycle.next i) = 1 := by
  fin_cases i
  · exact raw_flux_01
  · exact raw_flux_12
  · exact raw_flux_20

/-! ## 4. Dehn Twist Values -/

/-- The dehn twist on 3 vertices has value 1/3 on forward edges -/
lemma dehn_twist_forward_val (i : Fin 3) :
    (dehn_twist triangle_cycle).val i (triangle_cycle.next i) = 1 / 3 :=
  dehn_twist_constant triangle_cycle (by omega : 3 ≥ 3) i

/-! ## 5. Main Theorem: Genesis = 3 × Dehn Twist -/

/-- Helper: evaluate ![1, 2, 0] at concrete indices -/
@[simp] lemma matrix_next_0 : (![1, 2, 0] : Fin 3 → Fin 3) 0 = 1 := rfl
@[simp] lemma matrix_next_1 : (![1, 2, 0] : Fin 3 → Fin 3) 1 = 2 := rfl
@[simp] lemma matrix_next_2 : (![1, 2, 0] : Fin 3 → Fin 3) 2 = 0 := rfl

/-- The realized genesis cochain equals 3 times the Dehn twist. -/
lemma realize_genesis_00 : (realize (decode rotational_program)).val.val 0 0 = 0 := by
  simp only [realize, raw_flux, find_constraint, decode_genesis, List.find?]; rfl
lemma realize_genesis_01 : (realize (decode rotational_program)).val.val 0 1 = 1 := by
  simp only [realize, raw_flux, find_constraint, decode_genesis, List.find?]; rfl
lemma realize_genesis_02 : (realize (decode rotational_program)).val.val 0 2 = -1 := by
  simp only [realize, raw_flux, find_constraint, decode_genesis, List.find?]; rfl
lemma realize_genesis_10 : (realize (decode rotational_program)).val.val 1 0 = -1 := by
  simp only [realize, raw_flux, find_constraint, decode_genesis, List.find?]; rfl
lemma realize_genesis_11 : (realize (decode rotational_program)).val.val 1 1 = 0 := by
  simp only [realize, raw_flux, find_constraint, decode_genesis, List.find?]; rfl
lemma realize_genesis_12 : (realize (decode rotational_program)).val.val 1 2 = 1 := by
  simp only [realize, raw_flux, find_constraint, decode_genesis, List.find?]; rfl
lemma realize_genesis_20 : (realize (decode rotational_program)).val.val 2 0 = 1 := by
  simp only [realize, raw_flux, find_constraint, decode_genesis, List.find?]; rfl
lemma realize_genesis_21 : (realize (decode rotational_program)).val.val 2 1 = -1 := by
  simp only [realize, raw_flux, find_constraint, decode_genesis, List.find?]; rfl
lemma realize_genesis_22 : (realize (decode rotational_program)).val.val 2 2 = 0 := by
  simp only [realize, raw_flux, find_constraint, decode_genesis, List.find?]; rfl
@[simp] lemma triangle_next_eq_0 : triangle_cycle.next 0 = 1 := rfl
@[simp] lemma triangle_next_eq_1 : triangle_cycle.next 1 = 2 := rfl
@[simp] lemma triangle_next_eq_2 : triangle_cycle.next 2 = 0 := rfl

private lemma fin3_01 : (0 : Fin 3) = 1 ↔ False := by decide
private lemma fin3_02 : (0 : Fin 3) = 2 ↔ False := by decide
private lemma fin3_10 : (1 : Fin 3) = 0 ↔ False := by decide
private lemma fin3_12 : (1 : Fin 3) = 2 ↔ False := by decide
private lemma fin3_20 : (2 : Fin 3) = 0 ↔ False := by decide
private lemma fin3_21 : (2 : Fin 3) = 1 ↔ False := by decide

private lemma fin3_ne_01 : (0 : Fin 3) ≠ 1 ↔ True := by decide
private lemma fin3_ne_02 : (0 : Fin 3) ≠ 2 ↔ True := by decide
private lemma fin3_ne_10 : (1 : Fin 3) ≠ 0 ↔ True := by decide
private lemma fin3_ne_12 : (1 : Fin 3) ≠ 2 ↔ True := by decide
private lemma fin3_ne_20 : (2 : Fin 3) ≠ 0 ↔ True := by decide
private lemma fin3_ne_21 : (2 : Fin 3) ≠ 1 ↔ True := by decide
private lemma fin3_ne_self (i : Fin 3) : i ≠ i ↔ False := by simp

lemma dehn_genesis_00 : (dehn_twist triangle_cycle).val 0 0 = 0 := by
  simp only [dehn_twist, triangle_next_eq_0, fin3_01, false_and, if_false]

lemma dehn_genesis_01 : (dehn_twist triangle_cycle).val 0 1 = 1 / 3 := by
  simp only [dehn_twist, triangle_next_eq_0, triangle_next_eq_1, fin3_ne_02]
  simp only [true_and, if_true]; norm_num

lemma dehn_genesis_02 : (dehn_twist triangle_cycle).val 0 2 = -1 / 3 := by
  simp only [dehn_twist, triangle_next_eq_0, triangle_next_eq_2, fin3_21, fin3_ne_21]
  simp only [false_and, if_false, true_and, if_true]; norm_num

lemma dehn_genesis_10 : (dehn_twist triangle_cycle).val 1 0 = -1 / 3 := by
  simp only [dehn_twist, triangle_next_eq_1, triangle_next_eq_0, fin3_02, fin3_ne_02]
  simp only [false_and, if_false, true_and, if_true]; norm_num

lemma dehn_genesis_11 : (dehn_twist triangle_cycle).val 1 1 = 0 := by
  simp only [dehn_twist, triangle_next_eq_1, fin3_12, false_and, if_false]

lemma dehn_genesis_12 : (dehn_twist triangle_cycle).val 1 2 = 1 / 3 := by
  simp only [dehn_twist, triangle_next_eq_1, triangle_next_eq_2, fin3_ne_10]
  simp only [true_and, if_true]; norm_num

lemma dehn_genesis_20 : (dehn_twist triangle_cycle).val 2 0 = 1 / 3 := by
  simp only [dehn_twist, triangle_next_eq_2, triangle_next_eq_0, fin3_ne_21]
  simp only [true_and, if_true]; norm_num

lemma dehn_genesis_21 : (dehn_twist triangle_cycle).val 2 1 = -1 / 3 := by
  simp only [dehn_twist, triangle_next_eq_2, triangle_next_eq_1, fin3_10, fin3_ne_10]
  simp only [false_and, if_false, true_and, if_true]; norm_num

lemma dehn_genesis_22 : (dehn_twist triangle_cycle).val 2 2 = 0 := by
  simp only [dehn_twist, triangle_next_eq_2, fin3_20, false_and, if_false]

private lemma fin3_mk_0 : (⟨0, by omega⟩ : Fin 3) = 0 := rfl
private lemma fin3_mk_1 : (⟨1, by omega⟩ : Fin 3) = 1 := rfl
private lemma fin3_mk_2 : (⟨2, by omega⟩ : Fin 3) = 2 := rfl

theorem genesis_is_three_dehn :
    ∀ i j : Fin 3,
      (realize (decode rotational_program)).val.val i j =
      3 * (dehn_twist triangle_cycle).val i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [fin3_mk_0, fin3_mk_1, fin3_mk_2,
               realize_genesis_00, realize_genesis_01, realize_genesis_02,
               realize_genesis_10, realize_genesis_11, realize_genesis_12,
               realize_genesis_20, realize_genesis_21, realize_genesis_22,
               dehn_genesis_00, dehn_genesis_01, dehn_genesis_02,
               dehn_genesis_10, dehn_genesis_11, dehn_genesis_12,
               dehn_genesis_20, dehn_genesis_21, dehn_genesis_22] <;>
    norm_num

/-! ## 6. Corollaries -/

/-- The realized genesis cochain is divergence-free (harmonic) -/
theorem genesis_realization_is_harmonic :
    IsHarmonic (realize (decode rotational_program)).val := by
  have h_dehn_harm := dehn_twist_is_harmonic triangle_cycle (by omega : 3 ≥ 3)
  intro i
  calc ∑ j : Fin 3, (realize (decode rotational_program)).val.val i j
      = ∑ j : Fin 3, 3 * (dehn_twist triangle_cycle).val i j := by
          apply Finset.sum_congr rfl; intro j _; exact genesis_is_three_dehn i j
    _ = 3 * ∑ j : Fin 3, (dehn_twist triangle_cycle).val i j := by rw [Finset.mul_sum]
    _ = 3 * 0 := by rw [h_dehn_harm i]
    _ = 0 := by ring

/-- The energy of the realized genesis cochain is 3 -/
theorem genesis_realization_energy :
    norm_sq (realize (decode rotational_program)).val = 3 := by
  have h_dehn_energy := dehn_twist_energy triangle_cycle (by omega : 3 ≥ 3)
  have h_scaled : norm_sq (realize (decode rotational_program)).val =
                  9 * norm_sq (dehn_twist triangle_cycle) := by
    unfold norm_sq inner_product_C1
    have h_sq : ∀ i j, (realize (decode rotational_program)).val.val i j *
                       (realize (decode rotational_program)).val.val i j =
                       9 * ((dehn_twist triangle_cycle).val i j *
                            (dehn_twist triangle_cycle).val i j) := by
      intro i j
      rw [genesis_is_three_dehn i j]
      ring
    simp_rw [h_sq]
    simp only [Finset.mul_sum]
    ring_nf
  rw [h_scaled, h_dehn_energy]
  norm_num

/-- The winding number of the realized genesis cochain is 3 -/
theorem genesis_winding_is_three :
    ∑ i : Fin 3, (realize (decode rotational_program)).val.val i (triangle_cycle.next i) = 3 := by
  have h_dehn_winding := dehn_twist_winding_one triangle_cycle (by omega : 3 ≥ 3)
  calc ∑ i : Fin 3, (realize (decode rotational_program)).val.val i (triangle_cycle.next i)
      = ∑ i : Fin 3, 3 * (dehn_twist triangle_cycle).val i (triangle_cycle.next i) := by
          apply Finset.sum_congr rfl; intro i _; exact genesis_is_three_dehn i _
    _ = 3 * ∑ i : Fin 3, (dehn_twist triangle_cycle).val i (triangle_cycle.next i) := by
          rw [Finset.mul_sum]
    _ = 3 * 1 := by rw [h_dehn_winding]
    _ = 3 := by ring

/-- Genesis is unsatisfiable via the walk-sum perspective. -/
theorem genesis_unsatisfiable_geometric :
    ¬ Satisfiable (decode rotational_program) := by
  intro h_sat
  have h_exact := (satisfiable_iff_exact_on_graph (decode rotational_program)
                    genesis_is_consistent).mp h_sat
  rw [ImGradient, LinearMap.mem_range] at h_exact
  obtain ⟨φ, h_eq⟩ := h_exact
  have h_grad_winding : ∑ i : Fin 3,
      (d_G_linear (theory_graph (decode rotational_program)) φ).val.val i
        (triangle_cycle.next i) = 0 := by
    have h_sum : ∀ i : Fin 3,
        (d_G (theory_graph (decode rotational_program)) φ).val.val i (triangle_cycle.next i) =
        φ (triangle_cycle.next i) - φ i := by
      intro i
      unfold d_G
      have h_edge := triangle_embedded_in_genesis i
      simp only [h_edge, ↓reduceIte]
    simp only [d_G_linear, LinearMap.coe_mk, AddHom.coe_mk, h_sum]
    simp only [Fin.sum_univ_three, triangle_next_0, triangle_next_1, triangle_next_2]
    ring
  have h_realize_winding := genesis_winding_is_three
  have h_winding_eq : ∑ i : Fin 3,
      (realize (decode rotational_program)).val.val i (triangle_cycle.next i) =
      ∑ i : Fin 3,
      (d_G_linear (theory_graph (decode rotational_program)) φ).val.val i
        (triangle_cycle.next i) := by
    congr 1
    ext i
    have := congrFun (congrArg (·.val.val i) h_eq) (triangle_cycle.next i)
    exact this.symm
  rw [h_realize_winding, h_grad_winding] at h_winding_eq
  norm_num at h_winding_eq

/-! ## 7. Walk-Based Genesis Theorem -/

/-- The orbit of 0 under triangle_cycle.next is bijective (covers all of Fin 3). -/
lemma triangle_orbit_bijective :
    Function.Bijective (fun i : Fin 3 => triangle_cycle.next^[i.val] (0 : Fin 3)) := by
  constructor
  · -- Injective: different iterates give different results
    intro ⟨i, hi⟩ ⟨j, hj⟩ h
    simp only [Fin.mk.injEq]
    -- Check all 9 cases
    interval_cases i <;> interval_cases j <;> simp_all
  · -- Surjective: every element is hit
    intro y
    fin_cases y
    · exact ⟨⟨0, by omega⟩, rfl⟩
    · exact ⟨⟨1, by omega⟩, rfl⟩
    · exact ⟨⟨2, by omega⟩, rfl⟩

/-- Walking around the triangle accumulates 3 units of flux. -/
theorem genesis_walk_sum_is_three :
    walk_sum (theory_graph (decode rotational_program)) (realize (decode rotational_program))
      (canonical_cycle_walk triangle_cycle (theory_graph (decode rotational_program))
        triangle_embedded_in_genesis 0) = 3 := by
  rw [walk_sum_eq_winding triangle_cycle _ triangle_embedded_in_genesis _ 0
      triangle_orbit_bijective]
  exact genesis_winding_is_three

/-! ## 8. Uniqueness: The Harmonic Subspace is 1-Dimensional -/

/-- The genesis graph has exactly 6 directed edges (3 undirected). -/
lemma genesis_graph_edge_count :
    (theory_graph (decode rotational_program)).active_edges.card = 6 := by
  simp only [theory_graph, theory_edges, decode_genesis]
  native_decide

/-- The genesis graph edge count divided by 2 gives 3 undirected edges. -/
lemma genesis_undirected_edge_count :
    (theory_graph (decode rotational_program)).active_edges.card / 2 = 3 := by
  rw [genesis_graph_edge_count]

/-- The kernel of d_G on the genesis graph is exactly the constant functions. -/
lemma genesis_kernel_is_constants :
    ∀ φ : C0 3, φ ∈ LinearMap.ker (d_G_linear (theory_graph (decode rotational_program))) ↔
                ∃ c : ℝ, φ = fun _ => c := by
  intro φ
  constructor
  · intro h_ker
    simp only [LinearMap.mem_ker] at h_ker
    -- d_G φ = 0 means φ j - φ i = 0 on all active edges
    use φ 0
    -- Helper: extract that d_G φ = 0 implies gradient is zero
    have h_grad_zero : ∀ i j, (i, j) ∈ (theory_graph (decode rotational_program)).active_edges →
                        φ j - φ i = 0 := by
      intro i j h_edge
      have := congr_arg (fun x => x.val.val i j) h_ker
      simp only [d_G_linear, d_G, LinearMap.coe_mk, AddHom.coe_mk, h_edge, ↓reduceIte] at this
      exact this
    -- Active edges
    have h_01 : (0, 1) ∈ (theory_graph (decode rotational_program)).active_edges := by
      simp only [theory_graph, theory_edges, decode_genesis]; native_decide
    have h_12 : (1, 2) ∈ (theory_graph (decode rotational_program)).active_edges := by
      simp only [theory_graph, theory_edges, decode_genesis]; native_decide
    funext i
    fin_cases i
    · rfl
    · -- φ 1 = φ 0
      have h1 := h_grad_zero 0 1 h_01
      show φ 1 = φ 0
      linarith
    · -- φ 2 = φ 0
      have h1 := h_grad_zero 0 1 h_01
      have h2 := h_grad_zero 1 2 h_12
      show φ 2 = φ 0
      linarith
  · intro ⟨c, hφ⟩
    simp only [LinearMap.mem_ker]
    ext i j
    rw [hφ]
    simp only [d_G_linear, d_G, LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs with h
    · simp only [sub_self]
      rfl
    · rfl

/-- The kernel of d_G on the genesis graph has dimension 1. -/
lemma genesis_kernel_dim :
    Module.finrank ℝ (LinearMap.ker (d_G_linear (theory_graph (decode rotational_program)))) = 1 := by
  -- The kernel is exactly the constant functions, a 1-dimensional subspace
  have h_equiv : LinearMap.ker (d_G_linear (theory_graph (decode rotational_program))) =
                 Submodule.span ℝ {fun _ : Fin 3 => (1 : ℝ)} := by
    ext φ
    rw [genesis_kernel_is_constants]
    constructor
    · intro ⟨c, hφ⟩
      rw [hφ]
      rw [Submodule.mem_span_singleton]
      use c
      funext i
      simp
    · intro h_span
      rw [Submodule.mem_span_singleton] at h_span
      obtain ⟨c, hc⟩ := h_span
      use c
      funext i
      have := congr_fun hc i
      simp at this ⊢
      exact this.symm
  rw [h_equiv]
  have h_one_ne : (fun _ : Fin 3 => (1 : ℝ)) ≠ 0 := by
    intro h
    have := congr_fun h 0
    simp at this
  exact finrank_span_singleton h_one_ne

/-- The harmonic subspace of the genesis graph is 1-dimensional. -/
theorem genesis_harmonic_dim_eq_one :
    Module.finrank ℝ (HarmonicSubspace (theory_graph (decode rotational_program))) = 1 := by
  have h_formula := harmonic_dimension_eq_cyclomatic (theory_graph (decode rotational_program))
  rw [genesis_undirected_edge_count, genesis_kernel_dim] at h_formula
  linarith

/-- Every harmonic form on the genesis graph is a scalar multiple of the Dehn twist. -/
theorem genesis_harmonic_is_dehn_multiple :
    ∀ γ : HarmonicSubspace (theory_graph (decode rotational_program)),
    ∃ c : ℝ, (γ : ActiveForm (theory_graph (decode rotational_program))) =
             c • dehn_twist_active triangle_cycle _ triangle_embedded_in_genesis := by
  intro γ
  have h_dim := genesis_harmonic_dim_eq_one
  have h_dehn_harm := dehn_twist_in_harmonic _ triangle_cycle triangle_embedded_in_genesis (by omega : 3 ≥ 3)
  have h_dehn_ne := dehn_twist_active_ne_zero _ triangle_cycle triangle_embedded_in_genesis (by omega : 3 ≥ 3)
  let dehn := dehn_twist_active triangle_cycle _ triangle_embedded_in_genesis
  let H := HarmonicSubspace (theory_graph (decode rotational_program))
  let dehn_H : H := ⟨dehn, h_dehn_harm⟩
  have h_dehn_H_ne : dehn_H ≠ 0 := by
    intro h_zero
    apply h_dehn_ne
    calc dehn = (dehn_H : ActiveForm _) := rfl
      _ = (0 : H) := congrArg Subtype.val h_zero
      _ = 0 := rfl
  have h_span : Submodule.span ℝ ({dehn_H} : Set H) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_singleton h_dehn_H_ne]
    exact h_dim.symm
  have h_in_span : γ ∈ Submodule.span ℝ ({dehn_H} : Set H) := by
    rw [h_span]
    exact Submodule.mem_top
  rw [Submodule.mem_span_singleton] at h_in_span
  obtain ⟨c, hc⟩ := h_in_span
  use c
  have h_eq : (c • dehn_H : H).val = (γ : ActiveForm _) := congrArg Subtype.val hc
  simp only [Submodule.coe_smul] at h_eq
  exact h_eq.symm

end Diaspora.Logic.Kirchhoff
