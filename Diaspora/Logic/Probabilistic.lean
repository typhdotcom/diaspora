import Diaspora.Logic.Theory
import Diaspora.Hodge.Decomposition

namespace Diaspora.Logic.Probabilistic

open Diaspora.Core Diaspora.Hodge Diaspora.Logic

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-! ## 1. The Geometry of Truth -/

omit [DecidableEq (Fin n)] in
/-- Dimensional gap = Betti number. -/
theorem dimensional_gap (G : DynamicGraph n) :
    Module.finrank ℝ (ActiveForm G) - Module.finrank ℝ (ImGradient G) =
    Module.finrank ℝ (HarmonicSubspace G) := by
  have h_compl : IsCompl (ImGradient G) (HarmonicSubspace G) :=
    Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
  have h_add := Submodule.finrank_add_eq_of_isCompl h_compl
  omega

omit [DecidableEq (Fin n)] in
/-- Non-trivial topology ⟹ satisfiable constraints form proper subspace. -/
theorem genesis_is_generic (G : DynamicGraph n)
    (h_topo : Module.finrank ℝ (HarmonicSubspace G) > 0) :
    Module.finrank ℝ (ImGradient G) < Module.finrank ℝ (ActiveForm G) := by
  have h_gap := dimensional_gap G
  omega

/-! ## 2. Fragility of the Void -/

/--
DecidableEq instance for Constraint, needed for if-then-else expressions.
-/
noncomputable instance : DecidableEq (Constraint n) := fun c1 c2 =>
  if h : c1.src = c2.src ∧ c1.dst = c2.dst ∧ c1.val = c2.val then
    isTrue (by cases c1; cases c2; simp_all)
  else
    isFalse (by intro heq; cases heq; simp_all)

/-- A Theory is robustly satisfiable if it survives perturbation. -/
def RobustlySatisfiable (T : Theory n) : Prop :=
  ∀ (c : Constraint n), c ∈ T →
    Satisfiable (T.map (fun x => if x = c then {x with val := x.val + 1} else x))

omit [Fintype (Fin n)] in
/-- Perturbation preserves graph structure. -/
lemma perturb_preserves_edges (T : Theory n) (c : Constraint n) :
    theory_edges (T.map (fun x => if x = c then {x with val := x.val + 1} else x)) =
    theory_edges T := by
  unfold theory_edges
  have h_pert_src : ∀ x : Constraint n, (if x = c then {x with val := x.val + 1} else x).src = x.src :=
    fun x => by split_ifs <;> rfl
  have h_pert_dst : ∀ x : Constraint n, (if x = c then {x with val := x.val + 1} else x).dst = x.dst :=
    fun x => by split_ifs <;> rfl
  have h_edge : ∀ x : Constraint n,
      ((if x = c then {x with val := x.val + 1} else x).src,
       (if x = c then {x with val := x.val + 1} else x).dst) = (x.src, x.dst) := by
    intro x; simp only [h_pert_src, h_pert_dst]
  have h_edge_rev : ∀ x : Constraint n,
      ((if x = c then {x with val := x.val + 1} else x).dst,
       (if x = c then {x with val := x.val + 1} else x).src) = (x.dst, x.src) := by
    intro x; simp only [h_pert_src, h_pert_dst]
  simp only [List.map_map]
  have h1 : List.map ((fun c => (c.src, c.dst)) ∘ (fun x => if x = c then {x with val := x.val + 1} else x)) T =
            List.map (fun c => (c.src, c.dst)) T :=
    List.map_congr_left (fun x _ => h_edge x)
  have h2 : List.map ((fun c => (c.dst, c.src)) ∘ (fun x => if x = c then {x with val := x.val + 1} else x)) T =
            List.map (fun c => (c.dst, c.src)) T :=
    List.map_congr_left (fun x _ => h_edge_rev x)
  simp only [h1, h2]

omit [Fintype (Fin n)] in
/-- Perturbation preserves full graph structure. -/
lemma perturb_preserves_graph (T : Theory n) (c : Constraint n) :
    theory_graph (T.map (fun x => if x = c then {x with val := x.val + 1} else x)) =
    theory_graph T := by
  unfold theory_graph
  have h_edges := perturb_preserves_edges T c
  simp only [DynamicGraph.mk.injEq]
  exact h_edges

omit [Fintype (Fin n)] in
/-- Active edge ⟹ ∃ constraint covering it. -/
lemma active_edge_has_constraint (T : Theory n) (u v : Fin n)
    (h_active : (u, v) ∈ (theory_graph T).active_edges) :
    ∃ c ∈ T, (c.src = u ∧ c.dst = v) ∨ (c.src = v ∧ c.dst = u) := by
  simp only [theory_graph, theory_edges, Finset.mem_filter, List.mem_toFinset,
             List.mem_append, List.mem_map] at h_active
  obtain ⟨h_edge, _⟩ := h_active
  cases h_edge with
  | inl h => obtain ⟨c, hc, heq⟩ := h; exact ⟨c, hc, Or.inl (by simp_all)⟩
  | inr h => obtain ⟨c, hc, heq⟩ := h; exact ⟨c, hc, Or.inr (by simp_all)⟩

/-- Satisfiable + cycles ⟹ fragile under perturbation. -/
theorem void_is_fragile (T : Theory n)
    (h_cons : LocallyConsistent T)
    (h_sat : Satisfiable T)
    (h_topo : ∃ γ, γ ∈ HarmonicSubspace (theory_graph T) ∧ γ ≠ 0) :
    ¬ RobustlySatisfiable T := by
  obtain ⟨γ, h_harm, h_nonzero⟩ := h_topo
  intro h_robust
  have h_edge : ∃ u v, (u, v) ∈ (theory_graph T).active_edges ∧ γ.val.val u v ≠ 0 := by
    by_contra h_all_zero
    push_neg at h_all_zero
    apply h_nonzero
    ext u v
    by_cases he : (u, v) ∈ (theory_graph T).active_edges
    · exact h_all_zero u v he
    · exact γ.property u v he

  obtain ⟨u, v, h_active, h_val_ne⟩ := h_edge
  obtain ⟨c, hc, h_dir⟩ := active_edge_has_constraint T u v h_active
  have h_exact : (realize T) ∈ ImGradient (theory_graph T) :=
    (satisfiable_iff_exact_on_graph T h_cons).mp h_sat
  have h_orth : Diaspora.Core.ActiveForm.inner (realize T) γ = 0 := by
    rw [HarmonicSubspace] at h_harm
    have := Submodule.inner_left_of_mem_orthogonal h_exact h_harm
    rw [Diaspora.Core.ActiveForm.inner_comm]
    exact this
  let T' := T.map (fun x => if x = c then {x with val := x.val + 1} else x)
  have h_sat' := h_robust c hc
  obtain ⟨φ', h_model'⟩ := h_sat'
  have h_c_perturbed : {c with val := c.val + 1} ∈ T' := by
    show _ ∈ List.map _ _
    rw [List.mem_map]
    exact ⟨c, hc, by simp⟩
  have h_demand_c : φ' c.dst - φ' c.src = c.val + 1 := h_model' _ h_c_perturbed
  by_cases h_dup : ∃ c' ∈ T, c' ≠ c ∧ ((c'.src = c.src ∧ c'.dst = c.dst) ∨ (c'.src = c.dst ∧ c'.dst = c.src))

  case pos =>
    obtain ⟨c', hc', h_ne, h_same_edge⟩ := h_dup
    have h_c'_in_T' : c' ∈ T' := by
      show c' ∈ List.map _ _
      rw [List.mem_map]
      refine ⟨c', hc', ?_⟩
      split_ifs with h_eq
      · exact absurd h_eq h_ne
      · rfl

    have h_demand_c' : φ' c'.dst - φ' c'.src = c'.val := h_model' c' h_c'_in_T'

    cases h_same_edge with
    | inl h_same =>
      have h_cons_eq := (h_cons c hc c' hc').1 ⟨h_same.1.symm, h_same.2.symm⟩
      simp only [h_same.1, h_same.2] at h_demand_c'
      linarith
    | inr h_rev =>
      have h_cons_eq := (h_cons c hc c' hc').2 ⟨h_rev.2.symm, h_rev.1.symm⟩
      simp only [h_rev.1, h_rev.2] at h_demand_c'
      linarith

  case neg =>
    push_neg at h_dup
    have h_gamma_nonzero : γ.val.val c.src c.dst ≠ 0 := by
      cases h_dir with
      | inl h => rw [h.1, h.2]; exact h_val_ne
      | inr h => rw [h.1, h.2]; rw [γ.val.skew]; simp only [neg_ne_zero]; exact h_val_ne
    have h_c_no_loop : c.src ≠ c.dst := by
      intro h_loop
      cases h_dir with
      | inl h => rw [h.1, h.2] at h_loop; exact (theory_graph T).no_loops u (h_loop ▸ h_active)
      | inr h => rw [h.1, h.2] at h_loop; exact (theory_graph T).no_loops v (h_loop.symm ▸ h_active)
    have h_cons' : LocallyConsistent T' := by
      intro c1 h1 c2 h2
      simp only [T'] at h1 h2
      rw [List.mem_map] at h1 h2
      obtain ⟨c1', hc1_mem, hc1_eq⟩ := h1
      obtain ⟨c2', hc2_mem, hc2_eq⟩ := h2
      subst hc1_eq hc2_eq
      constructor
      · intro ⟨h_src, h_dst⟩
        by_cases h1c : c1' = c <;> by_cases h2c : c2' = c
        · simp only [h1c, h2c, ↓reduceIte]
        · simp only [h1c, ↓reduceIte, if_neg h2c] at h_src h_dst ⊢
          exact absurd h_dst.symm ((h_dup c2' hc2_mem h2c).1 h_src.symm)
        · simp only [if_neg h1c, h2c, ↓reduceIte] at h_src h_dst ⊢
          exact absurd h_dst ((h_dup c1' hc1_mem h1c).1 h_src)
        · simp only [if_neg h1c, if_neg h2c] at h_src h_dst ⊢
          exact (h_cons c1' hc1_mem c2' hc2_mem).1 ⟨h_src, h_dst⟩
      · intro ⟨h_src, h_dst⟩
        by_cases h1c : c1' = c <;> by_cases h2c : c2' = c
        · simp only [h1c, h2c, ↓reduceIte] at h_src
          exact absurd h_src h_c_no_loop
        · simp only [h1c, ↓reduceIte, if_neg h2c] at h_src h_dst ⊢
          exact absurd h_src.symm ((h_dup c2' hc2_mem h2c).2 h_dst.symm)
        · simp only [if_neg h1c, h2c, ↓reduceIte] at h_src h_dst ⊢
          exact absurd h_dst ((h_dup c1' hc1_mem h1c).2 h_src)
        · simp only [if_neg h1c, if_neg h2c] at h_src h_dst ⊢
          exact (h_cons c1' hc1_mem c2' hc2_mem).2 ⟨h_src, h_dst⟩
    have h_graph_eq := perturb_preserves_graph T c
    have h_sat' := h_robust c hc
    have h_exact' : realize T' ∈ ImGradient (theory_graph T') :=
      (satisfiable_iff_exact_on_graph T' h_cons').mp h_sat'
    let ip_T := (1/2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n, raw_flux T i j * γ.val.val i j
    let ip_T' := (1/2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n, raw_flux T' i j * γ.val.val i j
    have h_ip_T : ip_T = 0 := h_orth
    have h_diff_sum : ip_T' - ip_T = (1/2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n,
        (raw_flux T' i j - raw_flux T i j) * γ.val.val i j := by
      simp only [ip_T', ip_T]
      have h_factor : ∀ (a b : ℝ), (1/2) * a - (1/2) * b = (1/2) * (a - b) := by intro a b; ring
      rw [h_factor]
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _
      ring
    have h_find_perturb : ∀ u v, find_constraint T' u v =
        (find_constraint T u v).map (fun x => if x = c then {x with val := x.val + 1} else x) := by
      intro u v
      simp only [T', find_constraint]
      rw [List.find?_map]
      have h_pred_eq : (fun d => decide ((d.src = u ∧ d.dst = v) ∨ (d.src = v ∧ d.dst = u))) ∘
                       (fun x => if x = c then {x with val := x.val + 1} else x) =
                       (fun d => decide ((d.src = u ∧ d.dst = v) ∨ (d.src = v ∧ d.dst = u))) := by
        funext x
        simp only [Function.comp_apply]
        split_ifs <;> rfl
      rw [h_pred_eq]
    have h_find_c : find_constraint T c.src c.dst = some c := by
      unfold find_constraint
      have h_not_none : T.find? (fun x => (x.src = c.src ∧ x.dst = c.dst) ∨
                                          (x.src = c.dst ∧ x.dst = c.src)) ≠ none := by
        intro h_none
        rw [List.find?_eq_none] at h_none
        have := h_none c hc
        simp at this
      cases h_get : T.find? (fun x => (x.src = c.src ∧ x.dst = c.dst) ∨
                                       (x.src = c.dst ∧ x.dst = c.src)) with
      | none => exact absurd h_get h_not_none
      | some c' =>
        have h_c'_mem := List.mem_of_find?_eq_some h_get
        have h_c'_matches := List.find?_some h_get
        simp only [decide_eq_true_eq] at h_c'_matches
        by_cases h_eq : c' = c
        · subst h_eq; rfl
        · exfalso
          rcases h_c'_matches with ⟨hs, hd⟩ | ⟨hs, hd⟩
          · exact (h_dup c' h_c'_mem h_eq).1 hs hd
          · exact (h_dup c' h_c'_mem h_eq).2 hs hd

    have h_flux_diff : ∀ i j, raw_flux T' i j - raw_flux T i j =
        if i = c.src ∧ j = c.dst then 1
        else if i = c.dst ∧ j = c.src then -1
        else 0 := by
      intro i j
      by_cases h_loop : i = j
      · simp only [raw_flux, h_loop, ↓reduceIte, sub_self]
        split_ifs with h1 h2
        · exact absurd h1.2 (h1.1 ▸ h_c_no_loop)
        · exact absurd h2.1 (h2.2.symm ▸ h_c_no_loop)
        · rfl
      · simp only [raw_flux, h_loop, ↓reduceIte]
        rw [h_find_perturb]
        by_cases h_edge1 : i = c.src ∧ j = c.dst
        · simp only [h_edge1, ↓reduceIte, h_find_c, Option.map_some, and_self]
          ring
        · simp only [h_edge1, ↓reduceIte]
          by_cases h_edge2 : i = c.dst ∧ j = c.src
          · simp only [h_edge2]
            have h_find_c_rev : find_constraint T c.dst c.src = some c := by
              unfold find_constraint
              have h_not_none : T.find? (fun x => (x.src = c.dst ∧ x.dst = c.src) ∨
                                                  (x.src = c.src ∧ x.dst = c.dst)) ≠ none := by
                intro h_none
                rw [List.find?_eq_none] at h_none
                have := h_none c hc
                simp at this
              cases h_get : T.find? (fun x => (x.src = c.dst ∧ x.dst = c.src) ∨
                                               (x.src = c.src ∧ x.dst = c.dst)) with
              | none => exact absurd h_get h_not_none
              | some c' =>
                have h_c'_mem := List.mem_of_find?_eq_some h_get
                have h_c'_matches := List.find?_some h_get
                simp only [decide_eq_true_eq] at h_c'_matches
                by_cases h_eq : c' = c
                · subst h_eq; rfl
                · exfalso
                  rcases h_c'_matches with ⟨hs, hd⟩ | ⟨hs, hd⟩
                  · exact (h_dup c' h_c'_mem h_eq).2 hs hd
                  · exact (h_dup c' h_c'_mem h_eq).1 hs hd
            -- Substitute using h_edge2
            obtain ⟨hi, hj⟩ := h_edge2
            subst hi hj
            simp only [h_find_c_rev, Option.map_some, ↓reduceIte, and_self]
            have h_not_fwd : ¬(c.src = c.dst ∧ c.dst = c.src) := fun h => h_c_no_loop h.1
            simp only [h_not_fwd, ↓reduceIte]
            ring
          · simp only [h_edge2, ↓reduceIte]
            have h_not_c_edge : ¬((c.src = i ∧ c.dst = j) ∨ (c.src = j ∧ c.dst = i)) := by
              push_neg
              constructor
              · intro hs hd; exact h_edge1 ⟨hs.symm, hd.symm⟩
              · intro hs hd; exact h_edge2 ⟨hd.symm, hs.symm⟩
            match h_find : find_constraint T i j with
            | none => simp only [Option.map_none]; ring
            | some c' =>
              have h_c'_mem := List.mem_of_find?_eq_some h_find
              have h_c'_matches := List.find?_some h_find
              simp only [decide_eq_true_eq] at h_c'_matches
              have h_ne : c' ≠ c := by
                intro heq; rw [heq] at h_c'_matches; exact h_not_c_edge h_c'_matches
              simp only [Option.map_some, if_neg h_ne]
              ring
    have h_sum_simp : ∑ i : Fin n, ∑ j : Fin n,
        (raw_flux T' i j - raw_flux T i j) * γ.val.val i j =
        1 * γ.val.val c.src c.dst + (-1) * γ.val.val c.dst c.src := by
      simp_rw [h_flux_diff]
      simp only [ite_mul, one_mul, neg_one_mul, zero_mul]
      have h_split : ∀ i j, (if i = c.src ∧ j = c.dst then γ.val.val i j
                            else if i = c.dst ∧ j = c.src then -γ.val.val i j
                            else 0) =
                     (if i = c.src ∧ j = c.dst then γ.val.val i j else 0) +
                     (if i = c.dst ∧ j = c.src then -γ.val.val i j else 0) := by
        intro i j
        by_cases h1 : i = c.src ∧ j = c.dst <;> by_cases h2 : i = c.dst ∧ j = c.src
        · -- Both true: impossible since c.src ≠ c.dst
          exfalso; exact h_c_no_loop (h1.1.symm.trans h2.1)
        · simp only [if_pos h1, if_neg h2, add_zero]
        · simp only [if_neg h1, if_pos h2, zero_add]
        · simp only [if_neg h1, if_neg h2, add_zero]
      simp_rw [h_split, Finset.sum_add_distrib]
      have h_sum1 : ∑ i : Fin n, ∑ j : Fin n, (if i = c.src ∧ j = c.dst then γ.val.val i j else 0) =
                    γ.val.val c.src c.dst := by
        rw [Finset.sum_eq_single c.src, Finset.sum_eq_single c.dst]
        · simp only [and_self, ↓reduceIte]
        · intro j _ hj; simp only [hj, and_false, ↓reduceIte]
        · intro h; exact absurd (Finset.mem_univ _) h
        · intro i _ hi
          apply Finset.sum_eq_zero
          intro j _
          simp only [hi, false_and, ↓reduceIte]
        · intro h; exact absurd (Finset.mem_univ _) h
      -- Second sum: ∑ i, ∑ j, if i = c.dst ∧ j = c.src then -γ(i,j) else 0 = -γ(c.dst, c.src)
      have h_sum2 : ∑ i : Fin n, ∑ j : Fin n, (if i = c.dst ∧ j = c.src then -γ.val.val i j else 0) =
                    -γ.val.val c.dst c.src := by
        rw [Finset.sum_eq_single c.dst, Finset.sum_eq_single c.src]
        · simp only [and_self, ↓reduceIte]
        · intro j _ hj; simp only [hj, and_false, ↓reduceIte]
        · intro h; exact absurd (Finset.mem_univ _) h
        · intro i _ hi
          apply Finset.sum_eq_zero
          intro j _
          simp only [hi, false_and, ↓reduceIte]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [h_sum1, h_sum2]
    have h_skew : γ.val.val c.dst c.src = -γ.val.val c.src c.dst := γ.val.skew c.dst c.src
    have h_diff_val : ip_T' - ip_T = γ.val.val c.src c.dst := by
      rw [h_diff_sum, h_sum_simp, h_skew]
      ring
    have h_ip_T'_zero : ip_T' = 0 := by
      rw [ImGradient, LinearMap.mem_range] at h_exact'
      obtain ⟨φ, hφ⟩ := h_exact'
      have h_edges : (theory_graph T').active_edges = (theory_graph T).active_edges := by
        rw [h_graph_eq]
      have h_dG_eq : ∀ i j, (d_G_linear (theory_graph T') φ).val.val i j =
                            (d_G_linear (theory_graph T) φ).val.val i j := by
        intro i j
        simp only [d_G_linear, LinearMap.coe_mk, AddHom.coe_mk, d_G, h_edges]
        congr 1
      have h_dG_exact : d_G_linear (theory_graph T) φ ∈ ImGradient (theory_graph T) := by
        rw [ImGradient, LinearMap.mem_range]; exact ⟨φ, rfl⟩
      have h_orth_dG : Diaspora.Core.ActiveForm.inner (d_G_linear (theory_graph T) φ) γ = 0 := by
        rw [Diaspora.Core.ActiveForm.inner_comm]
        exact Submodule.inner_left_of_mem_orthogonal h_dG_exact h_harm
      calc ip_T' = (1/2 : ℝ) * ∑ i, ∑ j, (realize T').val.val i j * γ.val.val i j := rfl
        _ = (1/2 : ℝ) * ∑ i, ∑ j, (d_G_linear (theory_graph T') φ).val.val i j * γ.val.val i j := by
            rw [← hφ]
        _ = (1/2 : ℝ) * ∑ i, ∑ j, (d_G_linear (theory_graph T) φ).val.val i j * γ.val.val i j := by
            congr 1; apply Finset.sum_congr rfl; intro i _
            apply Finset.sum_congr rfl; intro j _; rw [h_dG_eq]
        _ = Diaspora.Core.ActiveForm.inner (d_G_linear (theory_graph T) φ) γ := rfl
        _ = 0 := h_orth_dG
    have h_gamma_zero : γ.val.val c.src c.dst = 0 := by
      calc γ.val.val c.src c.dst = ip_T' - ip_T := h_diff_val.symm
        _ = 0 - 0 := by rw [h_ip_T'_zero, h_ip_T]
        _ = 0 := by ring

    exact h_gamma_nonzero h_gamma_zero

end Diaspora.Logic.Probabilistic
