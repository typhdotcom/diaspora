import Diaspora.Core.Calculus
import Diaspora.Hodge.Decomposition
import Mathlib.Data.List.Basic

namespace Diaspora.Logic

open Diaspora.Core Diaspora.Hodge

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-! ## 1. Logical Structures -/

/-- A single logical constraint: demands ϕ(dst) - ϕ(src) = val -/
structure Constraint (n : ℕ) where
  src : Fin n
  dst : Fin n
  val : ℝ

/-- A Theory is a collection of constraints. -/
def Theory (n : ℕ) := List (Constraint n)

instance : Membership (Constraint n) (Theory n) := List.instMembership

/--
Semantic Satisfiability:
A theory is satisfiable if there exists a potential ϕ (a "Model")
that respects every constraint in the list.
-/
def Satisfiable (T : Theory n) : Prop :=
  ∃ (ϕ : C0 n), ∀ c ∈ T, ϕ c.dst - ϕ c.src = c.val

/-! ## 2. From Logic to Topology -/

/--
Local Consistency:
A theory is locally consistent if it does not demand two different values
for the same edge (or its reverse).
-/
def LocallyConsistent (T : Theory n) : Prop :=
  ∀ c1 ∈ T, ∀ c2 ∈ T,
    ((c1.src = c2.src ∧ c1.dst = c2.dst) → c1.val = c2.val) ∧
    ((c1.src = c2.dst ∧ c1.dst = c2.src) → c1.val = -c2.val)

/--
The set of active edges defined by the theory.
We explicitly symmetrize it: if c is in T, both (src, dst) and (dst, src) are edges.
Filters out any self-loops to maintain graph invariant.
-/
def theory_edges (T : Theory n) : Finset (Fin n × Fin n) :=
  let directed := T.map (fun c => (c.src, c.dst))
  let reversed := T.map (fun c => (c.dst, c.src))
  ((directed ++ reversed).toFinset).filter (fun p => p.1 ≠ p.2)

/--
The "Universe of Discourse" for a Theory.
-/
def theory_graph (T : Theory n) : DynamicGraph n where
  active_edges := theory_edges T
  symmetric := by
    intro i j
    simp only [theory_edges, Finset.mem_filter, List.mem_toFinset, List.mem_append, List.mem_map, ne_eq]
    constructor
    · rintro ⟨(⟨c, hc, h_eq⟩ | ⟨c, hc, h_eq⟩), hne⟩
      · exact ⟨Or.inr ⟨c, hc, by simp_all⟩, Ne.symm hne⟩
      · exact ⟨Or.inl ⟨c, hc, by simp_all⟩, Ne.symm hne⟩
    · rintro ⟨(⟨c, hc, h_eq⟩ | ⟨c, hc, h_eq⟩), hne⟩
      · exact ⟨Or.inr ⟨c, hc, by simp_all⟩, Ne.symm hne⟩
      · exact ⟨Or.inl ⟨c, hc, by simp_all⟩, Ne.symm hne⟩
  no_loops := by
    intro i
    simp only [theory_edges, Finset.mem_filter, ne_eq, not_and, not_not]
    intro _; trivial

/-! ## 3. Geometric Realization -/

/--
Helper: Find the first constraint in T that covers the edge {u, v}.
This predicate is symmetric in u, v.
-/
def find_constraint (T : Theory n) (u v : Fin n) : Option (Constraint n) :=
  T.find? (fun c => (c.src = u ∧ c.dst = v) ∨ (c.src = v ∧ c.dst = u))

/--
The raw flux function.
If we find a constraint `c` for edge {i, j}:
- If `c` goes i->j, we return `c.val`.
- If `c` goes j->i, we return `-c.val`.
Returns 0 for self-loops to ensure skew symmetry.
-/
def raw_flux (T : Theory n) (i j : Fin n) : ℝ :=
  if i = j then 0
  else match find_constraint T i j with
  | none => 0
  | some c =>
    if c.src = i ∧ c.dst = j then c.val
    else -c.val

omit [Fintype (Fin n)] in
lemma raw_flux_skew (T : Theory n) (i j : Fin n) : raw_flux T i j = - raw_flux T j i := by
  unfold raw_flux find_constraint
  -- Handle self-loop case first
  by_cases h_eq : i = j
  · simp only [h_eq, ite_true]; ring
  · simp only [h_eq, Ne.symm h_eq, ite_false]
    -- The predicates are symmetric (swapped)
    have hfind_eq : T.find? (fun c => decide ((c.src = i ∧ c.dst = j) ∨ (c.src = j ∧ c.dst = i))) =
                    T.find? (fun c => decide ((c.src = j ∧ c.dst = i) ∨ (c.src = i ∧ c.dst = j))) := by
      congr 1; ext c; simp only [decide_eq_decide]; exact or_comm
    simp only [hfind_eq]
    match h : T.find? (fun c => decide ((c.src = j ∧ c.dst = i) ∨ (c.src = i ∧ c.dst = j))) with
    | none => simp only [h]; ring
    | some c =>
      simp only [h]
      have h_sat := List.find?_some h
      simp only [decide_eq_true_eq] at h_sat
      rcases h_sat with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Case c.src = j, c.dst = i
        simp only [and_self, Ne.symm h_eq, false_and, ite_false, ite_true]
      · -- Case c.src = i, c.dst = j
        simp only [and_self, h_eq, false_and, ite_false, ite_true, neg_neg]

/--
Realization: Converting a logical theory into a representational demand (1-cochain).
-/
noncomputable def realize (T : Theory n) : ActiveForm (theory_graph T) :=
  ⟨{ val := raw_flux T, skew := raw_flux_skew T },
   by
     intro i j h_not_active
     simp only [raw_flux]
     -- If edge (i,j) is not active, either i=j or find? returns none
     by_cases h_eq : i = j
     · simp only [h_eq, ite_true]
     · simp only [h_eq, ite_false]
       -- Show find? returns none because no constraint covers this edge
       have h_none : T.find? (fun c => decide ((c.src = i ∧ c.dst = j) ∨ (c.src = j ∧ c.dst = i))) = none := by
         apply List.find?_eq_none.mpr
         intro c hc
         simp only [decide_eq_true_eq, not_or]
         push_neg
         constructor
         · intro h_src h_dst
           apply h_not_active
           simp only [theory_graph, theory_edges, Finset.mem_filter, List.mem_toFinset,
                      List.mem_append, List.mem_map, ne_eq]
           exact ⟨Or.inl ⟨c, hc, by simp [h_src, h_dst]⟩, h_eq⟩
         · intro h_src h_dst
           apply h_not_active
           simp only [theory_graph, theory_edges, Finset.mem_filter, List.mem_toFinset,
                      List.mem_append, List.mem_map, ne_eq]
           exact ⟨Or.inr ⟨c, hc, by simp [h_src, h_dst]⟩, h_eq⟩
       simp only [find_constraint, h_none]⟩

/-! ## 3. The Bridge: Satisfiability ↔ Exactness -/

theorem satisfiable_iff_exact_on_graph
  (T : Theory n) (h_cons : LocallyConsistent T) :
  Satisfiable T ↔ (realize T) ∈ ImGradient (theory_graph T) := by
  constructor
  · -- Satisfiable -> Exact
    intro h_sat
    obtain ⟨ϕ, h_model⟩ := h_sat
    rw [ImGradient, LinearMap.mem_range]
    use ϕ
    ext i j
    -- Check that d_G ϕ matches realize T on active edges
    by_cases h_edge : (i, j) ∈ (theory_graph T).active_edges
    · -- Active edge
      have h_realize : (realize T).val.val i j = raw_flux T i j := rfl
      simp only [d_G_linear, LinearMap.coe_mk, AddHom.coe_mk, d_G, h_edge, ↓reduceIte]
      rw [h_realize, raw_flux]
      -- Active edges have i ≠ j
      have h_ne : i ≠ j := by
        simp only [theory_graph, theory_edges, Finset.mem_filter, ne_eq] at h_edge
        exact h_edge.2
      simp only [h_ne, ↓reduceIte]
      -- We know the edge is active, so find_constraint returns SOME c.
      match h_find : find_constraint T i j with
      | none =>
        -- Contradiction: edge is active means some c exists
        unfold find_constraint at h_find
        exfalso
        simp only [theory_graph, theory_edges, Finset.mem_filter, List.mem_toFinset,
                   List.mem_append, List.mem_map, ne_eq] at h_edge
        obtain ⟨(⟨c, hc, h_orient⟩ | ⟨c, hc, h_orient⟩), _⟩ := h_edge
        · have h_sat : decide ((c.src = i ∧ c.dst = j) ∨ (c.src = j ∧ c.dst = i)) = true := by
            simp_all
          rw [List.find?_eq_none] at h_find
          exact h_find c hc h_sat
        · have h_sat : decide ((c.src = i ∧ c.dst = j) ∨ (c.src = j ∧ c.dst = i)) = true := by
            simp_all
          rw [List.find?_eq_none] at h_find
          exact h_find c hc h_sat
      | some c =>
        have hc : c ∈ T := List.mem_of_find?_eq_some h_find
        have h_match : (c.src = i ∧ c.dst = j) ∨ (c.src = j ∧ c.dst = i) := by
          have := List.find?_some h_find
          simp at this; exact this
        dsimp only
        split_ifs with h_dir
        · -- c is i->j, so c.src = i, c.dst = j
          rw [← h_dir.1, ← h_dir.2, h_model c hc]
        · -- c is j->i
          push_neg at h_dir
          cases h_match with
          | inl h_bad => exact absurd h_bad.2 (h_dir h_bad.1)
          | inr h_rev =>
            rw [← h_rev.1, ← h_rev.2, ← neg_sub, h_model c hc]
    · -- Non-active edges
      simp only [d_G_linear, LinearMap.coe_mk, AddHom.coe_mk, d_G, h_edge, ↓reduceIte]
      exact ((realize T).property i j h_edge).symm

  · -- Exact -> Satisfiable
    intro h_exact
    rw [ImGradient, LinearMap.mem_range] at h_exact
    obtain ⟨ϕ, h_phi⟩ := h_exact
    use ϕ
    intro c hc
    -- The edge (c.src, c.dst) is active because c ∈ T (assuming src ≠ dst)
    by_cases h_loop : c.src = c.dst
    · -- Self-loop constraint: need c.val = 0
      -- LocallyConsistent with c.src = c.dst means c.val = -c.val
      have h_self := (h_cons c hc c hc).2
      simp only [h_loop, and_self, forall_const] at h_self
      -- h_self : c.val = -c.val implies c.val = 0
      have h_zero : c.val = 0 := by linarith
      simp only [h_loop, h_zero, sub_self]
    · -- Normal case: src ≠ dst
      have h_active : (c.src, c.dst) ∈ (theory_graph T).active_edges := by
        simp only [theory_graph, theory_edges, Finset.mem_filter, List.mem_toFinset,
                   List.mem_append, List.mem_map, ne_eq]
        exact ⟨Or.inl ⟨c, hc, rfl⟩, h_loop⟩
      -- d_G_linear ϕ = realize T
      have h_eq : (d_G_linear (theory_graph T) ϕ).val.val c.src c.dst =
                  (realize T).val.val c.src c.dst := by simp only [h_phi]
      simp only [d_G_linear, LinearMap.coe_mk, AddHom.coe_mk, d_G, h_active, ↓reduceIte] at h_eq
      -- RHS: raw_flux T c.src c.dst
      simp only [realize, raw_flux, h_loop, ↓reduceIte] at h_eq
      match h_find : find_constraint T c.src c.dst with
      | none =>
        unfold find_constraint at h_find
        exfalso
        have h_sat : decide ((c.src = c.src ∧ c.dst = c.dst) ∨ (c.src = c.dst ∧ c.dst = c.src)) = true := by
          simp
        rw [List.find?_eq_none] at h_find
        exact h_find c hc h_sat
      | some c' =>
        have hc' : c' ∈ T := List.mem_of_find?_eq_some h_find
        -- Unfold find_constraint in both h_eq and h_find
        unfold find_constraint at h_eq h_find
        -- Now substitute the result into h_eq
        simp only [h_find] at h_eq
        -- Now h_eq has the if-then-else
        split_ifs at h_eq with h_dir
        · -- c' is src->dst. return c'.val.
          -- We need c.val = c'.val by consistency.
          have h_cons_check : c.val = c'.val :=
             (h_cons c hc c' hc').1 ⟨h_dir.1.symm, h_dir.2.symm⟩
          rw [h_eq, h_cons_check]
        · -- c' is dst->src. return -c'.val.
          -- c.src=src, c.dst=dst. c'.src=dst, c'.dst=src.
          have h_match : (c'.src = c.src ∧ c'.dst = c.dst) ∨ (c'.src = c.dst ∧ c'.dst = c.src) := by
            have := List.find?_some h_find; simp at this; exact this
          cases h_match with
          | inl h_bad => exact absurd h_bad h_dir
          | inr h_rev =>
             have h_cons_check := (h_cons c hc c' hc').2
             simp only [h_rev, and_self, forall_const] at h_cons_check
             rw [h_eq, h_cons_check]

theorem inconsistency_implies_topology
  (T : Theory n) (h_cons : LocallyConsistent T) :
  ¬ Satisfiable T → ∃ γ, γ ∈ HarmonicSubspace (theory_graph T) ∧ γ ≠ 0 := by
  intro h_unsat
  -- 1. Hodge Decomposition exists
  have h_decomp := hodge_decomposition_graph (theory_graph T) (realize T)
  obtain ⟨ϕ, γ, h_eq, h_harm, _⟩ := h_decomp

  -- 2. If γ were 0, then realize T = dϕ -> exact -> satisfiable
  by_contra h_no_gamma
  push_neg at h_no_gamma
  -- h_no_gamma : ∀ x ∈ HarmonicSubspace, x = 0
  have h_zero : γ = 0 := h_no_gamma γ h_harm

  rw [h_zero, add_zero] at h_eq
  have h_exact : (realize T) ∈ ImGradient (theory_graph T) := by
    rw [ImGradient, LinearMap.mem_range]; use ϕ; exact h_eq.symm

  have h_sat := (satisfiable_iff_exact_on_graph T h_cons).mpr h_exact
  contradiction

end Diaspora.Logic
