import Diaspora.Logic.Classicality.Cycles
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace Diaspora.Logic

open Diaspora.Core Diaspora.Hodge

variable {n : ℕ}

/-- Classical universes have no cycles: dim(H) = 0 ⟹ acyclic. -/
theorem classical_implies_acyclic [DecidableEq (Fin n)] [NeZero n]
    (G : DynamicGraph n) (h_class : IsClassical G) :
    (DynamicGraph.toSimpleGraph G).IsAcyclic := by
  intro v w h_cycle
  exact cycle_walk_implies_nonclassical G w h_cycle h_class

/-- Canonical height: distance from vertex 0. -/
noncomputable def canonical_height [NeZero n] (G : DynamicGraph n) : C0 n :=
  fun v => (DynamicGraph.toSimpleGraph G).dist ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ v

/-- In a tree, adjacent vertices have distances differing by 1. -/
lemma tree_adjacent_dist_diff [NeZero n] {G : SimpleGraph (Fin n)}
    (h_acyclic : G.IsAcyclic) (h_conn : G.Connected)
    {u v : Fin n} (h_adj : G.Adj u v) (r : Fin n) :
    G.dist r u + 1 = G.dist r v ∨ G.dist r v + 1 = G.dist r u := by
  have h_diff := h_conn.diff_dist_adj (u := r) h_adj
  have h_ne : G.dist r u ≠ G.dist r v := by
    intro h_eq
    have h_u_ne_v : u ≠ v := h_adj.ne
    obtain ⟨p_ru, hp_ru⟩ := (h_conn r u).exists_walk_length_eq_dist
    obtain ⟨p_rv, hp_rv⟩ := (h_conn r v).exists_walk_length_eq_dist
    by_cases hv_on : v ∈ p_ru.support
    · have h_spec := p_ru.take_spec hv_on
      have h_len_add : (p_ru.takeUntil v hv_on).length + (p_ru.dropUntil v hv_on).length = p_ru.length := by
        calc (p_ru.takeUntil v hv_on).length + (p_ru.dropUntil v hv_on).length
            = ((p_ru.takeUntil v hv_on).append (p_ru.dropUntil v hv_on)).length := by
                rw [SimpleGraph.Walk.length_append]
          _ = p_ru.length := by rw [h_spec]
      have h_dist_rv : G.dist r v ≤ (p_ru.takeUntil v hv_on).length := SimpleGraph.dist_le _
      have h_dist_vu : G.dist v u ≤ (p_ru.dropUntil v hv_on).length := SimpleGraph.dist_le _
      have hadj_dist : G.dist v u = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h_adj.symm
      have h_tri := h_conn.dist_triangle (u := r) (v := v) (w := u)
      omega
    · let w_ruv := p_ru.append (SimpleGraph.Walk.cons h_adj SimpleGraph.Walk.nil)
      have h_len : w_ruv.length = G.dist r u + 1 := by
        simp [w_ruv, hp_ru]
      have h_le := SimpleGraph.dist_le w_ruv
      by_cases hu_on : u ∈ p_rv.support
      · have h_spec := p_rv.take_spec hu_on
        have h_len_add : (p_rv.takeUntil u hu_on).length + (p_rv.dropUntil u hu_on).length = p_rv.length := by
          calc (p_rv.takeUntil u hu_on).length + (p_rv.dropUntil u hu_on).length
              = ((p_rv.takeUntil u hu_on).append (p_rv.dropUntil u hu_on)).length := by
                  rw [SimpleGraph.Walk.length_append]
            _ = p_rv.length := by rw [h_spec]
        have h_dist_ru : G.dist r u ≤ (p_rv.takeUntil u hu_on).length := SimpleGraph.dist_le _
        have h_dist_uv : G.dist u v ≤ (p_rv.dropUntil u hu_on).length := SimpleGraph.dist_le _
        have hadj_dist : G.dist u v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h_adj
        have h_tri := h_conn.dist_triangle (u := r) (v := u) (w := v)
        omega
      · have hp_ru_path : p_ru.IsPath := p_ru.isPath_of_length_eq_dist hp_ru
        have hp_rv_path : p_rv.IsPath := p_rv.isPath_of_length_eq_dist hp_rv
        let w_ruv := p_ru.concat h_adj
        have hw_path : w_ruv.IsPath := by
          rw [SimpleGraph.Walk.concat_isPath_iff]
          exact ⟨hp_ru_path, hv_on⟩
        let path1 : G.Path r v := ⟨p_rv, hp_rv_path⟩
        let path2 : G.Path r v := ⟨w_ruv, hw_path⟩
        have h_uniq := h_acyclic.path_unique path1 path2
        have h_len1 : p_rv.length = G.dist r v := hp_rv
        have h_len2 : w_ruv.length = G.dist r u + 1 := by simp [w_ruv, hp_ru]
        have h_walks_eq : p_rv = w_ruv := congrArg Subtype.val h_uniq
        have h_lens_eq : p_rv.length = w_ruv.length := congrArg SimpleGraph.Walk.length h_walks_eq
        omega
  omega

/-- Classical connected universes admit intrinsic hierarchy via graph distance. -/
theorem classical_universe_admits_intrinsic_hierarchy [NeZero n] [DecidableEq (Fin n)]
    (G : DynamicGraph n) (h_class : IsClassical G)
    (h_conn : (DynamicGraph.toSimpleGraph G).Connected) :
    IsFaithfulPotential G (canonical_height G) ∧ WellFounded (IsMember G (canonical_height G)) := by
  have h_acyclic := classical_implies_acyclic G h_class
  constructor
  · intro i j h_edge
    unfold canonical_height
    simp only [ne_eq, Nat.cast_inj]
    have h_adj : (DynamicGraph.toSimpleGraph G).Adj i j := h_edge
    have h_diff := tree_adjacent_dist_diff h_acyclic h_conn h_adj ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    omega
  · exact isMember_wellFounded G _

/-- Extrinsic version using vertex indices. -/
theorem classical_universe_admits_rank [NeZero n] (G : DynamicGraph n) (_h_class : IsClassical G) :
    ∃ (ϕ : C0 n), IsFaithfulPotential G ϕ ∧ WellFounded (IsMember G ϕ) := by
  use fun v => v.val
  constructor
  · intro i j h_edge
    have h_ne : i ≠ j := fun h_eq => G.no_loops i (h_eq ▸ h_edge)
    simp only [ne_eq, Nat.cast_inj]
    exact Fin.val_ne_of_ne h_ne
  · exact isMember_wellFounded G _

/-- Classical universes admit no paradoxes: every ActiveForm is exact. -/
theorem classical_universe_admits_no_paradoxes [Fintype (Fin n)] [DecidableEq (Fin n)]
    (G : DynamicGraph n) (h_class : IsClassical G) :
    ∀ σ : ActiveForm G, σ ∈ ImGradient G := by
  intro σ
  have h_decomp := hodge_decomposition_graph G σ
  obtain ⟨ϕ, γ, h_eq, h_harm, _⟩ := h_decomp
  have h_zero : γ = 0 := by
    have h_all_zero := finrank_zero_iff_forall_zero.mp h_class
    exact Subtype.ext_iff.mp (h_all_zero ⟨γ, h_harm⟩)
  rw [h_zero, add_zero] at h_eq
  rw [ImGradient, LinearMap.mem_range]
  exact ⟨ϕ, h_eq.symm⟩

end Diaspora.Logic
