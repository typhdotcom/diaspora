import Diaspora.Logic.Theory

namespace Diaspora.Logic.Inverse

open Diaspora.Core Diaspora.Hodge Diaspora.Logic

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-! ## 1. Constructing Logic from Physics -/

/-- Construct a Theory from an arbitrary 1-cochain. -/
noncomputable def fossilize (G : DynamicGraph n) (σ : ActiveForm G) : Theory n :=
  let edges := G.active_edges.toList
  edges.filterMap (fun (i, j) =>
    if i < j then
      some { src := i, dst := j, val := σ.val.val i j }
    else none
  )

/-! ## 2. Fidelity of the Fossil -/

omit [Fintype (Fin n)] in
/-- The theory graph of the fossilized theory is a subgraph of the original. -/
lemma fossil_graph_subset (G : DynamicGraph n) (σ : ActiveForm G) :
    (theory_graph (fossilize G σ)).active_edges ⊆ G.active_edges := by
  intro x hx
  simp only [theory_graph, theory_edges, fossilize, Finset.mem_filter, List.mem_toFinset,
    List.mem_append, List.mem_map, List.mem_filterMap, ne_eq] at hx
  obtain ⟨h_or, _⟩ := hx
  rcases h_or with (⟨c, ⟨⟨a, b⟩, ha_mem, ha_eq⟩, rfl⟩ | ⟨c, ⟨⟨a, b⟩, ha_mem, ha_eq⟩, rfl⟩)
  all_goals {
    split_ifs at ha_eq with h_lt
    · cases Option.some.inj ha_eq
      simp only [Finset.mem_toList] at ha_mem
      first | exact ha_mem | exact (G.symmetric _ _).mp ha_mem
  }

omit [Fintype (Fin n)] [DecidableEq (Fin n)] in
/-- The fossilized theory is locally consistent. -/
theorem fossil_is_consistent (G : DynamicGraph n) (σ : ActiveForm G) :
    LocallyConsistent (fossilize G σ) := by
  intro c1 h1 c2 h2
  unfold fossilize at h1 h2
  rw [List.mem_filterMap] at h1 h2
  obtain ⟨⟨i1, j1⟩, hp1_mem, hp1_eq⟩ := h1
  obtain ⟨⟨i2, j2⟩, hp2_mem, hp2_eq⟩ := h2
  simp only at hp1_eq hp2_eq
  split_ifs at hp1_eq with h_lt1
  split_ifs at hp2_eq with h_lt2
  cases Option.some.inj hp1_eq
  cases Option.some.inj hp2_eq
  constructor
  · intro ⟨h_src, h_dst⟩
    simp only at h_src h_dst ⊢
    rw [h_src, h_dst]
  · intro ⟨h_src, h_dst⟩
    simp only at h_src h_dst
    omega

/-! ## 3. The Pure Paradox Theorem -/

/-- For harmonic γ, the fossilized theory realizes exactly to γ on active edges. -/
theorem matter_is_fossilized_logic (G : DynamicGraph n) (γ : ActiveForm G)
    (_h_harm : γ ∈ HarmonicSubspace G) :
    let T := fossilize G γ
    ∀ i j, (i, j) ∈ G.active_edges → (realize T).val.val i j = γ.val.val i j := by
  intro T i j h_edge
  unfold realize raw_flux
  have h_ne : i ≠ j := by intro heq; subst heq; exact G.no_loops i h_edge
  simp [h_ne, ↓reduceIte]
  unfold find_constraint
  rcases Nat.lt_trichotomy i j with h_lt | h_eq | h_gt
  · have h_lt_fin : i < j := h_lt
    have h_mem : { src := i, dst := j, val := γ.val.val i j } ∈ T := by
      simp only [T, fossilize]
      rw [List.mem_filterMap]
      exact ⟨(i, j), Finset.mem_toList.mpr h_edge, by simp only [h_lt_fin, ↓reduceIte]⟩
    match h_find : T.find? (fun c => decide (c.src = i ∧ c.dst = j ∨ c.src = j ∧ c.dst = i)) with
    | none =>
      exfalso
      rw [List.find?_eq_none] at h_find
      have := h_find _ h_mem
      simp at this
    | some c =>
      simp only [h_find]
      have h_sat := List.find?_some h_find
      simp only [decide_eq_true_eq] at h_sat
      rcases h_sat with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · have hc_mem := List.mem_of_find?_eq_some h_find
        simp only [T, fossilize] at hc_mem
        rw [List.mem_filterMap] at hc_mem
        obtain ⟨⟨a, b⟩, hab_mem, hab_eq⟩ := hc_mem
        simp only at hab_eq
        split_ifs at hab_eq with h_ab
        · cases Option.some.inj hab_eq
          simp only [and_self, ↓reduceIte]
      · have hc_mem := List.mem_of_find?_eq_some h_find
        simp only [T, fossilize] at hc_mem
        rw [List.mem_filterMap] at hc_mem
        obtain ⟨⟨a, b⟩, hab_mem, hab_eq⟩ := hc_mem
        simp only at hab_eq
        split_ifs at hab_eq with h_ab
        · cases Option.some.inj hab_eq
          simp only at h_lt h_ab
          omega
  · exact absurd (Fin.val_injective h_eq) h_ne
  · have h_gt_fin : j < i := h_gt
    have h_edge_sym : (j, i) ∈ G.active_edges := (G.symmetric j i).mpr h_edge
    have h_mem : { src := j, dst := i, val := γ.val.val j i } ∈ T := by
      simp only [T, fossilize]
      rw [List.mem_filterMap]
      exact ⟨(j, i), Finset.mem_toList.mpr h_edge_sym, by simp only [h_gt_fin, ↓reduceIte]⟩
    match h_find : T.find? (fun c => decide (c.src = i ∧ c.dst = j ∨ c.src = j ∧ c.dst = i)) with
    | none =>
      exfalso
      rw [List.find?_eq_none] at h_find
      have := h_find _ h_mem
      simp [Ne.symm h_ne] at this
    | some c =>
      simp only [h_find]
      have h_sat := List.find?_some h_find
      simp only [decide_eq_true_eq] at h_sat
      rcases h_sat with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · have hc_mem := List.mem_of_find?_eq_some h_find
        simp only [T, fossilize] at hc_mem
        rw [List.mem_filterMap] at hc_mem
        obtain ⟨⟨a, b⟩, hab_mem, hab_eq⟩ := hc_mem
        simp only at hab_eq
        split_ifs at hab_eq with h_ab
        · cases Option.some.inj hab_eq
          simp only at h_gt h_ab
          omega
      · have hc_mem := List.mem_of_find?_eq_some h_find
        simp only [T, fossilize] at hc_mem
        rw [List.mem_filterMap] at hc_mem
        obtain ⟨⟨a, b⟩, hab_mem, hab_eq⟩ := hc_mem
        simp only at hab_eq
        split_ifs at hab_eq with h_ab
        · cases Option.some.inj hab_eq
          simp only [h_ne, and_false, ↓reduceIte]
          exact neg_eq_iff_eq_neg.mpr (γ.val.skew a b)

/-- Every non-zero harmonic form corresponds to an unsatisfiable theory. -/
theorem harmonic_yields_unsatisfiable (G : DynamicGraph n) (γ : ActiveForm G)
    (h_harm : γ ∈ HarmonicSubspace G) (h_ne : γ ≠ 0) :
    ¬Satisfiable (fossilize G γ) := by
  intro ⟨ϕ, h_model⟩
  have h_exact : γ ∈ ImGradient G := by
    rw [ImGradient, LinearMap.mem_range]
    use ϕ
    ext i j
    by_cases h_edge : (i, j) ∈ G.active_edges
    · simp only [d_G_linear, LinearMap.coe_mk, AddHom.coe_mk, d_G, h_edge, ↓reduceIte]
      have h_ne_ij : i ≠ j := by intro heq; subst heq; exact G.no_loops i h_edge
      rcases Nat.lt_trichotomy i j with h_lt | h_eq | h_gt
      · have h_lt_fin : i < j := h_lt
        have h_mem : { src := i, dst := j, val := γ.val.val i j } ∈ fossilize G γ := by
          simp only [fossilize]
          rw [List.mem_filterMap]
          exact ⟨(i, j), Finset.mem_toList.mpr h_edge, by simp only [h_lt_fin, ↓reduceIte]⟩
        have h_eq := h_model _ h_mem
        simp only at h_eq
        linarith
      · exact absurd (Fin.val_injective h_eq) h_ne_ij
      · have h_gt_fin : j < i := h_gt
        have h_edge_sym := (G.symmetric j i).mpr h_edge
        have h_mem : { src := j, dst := i, val := γ.val.val j i } ∈ fossilize G γ := by
          simp only [fossilize]
          rw [List.mem_filterMap]
          exact ⟨(j, i), Finset.mem_toList.mpr h_edge_sym, by simp only [h_gt_fin, ↓reduceIte]⟩
        have h_eq := h_model _ h_mem
        simp only at h_eq
        have h_skew := γ.val.skew j i
        linarith
    · simp only [d_G_linear, LinearMap.coe_mk, AddHom.coe_mk, d_G, h_edge, ↓reduceIte]
      exact (γ.property i j h_edge).symm
  rw [HarmonicSubspace, Submodule.mem_orthogonal'] at h_harm
  have h_self_orth := h_harm γ h_exact
  rw [inner_self_eq_zero] at h_self_orth
  exact h_ne h_self_orth

/-- Corollary: Every non-zero particle is locally consistent but unsatisfiable. -/
theorem particle_is_paradox (G : DynamicGraph n) (γ : ActiveForm G)
    (h_harm : γ ∈ HarmonicSubspace G) (h_ne : γ ≠ 0) :
    LocallyConsistent (fossilize G γ) ∧ ¬Satisfiable (fossilize G γ) :=
  ⟨fossil_is_consistent G γ, harmonic_yields_unsatisfiable G γ h_harm h_ne⟩

end Diaspora.Logic.Inverse
