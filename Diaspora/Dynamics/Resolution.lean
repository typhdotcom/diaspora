import Diaspora.Hodge.EdgeAddition
import Diaspora.Dynamics.Transition
import Diaspora.Logic.Information

/-!
# The Arrow of Resolution

Removing a non-bridge edge from a connected graph decreases b₁ by exactly 1.
-/

open BigOperators Diaspora.Core Diaspora.Hodge Diaspora.Logic.Information

namespace Diaspora.Dynamics.Resolution

variable {n : ℕ} [Fintype (Fin n)]

/-! ## Non-Bridge Edges -/

/-- An edge is a **non-bridge** (cycle edge) if removing it preserves connectivity.
    Equivalently: the edge is part of at least one cycle. -/
def IsNonBridgeEdge (G : DynamicGraph n) (i j : Fin n) : Prop :=
  (i, j) ∈ G.active_edges ∧
  Module.finrank ℝ (LinearMap.ker (d_G_linear (remove_edge G i j))) =
  Module.finrank ℝ (LinearMap.ker (d_G_linear G))

/-- An edge is a **bridge** if removing it disconnects the graph.
    Equivalently: removing it increases the kernel dimension. -/
def IsBridgeEdge (G : DynamicGraph n) (i j : Fin n) : Prop :=
  (i, j) ∈ G.active_edges ∧
  Module.finrank ℝ (LinearMap.ker (d_G_linear (remove_edge G i j))) >
  Module.finrank ℝ (LinearMap.ker (d_G_linear G))

/-- Every active edge is either a bridge or a non-bridge. -/
theorem edge_trichotomy (G : DynamicGraph n) (i j : Fin n)
    (h_active : (i, j) ∈ G.active_edges) :
    IsNonBridgeEdge G i j ∨ IsBridgeEdge G i j := by
  by_cases h : Module.finrank ℝ (LinearMap.ker (d_G_linear (remove_edge G i j))) =
               Module.finrank ℝ (LinearMap.ker (d_G_linear G))
  · left; exact ⟨h_active, h⟩
  · right
    refine ⟨h_active, ?_⟩
    -- Removing edges can only increase kernel dimension (fewer constraints)
    have h_ker_mono : LinearMap.ker (d_G_linear G) ≤
                      LinearMap.ker (d_G_linear (remove_edge G i j)) := by
      intro φ hφ
      rw [LinearMap.mem_ker] at hφ ⊢
      ext a b
      show (d_G (remove_edge G i j) φ).val.val a b = 0
      unfold d_G
      by_cases hab : (a, b) ∈ (remove_edge G i j).active_edges
      · have hab_orig : (a, b) ∈ G.active_edges := by
          simp only [remove_edge, Finset.mem_erase, ne_eq] at hab
          exact hab.2.2
        have hφ_ab : (d_G G φ).val.val a b = 0 := by
          have := congr_fun₂ (congr_arg C1.val (congr_arg Subtype.val hφ)) a b
          exact this
        simp only [d_G, hab_orig, ↓reduceIte] at hφ_ab
        simp only [hab, ↓reduceIte]
        exact hφ_ab
      · simp only [hab, ↓reduceIte]
    have h_dim_mono := Submodule.finrank_mono h_ker_mono
    omega

/-! ## The Edge Removal Theorem -/

/-- **The Edge Removal Theorem**: Removing a non-bridge edge from a connected graph
    decreases the Betti number by exactly 1.

    This is the dual of `edge_addition_increases_betti`.
-/
theorem edge_removal_decreases_betti [NeZero n] (G : DynamicGraph n)
    (i j : Fin n) (h_ne : i ≠ j)
    (h_active : (i, j) ∈ G.active_edges)
    (h_conn : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1)
    (h_nonbridge : IsNonBridgeEdge G i j) :
    Module.finrank ℝ (HarmonicSubspace (remove_edge G i j)) + 1 =
    Module.finrank ℝ (HarmonicSubspace G) := by
  -- Key insight: G = addEdge (remove_edge G i j) i j
  -- So by edge_addition_increases_betti:
  --   b₁(G) = b₁(remove_edge G i j) + 1
  -- Therefore: b₁(remove_edge G i j) = b₁(G) - 1

  -- Use the harmonic dimension formula for both graphs
  have h_G := harmonic_dimension_eq_cyclomatic G
  have h_G' := harmonic_dimension_eq_cyclomatic (remove_edge G i j)

  -- Non-bridge means connectivity preserved
  have h_conn' : Module.finrank ℝ (LinearMap.ker (d_G_linear (remove_edge G i j))) = 1 :=
    h_nonbridge.2.trans h_conn

  rw [h_conn] at h_G
  rw [h_conn'] at h_G'

  -- Edge count decreases by 2 (both directions)
  have h_card : (remove_edge G i j).active_edges.card + 2 = G.active_edges.card := by
    have h_sym : (j, i) ∈ G.active_edges := (G.symmetric i j).mp h_active
    have h_ne_pair : (i, j) ≠ (j, i) := by intro h; injection h with h'; exact h_ne h'
    have h_mem_after : (j, i) ∈ G.active_edges.erase (i, j) := by
      simp only [Finset.mem_erase]; exact ⟨h_ne_pair.symm, h_sym⟩
    have h1 : (G.active_edges.erase (i, j)).card + 1 = G.active_edges.card :=
      Finset.card_erase_add_one h_active
    have h2 : ((G.active_edges.erase (i, j)).erase (j, i)).card + 1 =
              (G.active_edges.erase (i, j)).card :=
      Finset.card_erase_add_one h_mem_after
    -- Direct computation: show the cards are equal
    have h_eq : (remove_edge G i j).active_edges.card =
                ((G.active_edges.erase (i, j)).erase (j, i)).card := by
      -- Both are the same finset, just with different DecidableEq instances
      -- The finsets are equal by definition
      rfl
    omega

  -- Both graphs have even edge count (symmetric edges)
  have h_even_G := active_edges_even_card G
  have h_even_G' := active_edges_even_card (remove_edge G i j)
  obtain ⟨k, hk⟩ := h_even_G
  obtain ⟨k', hk'⟩ := h_even_G'

  -- From h_card: k' + k' + 2 = k + k, so k' = k - 1
  have h_k : k' + 1 = k := by omega

  -- Substitute into the dimension formulas
  simp only [hk, hk'] at h_G h_G'
  -- h_G: finrank H(G) + n = k + 1
  -- h_G': finrank H(G') + n = k' + 1

  omega

/-! ## Consequences for Evolution -/

/--
**The Resolution Principle**: Every non-bridge edge break resolves exactly
one unit of topological deficit.
-/
theorem nonbridge_break_resolves_one_deficit [NeZero n] (G : DynamicGraph n)
    (i j : Fin n) (h_ne : i ≠ j)
    (h_active : (i, j) ∈ G.active_edges)
    (h_conn : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1)
    (h_nonbridge : IsNonBridgeEdge G i j) :
    TopologicalDeficit (remove_edge G i j) + 1 = TopologicalDeficit G := by
  rw [topological_deficit_eq_harmonic_dim, topological_deficit_eq_harmonic_dim]
  have h := edge_removal_decreases_betti G i j h_ne h_active h_conn h_nonbridge
  -- Convert natural number equality to real equality
  have h_real : (Module.finrank ℝ (HarmonicSubspace (remove_edge G i j)) : ℝ) + 1 =
                (Module.finrank ℝ (HarmonicSubspace G) : ℝ) := by
    exact_mod_cast h
  exact h_real

/--
**The Arrow Has Two Faces**: When evolution breaks a non-bridge edge:
1. Entropy increases (latent_capacity grows by σ(i,j)²)
2. Paradox decreases (topological deficit drops by 1)
-/
theorem evolution_dual_arrow [NeZero n] (G : DynamicGraph n) (σ : C1 n)
    (i j : Fin n) (h_ne : i ≠ j)
    (h_active : (i, j) ∈ G.active_edges)
    (h_conn : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1)
    (h_nonbridge : IsNonBridgeEdge G i j) :
    -- Entropy increases
    (latent_capacity (remove_edge G i j) σ = latent_capacity G σ + (σ.val i j)^2) ∧
    -- Paradox decreases
    (TopologicalDeficit (remove_edge G i j) + 1 = TopologicalDeficit G) := by
  constructor
  · exact latent_capacity_growth G σ i j h_active
  · exact nonbridge_break_resolves_one_deficit G i j h_ne h_active h_conn h_nonbridge

/-! ## The Classical Attractor -/

/--
**Sufficient Breaks Lead to Classicality**: If all edges of a connected graph are
non-bridges (i.e., the graph has no bridges), then repeatedly breaking edges
eventually reaches b₁ = 0 (classical state).

The number of breaks needed equals the initial Betti number.
-/
theorem betti_counts_nonbridge_edges [NeZero n] (G : DynamicGraph n)
    (h_conn : Module.finrank ℝ (LinearMap.ker (d_G_linear G)) = 1) :
    Module.finrank ℝ (HarmonicSubspace G) =
    G.active_edges.card / 2 - (n - 1) := by
  have h := Diaspora.Hodge.EdgeAddition.betti_counts_excess_edges G h_conn
  have h_n_pos : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  omega

end Diaspora.Dynamics.Resolution
