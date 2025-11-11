/-
# Unified Conservation of Holonomy

Proves the two fundamental conservation laws that govern holonomy in all merging scenarios:

1. **Law of Emergence** (Dynamic Topology): Merging open paths creates manifest holonomy
   equal to the sum of their latent holonomies: K_final = K₁ + K₂

2. **Law of Averaging** (Static Topology): Merging systems with a shared cycle averages
   their manifest holonomies: K_final = (K₁ + K₂)/2

These laws show that holonomy is conserved during topological transformations,
whether creating new cycles (emergence) or reconciling existing ones (averaging).
-/

import Diaspora.GaugeTheoreticHolonomy
import Mathlib.Algebra.BigOperators.Field

open GaugeTheoretic

namespace ConservationOfHolonomy

/-! ## Part 1: Open Paths and Latent Holonomy -/

/-- An open path: k edges with distinct start and end nodes -/
structure Path (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) where
  /-- The nodes in the path (length k+1) -/
  nodes : Fin (k+1) → Fin n
  /-- Path property: first node ≠ last node (open path) -/
  open_path : nodes 0 ≠ nodes ⟨k, Nat.lt_succ_self k⟩
  /-- Consecutive nodes are adjacent -/
  adjacent : ∀ (i : Fin k), G.Adj (nodes i.castSucc) (nodes i.succ)
  /-- Edges are distinct (no edge is traversed twice) -/
  distinct_edges : ∀ (i j : Fin k),
    (nodes i.castSucc, nodes i.succ) = (nodes j.castSucc, nodes j.succ) → i = j

/-- Latent holonomy: sum of constraints along an open path -/
noncomputable def latent_holonomy {n k : ℕ} (X : ConfigSpace n) (p : Path n X.graph k) : ℝ :=
  ∑ i : Fin k, X.constraints (p.nodes i.castSucc) (p.nodes i.succ) (p.adjacent i)

/-! ## Part 2: Law of Emergence (Dynamic Topology)

When two open paths are merged to form a cycle, the manifest holonomy of the
resulting cycle equals the sum of the latent holonomies of the constituent paths.

This proves conservation during topological change: latent → manifest.
-/

/-- Two paths that can be merged to form a cycle -/
structure MergeablePaths (n : ℕ) (G : SimpleGraph (Fin n)) (k₁ k₂ : ℕ) where
  /-- First path -/
  path₁ : Path n G k₁
  /-- Second path -/
  path₂ : Path n G k₂
  /-- Paths connect: end of path₁ = start of path₂ -/
  connects₁ : path₁.nodes ⟨k₁, Nat.lt_succ_self k₁⟩ = path₂.nodes 0
  /-- Paths close: end of path₂ = start of path₁ -/
  connects₂ : path₂.nodes ⟨k₂, Nat.lt_succ_self k₂⟩ = path₁.nodes 0
  /-- The paths are edge-disjoint (they don't share any internal edges) -/
  h_disjoint : ∀ (i : Fin k₁) (j : Fin k₂),
    (path₁.nodes i.castSucc, path₁.nodes i.succ) ≠
    (path₂.nodes j.castSucc, path₂.nodes j.succ)

/-- Merging two paths creates a cycle -/
noncomputable def merge_to_cycle {n k₁ k₂ : ℕ} {G : SimpleGraph (Fin n)}
    (mp : MergeablePaths n G k₁ k₂) : Cycle n G (k₁ + k₂) := {
  nodes := fun i =>
    if h : i.val < k₁ then
      mp.path₁.nodes ⟨i.val, by omega⟩
    else
      mp.path₂.nodes ⟨i.val - k₁, by omega⟩
  closes := by
    -- Prove cycle closes: nodes[0] = nodes[k₁ + k₂]
    -- We'll show k₁ > 0, then use mp.connects₂
    by_cases h_k : (0 : ℕ) < k₁
    · -- Case: k₁ > 0
      have h_0 : (0 : Fin (k₁ + k₂ + 1)).val < k₁ := by simpa using h_k
      rw [dif_pos h_0]
      have h_ne : ¬((⟨k₁ + k₂, by omega⟩ : Fin (k₁ + k₂ + 1)).val < k₁) := by simp
      rw [dif_neg h_ne]
      -- Goal: path₁.nodes[0] = path₂.nodes[k₁ + k₂ - k₁]
      have h_eq : ⟨k₁ + k₂ - k₁, by omega⟩ = (⟨k₂, Nat.lt_succ_self k₂⟩ : Fin (k₂ + 1)) := by
        congr 1
        omega
      rw [h_eq]
      exact mp.connects₂.symm
    · -- Case: k₁ = 0, impossible
      exfalso
      have : k₁ = 0 := by omega
      subst this
      exact mp.path₁.open_path rfl
  adjacent := by
    intro i
    -- Strategy: Case split on whether edge is in path₁, path₂, or connects them
    -- Show: if i.castSucc.val < k₁ then ... else ... is adjacent to if i.succ.val < k₁ then ... else ...
    by_cases h_start : i.castSucc.val < k₁
    · -- First node comes from path₁
      rw [dif_pos h_start]
      by_cases h_end : i.succ.val < k₁
      · -- Both nodes from path₁: use path₁.adjacent
        rw [dif_pos h_end]
        -- Goal: G.Adj (path₁.nodes ⟨i.castSucc.val, _⟩) (path₁.nodes ⟨i.succ.val, _⟩)
        -- This follows from path₁.adjacent for the corresponding Fin k₁ index
        have h_i_lt : i.val < k₁ := by
          have : i.castSucc.val = i.val := by simp [Fin.castSucc]
          omega
        convert mp.path₁.adjacent ⟨i.val, h_i_lt⟩ using 2
      · -- Boundary case: edge from last node of path₁ to first node of path₂
        -- i.castSucc.val < k₁ but i.succ.val ≥ k₁
        -- So i.val = k₁ - 1 and i.succ.val = k₁
        have h_i_val : i.val = k₁ - 1 := by
          have : i.castSucc.val = i.val := by simp [Fin.castSucc]
          have : i.succ.val = i.val + 1 := by simp [Fin.succ]
          omega
        have h_succ_val : i.succ.val = k₁ := by simp [Fin.succ, h_i_val]; omega
        rw [dif_neg h_end]
        -- Goal: G.Adj (path₁.nodes[k₁-1]) (path₂.nodes[0])
        -- Use path₁.adjacent to get G.Adj (path₁.nodes[k₁-1]) (path₁.nodes[k₁])
        -- Then use mp.connects₁: path₁.nodes[k₁] = path₂.nodes[0]
        have h_k1_ge : 1 ≤ k₁ := by omega
        have h_adj : G.Adj (mp.path₁.nodes ((⟨k₁ - 1, by omega⟩ : Fin k₁).castSucc))
                           (mp.path₁.nodes ((⟨k₁ - 1, by omega⟩ : Fin k₁).succ)) :=
          mp.path₁.adjacent (⟨k₁ - 1, by omega⟩ : Fin k₁)
        simp [Fin.castSucc, Fin.succ] at h_adj
        -- h_adj: G.Adj (path₁.nodes[k₁-1]) (path₁.nodes[k₁-1+1])
        -- Need: G.Adj (path₁.nodes[i.castSucc.val]) (path₂.nodes[i.succ.val - k₁])
        have h_simp : k₁ - 1 + 1 = k₁ := by omega
        simp only [h_simp] at h_adj
        have h1 : mp.path₁.nodes ⟨i.castSucc.val, by omega⟩ = mp.path₁.nodes ⟨k₁ - 1, by omega⟩ := by
          congr 1; ext; simp; omega
        have h2 : mp.path₂.nodes ⟨i.succ.val - k₁, by omega⟩ = mp.path₁.nodes ⟨k₁, Nat.lt_succ_self k₁⟩ := by
          have : (⟨i.succ.val - k₁, by omega⟩ : Fin (k₂ + 1)) = 0 := by
            ext
            simp [Fin.succ, h_i_val]
            omega
          rw [this, ← mp.connects₁]
        rw [h1, h2]
        exact h_adj
    · -- First node comes from path₂
      rw [dif_neg h_start]
      -- Second node must also come from path₂ (since i.succ.val > i.castSucc.val ≥ k₁)
      have h_end : ¬(i.succ.val < k₁) := by
        have : i.castSucc.val ≤ i.succ.val := by simp [Fin.castSucc, Fin.succ]
        omega
      rw [dif_neg h_end]
      -- Both from path₂: use path₂.adjacent
      -- Goal: G.Adj (path₂.nodes[i.castSucc.val - k₁]) (path₂.nodes[i.succ.val - k₁])
      -- Map i to the corresponding index in path₂
      have h_i_ge : k₁ ≤ i.val := by
        have : i.castSucc.val = i.val := by simp [Fin.castSucc]
        omega
      have h_adj : G.Adj (mp.path₂.nodes ((⟨i.val - k₁, by omega⟩ : Fin k₂).castSucc))
                         (mp.path₂.nodes ((⟨i.val - k₁, by omega⟩ : Fin k₂).succ)) :=
        mp.path₂.adjacent (⟨i.val - k₁, by omega⟩ : Fin k₂)
      simp [Fin.castSucc, Fin.succ] at h_adj
      -- h_adj: G.Adj (path₂.nodes[i.val - k₁]) (path₂.nodes[i.val - k₁ + 1])
      -- Need: G.Adj (path₂.nodes[i.castSucc.val - k₁]) (path₂.nodes[i.succ.val - k₁])
      have h1 : mp.path₂.nodes ⟨i.castSucc.val - k₁, by omega⟩ = mp.path₂.nodes ⟨i.val - k₁, by omega⟩ := by
        congr 1
      have h2 : mp.path₂.nodes ⟨i.succ.val - k₁, by omega⟩ = mp.path₂.nodes ⟨i.val - k₁ + 1, by omega⟩ := by
        congr 1
        ext
        simp [Fin.succ]
        omega
      rw [h1, h2]
      exact h_adj
  distinct_edges := by
    intro i j h_eq
    -- Strategy: Case analysis on which paths the edges come from
    by_cases h_i_start : i.castSucc.val < k₁
    · -- First node of edge i comes from path₁
      by_cases h_i_end : i.succ.val < k₁
      · -- Edge i entirely in path₁
        by_cases h_j_start : j.castSucc.val < k₁
        · -- First node of edge j comes from path₁
          by_cases h_j_end : j.succ.val < k₁
          · -- Both edges entirely in path₁
            -- Simplify the edge equation
            simp only [dif_pos h_i_start, dif_pos h_i_end, dif_pos h_j_start, dif_pos h_j_end] at h_eq
            -- Extract Fin k₁ indices for the edges
            have h_i_lt : i.val < k₁ := by
              have : i.castSucc.val = i.val := by simp [Fin.castSucc]
              omega
            have h_j_lt : j.val < k₁ := by
              have : j.castSucc.val = j.val := by simp [Fin.castSucc]
              omega
            -- Build path₁ edge equality
            have h_path_eq : (mp.path₁.nodes (⟨i.val, h_i_lt⟩ : Fin k₁).castSucc,
                              mp.path₁.nodes (⟨i.val, h_i_lt⟩ : Fin k₁).succ) =
                             (mp.path₁.nodes (⟨j.val, h_j_lt⟩ : Fin k₁).castSucc,
                              mp.path₁.nodes (⟨j.val, h_j_lt⟩ : Fin k₁).succ) := by
              simp [Fin.castSucc, Fin.succ] at h_eq ⊢
              exact h_eq
            -- Apply path₁.distinct_edges
            have : (⟨i.val, h_i_lt⟩ : Fin k₁) = (⟨j.val, h_j_lt⟩ : Fin k₁) :=
              mp.path₁.distinct_edges _ _ h_path_eq
            -- Conclude i = j
            ext
            simp at this
            exact this
          · -- Edge i in path₁, edge j is boundary
            -- Edge i: both nodes from path₁ (i.succ.val < k₁)
            -- Edge j: first from path₁, second from path₂ (j.succ.val ≥ k₁)
            -- Cannot be equal: second nodes come from different sources
            simp only [dif_pos h_i_start, dif_pos h_i_end, dif_pos h_j_start, dif_neg h_j_end] at h_eq
            -- h_eq says: (path₁.nodes ⟨i.val, _⟩, path₁.nodes ⟨i.succ.val, _⟩) =
            --            (path₁.nodes ⟨j.castSucc.val, _⟩, path₂.nodes ⟨j.succ.val - k₁, _⟩)
            exfalso
            -- The second components contradict each other
            have h_contra : mp.path₁.nodes ⟨i.succ.val, by omega⟩ = mp.path₂.nodes ⟨j.succ.val - k₁, by omega⟩ := by
              have := congr_arg Prod.snd h_eq
              exact this
            -- path₁.nodes ⟨i.succ.val, _⟩ = path₂.nodes ⟨j.succ.val - k₁, _⟩
            -- But j.succ.val ≥ k₁, so j.succ.val - k₁ = something ≥ 0
            -- And j.castSucc.val < k₁, j.succ.val = j.val + 1, so j.val < k₁, thus j.val + 1 could be = k₁
            have h_j_val_eq : j.val = k₁ - 1 := by
              have : j.castSucc.val = j.val := by simp [Fin.castSucc]
              have : j.succ.val = j.val + 1 := by simp [Fin.succ]
              omega
            have h_j_succ_eq : j.succ.val = k₁ := by simp [Fin.succ, h_j_val_eq]; omega
            -- j.succ.val - k₁ = 0
            have h_j_idx : (⟨j.succ.val - k₁, by omega⟩ : Fin (k₂ + 1)) = 0 := by
              ext; simp; omega
            -- Edge i has both nodes accessed via path₁ indices < k₁
            -- Edge j has first node via path₁, second via path₂
            -- If the edges (as pairs) are equal, the first components give us:
            -- path₁.nodes ⟨i.castSucc.val, _⟩ = path₁.nodes ⟨j.castSucc.val, _⟩
            -- The second components give us:
            -- path₁.nodes ⟨i.succ.val, _⟩ = path₂.nodes ⟨j.succ.val - k₁, _⟩
            -- We know j.succ.val = k₁, so j.succ.val - k₁ = 0
            -- Thus: path₁.nodes ⟨i.succ.val, _⟩ = path₂.nodes 0
            -- By connects₁: path₂.nodes 0 = path₁.nodes k₁
            -- So: path₁.nodes ⟨i.succ.val, _⟩ = path₁.nodes k₁
            -- But i.succ.val < k₁, so i.succ.val ≠ k₁
            -- Nodes of a path CAN revisit, so this doesn't immediately give contradiction
            -- However: we also have from first components that the edges START at the same node
            -- And if i ≠ j but they start at the same node and form equal edges,
            -- then by distinct_edges property of the cycle, they must be the same edge index
            -- Actually, the simplest approach: j.val = k₁-1 means j is the boundary edge index
            -- But we assumed j.castSucc.val < k₁, so j.val < k₁
            -- And j.val = k₁-1 with j.succ.val = k₁ means the edge crosses the boundary
            -- Meanwhile i.succ.val < k₁ means edge i is entirely in path₁
            -- These are accessing different "logical" edges in the merged cycle
            -- even if the nodes might overlap. The cycle's distinct_edges will handle this.
            -- But we're PROVING distinct_edges! Can't use it.
            -- Let me use: i and j have the same first node index in merge_to_cycle
            -- i.castSucc.val and j.castSucc.val are both < k₁
            -- So they map to the same path₁.nodes call
            -- For them to give the same node, we'd need i.castSucc.val = j.castSucc.val
            -- Thus i.val = j.val
            -- Edge i: entirely in path₁ (i.val < k₁ - 1)
            -- Edge j: the boundary edge (j.val = k₁ - 1)
            -- Both edges are actually edges OF path₁!
            -- Edge i in merged cycle = edge ⟨i.val, _⟩ in path₁
            -- Edge j in merged cycle = edge ⟨k₁ - 1, _⟩ in path₁ (the last edge)
            -- Since i.val < k₁ - 1, these are distinct edges in path₁
            -- By path₁.distinct_edges, they have distinct node pairs
            have h_i_val_lt : i.val < k₁ - 1 := by
              have : i.succ.val = i.val + 1 := by simp [Fin.succ]
              omega
            -- Since i.val < k₁ - 1 and j.val = k₁ - 1, we have i.val ≠ j.val
            -- But the first components of the edges must be equal (from h_eq)
            -- Both edges start from nodes with indices i.val and j.val respectively
            -- Since these are distinct and both < k₁, they map to potentially different nodes
            -- However, for the edges to be equal, the nodes must be the same
            -- Use path₁.distinct_edges on the subproblem
            -- Edge i corresponds to path₁ edge at index i.val < k₁ - 1
            -- Edge j is the boundary, which is path₁'s last edge at index k₁ - 1
            -- These are distinct edges in path₁ (different indices)
            -- But h_eq claims they produce the same node pair in the merged cycle
            -- This is impossible since path₁.distinct_edges says distinct indices → distinct edges
            have : i.val = k₁ - 1 := by
              -- Both edges can be viewed as path₁ edges
              -- Edge i: (path₁.nodes ⟨i.val, _⟩, path₁.nodes ⟨i.val+1, _⟩)
              -- Edge j: (path₁.nodes ⟨k₁-1, _⟩, path₂.nodes 0) = (path₁.nodes ⟨k₁-1, _⟩, path₁.nodes k₁)
              -- The second equality uses mp.connects₁
              -- From h_eq, we have both edges equal
              have h_first := congr_arg Prod.fst h_eq
              have h_second := congr_arg Prod.snd h_eq
              -- h_second: mp.path₁.nodes ⟨i.succ.val, _⟩ = mp.path₂.nodes ⟨j.succ.val - k₁, _⟩
              -- Since j.succ.val = k₁, we have j.succ.val - k₁ = 0
              rw [h_j_idx] at h_second
              -- h_second: mp.path₁.nodes ⟨i.succ.val, _⟩ = mp.path₂.nodes 0
              -- Use mp.connects₁: path₁.nodes k₁ = path₂.nodes 0
              have h_connects : mp.path₁.nodes ⟨k₁, Nat.lt_succ_self k₁⟩ = mp.path₂.nodes 0 := mp.connects₁
              rw [← h_connects] at h_second
              -- h_second: mp.path₁.nodes ⟨i.succ.val, _⟩ = mp.path₁.nodes ⟨k₁, _⟩
              -- Also simplify j.castSucc.val to k₁ - 1
              have h_j_cast : j.castSucc.val = k₁ - 1 := by simp [Fin.castSucc, h_j_val_eq]
              -- h_first: mp.path₁.nodes ⟨i.val, _⟩ = mp.path₁.nodes ⟨j.castSucc.val, _⟩
              --        = mp.path₁.nodes ⟨k₁ - 1, _⟩
              -- Now we have: edge i = (path₁.nodes ⟨i.val, _⟩, path₁.nodes ⟨i.succ.val, _⟩)
              --        and this equals (path₁.nodes ⟨k₁-1, _⟩, path₁.nodes k₁)
              -- These are both edges of path₁
              -- Edge i has index ⟨i.val, _⟩ where i.val < k₁ - 1
              -- The other edge has index ⟨k₁ - 1, _⟩
              -- By path₁.distinct_edges, if edges are equal, indices are equal
              have h_i_succ : i.succ.val = i.val + 1 := by simp [Fin.succ]
              have h_path_edges_eq : (mp.path₁.nodes (⟨i.val, by omega⟩ : Fin k₁).castSucc,
                                       mp.path₁.nodes (⟨i.val, by omega⟩ : Fin k₁).succ) =
                                      (mp.path₁.nodes (⟨k₁ - 1, by omega⟩ : Fin k₁).castSucc,
                                       mp.path₁.nodes (⟨k₁ - 1, by omega⟩ : Fin k₁).succ) := by
                simp [Fin.castSucc, Fin.succ]
                constructor
                · -- First component
                  have : (⟨i.val, by omega⟩ : Fin (k₁ + 1)) = (⟨i.val, by omega⟩ : Fin k₁).castSucc := by
                    ext; simp [Fin.castSucc]
                  rw [this]
                  have : (⟨k₁ - 1, by omega⟩ : Fin (k₁ + 1)) = (⟨j.castSucc.val, by omega⟩ : Fin (k₁ + 1)) := by
                    ext; simp; omega
                  rw [this]; exact h_first
                · -- Second component
                  -- h_second is simplified version: path₁.nodes ⟨i.succ.val, _⟩ = path₁.nodes ⟨k₁, _⟩
                  -- Goal: mp.path₁.nodes ⟨i.val + 1, _⟩ = mp.path₁.nodes ⟨k₁ - 1 + 1, _⟩
                  -- Show i.val + 1 = i.succ.val and k₁ - 1 + 1 = k₁
                  have h_i_eq : (⟨i.val + 1, by omega⟩ : Fin (k₁ + 1)) = ⟨i.succ.val, by omega⟩ := by
                    ext; rw [h_i_succ]
                  have h_k_eq : (⟨k₁ - 1 + 1, by omega⟩ : Fin (k₁ + 1)) = ⟨k₁, by omega⟩ := by
                    ext
                    simp
                    -- We know j.val = k₁ - 1 and j.val < k₁ + k₂, so k₁ > 0
                    have h_k₁_pos : 0 < k₁ := by
                      have : j.val < k₁ + k₂ := j.isLt
                      omega
                    -- Now use: k₁ - 1 + 1 = k₁ when k₁ > 0
                    have : k₁ - 1 + 1 = k₁ := Nat.sub_add_cancel h_k₁_pos
                    exact this
                  rw [h_i_eq, h_k_eq]; exact h_second
              have h_idx_eq := mp.path₁.distinct_edges ⟨i.val, by omega⟩ ⟨k₁ - 1, by omega⟩ h_path_edges_eq
              -- h_idx_eq : ⟨i.val, _⟩ = ⟨k₁ - 1, _⟩
              have : i.val = k₁ - 1 := by
                have := congr_arg Fin.val h_idx_eq
                exact this
              exact this
            omega
        · -- Edge i in path₁, edge j in path₂
          -- Edge i: entirely in path₁ (i.val < k₁)
          -- Edge j: entirely in path₂ (j.val ≥ k₁)
          -- By h_disjoint, path₁ and path₂ don't share edges
          simp only [dif_pos h_i_start, dif_pos h_i_end, dif_neg h_j_start] at h_eq
          exfalso
          -- Build Fin k₂ index for edge j in path₂
          have h_j_succ : ¬(j.succ.val < k₁) := by
            have : j.castSucc.val ≤ j.succ.val := by simp [Fin.castSucc, Fin.succ]
            omega
          simp only [dif_neg h_j_succ] at h_eq
          -- Now h_eq says edge from path₁ equals edge from path₂
          have h_i_idx : i.val < k₁ := by
            have : i.castSucc.val = i.val := by simp [Fin.castSucc]
            omega
          have h_j_idx : k₁ ≤ j.val := by
            have : j.castSucc.val = j.val := by simp [Fin.castSucc]
            omega
          -- Edge i in path₁: index ⟨i.val, _⟩
          -- Edge j in path₂: index ⟨j.val - k₁, _⟩
          -- h_eq says two edges are equal, but they're from disjoint paths
          -- Extract the edge equality in the form we need
          have h_first := congr_arg Prod.fst h_eq
          have h_second := congr_arg Prod.snd h_eq
          have h_path_eq : (mp.path₁.nodes (⟨i.val, h_i_idx⟩ : Fin k₁).castSucc,
                            mp.path₁.nodes (⟨i.val, h_i_idx⟩ : Fin k₁).succ) =
                           (mp.path₂.nodes (⟨j.val - k₁, by omega⟩ : Fin k₂).castSucc,
                            mp.path₂.nodes (⟨j.val - k₁, by omega⟩ : Fin k₂).succ) := by
            simp [Fin.castSucc, Fin.succ]
            simp at h_first h_second
            constructor
            · exact h_first
            · -- h_second has j + 1 - k₁, but we need j - k₁ + 1
              have : (⟨j.val + 1 - k₁, by omega⟩ : Fin (k₂ + 1)) = (⟨j.val - k₁ + 1, by omega⟩ : Fin (k₂ + 1)) := by
                ext; simp; omega
              rw [← this]; exact h_second
          -- This contradicts h_disjoint
          exact mp.h_disjoint (⟨i.val, h_i_idx⟩ : Fin k₁) (⟨j.val - k₁, by omega⟩ : Fin k₂) h_path_eq
      · -- Edge i is the boundary edge
        -- i.castSucc.val < k₁ but i.succ.val ≥ k₁
        by_cases h_j_start : j.castSucc.val < k₁
        · by_cases h_j_end : j.succ.val < k₁
          · -- Edge i is boundary, edge j is in path₁
            -- Symmetric to previous case
            simp only [dif_pos h_i_start, dif_neg h_i_end, dif_pos h_j_start, dif_pos h_j_end] at h_eq
            exfalso
            -- Symmetric to previous case
            -- Edge i: the boundary edge (i.val = k₁ - 1)
            -- Edge j: entirely in path₁ (j.val < k₁ - 1)
            have h_i_val_eq : i.val = k₁ - 1 := by
              have : i.castSucc.val = i.val := by simp [Fin.castSucc]
              have : i.succ.val = i.val + 1 := by simp [Fin.succ]
              omega
            have h_j_val_lt : j.val < k₁ - 1 := by
              have : j.succ.val = j.val + 1 := by simp [Fin.succ]
              omega
            have h_j_val_lt_k₁ : j.val < k₁ := by omega
            -- Extract node equalities from h_eq
            have h_first := congr_arg Prod.fst h_eq
            have h_second := congr_arg Prod.snd h_eq
            -- Since i.succ.val = k₁, we have i.succ.val - k₁ = 0
            -- So h_second says mp.path₂.nodes 0 = mp.path₁.nodes ⟨j.succ⟩
            -- But mp.path₂.nodes 0 = mp.path₁.nodes k₁ (by connects₁)
            -- Build the path₁ edge equality
            -- h_first: mp.path₁.nodes ⟨i.castSucc⟩ = mp.path₁.nodes ⟨j.castSucc⟩
            -- Since i.castSucc = k₁ - 1 and j.castSucc = j.val, we have:
            -- mp.path₁.nodes ⟨k₁ - 1⟩ = mp.path₁.nodes ⟨j.val⟩
            -- Similarly, h_second tells us about the succ values
            -- i.succ = k₁, so mp.path₂.nodes ⟨i.succ - k₁⟩ = mp.path₂.nodes ⟨0⟩ = mp.path₁.nodes k₁
            --  = mp.path₁.nodes ⟨j.succ⟩
            -- These two equalities together form the path₁ edge equality
            have h_path_eq : (mp.path₁.nodes (⟨k₁ - 1, by omega⟩ : Fin k₁).castSucc,
                              mp.path₁.nodes (⟨k₁ - 1, by omega⟩ : Fin k₁).succ) =
                             (mp.path₁.nodes (⟨j.val, h_j_val_lt_k₁⟩ : Fin k₁).castSucc,
                              mp.path₁.nodes (⟨j.val, h_j_val_lt_k₁⟩ : Fin k₁).succ) := by
              simp [Fin.castSucc, Fin.succ]
              simp at h_first h_second
              -- We know i = k₁ - 1, so after simp h_first has mp.path₁.nodes ⟨i⟩ = mp.path₁.nodes ⟨j⟩
              -- We need mp.path₁.nodes ⟨k₁ - 1⟩ = mp.path₁.nodes ⟨j⟩
              -- But ⟨i⟩ = ⟨k₁ - 1⟩ since i = k₁ - 1
              constructor
              · have : (⟨i.val, by omega⟩ : Fin (k₁ + 1)) = (⟨k₁ - 1, by omega⟩ : Fin (k₁ + 1)) := by ext; omega
                rw [← this]; exact h_first
              · -- h_second: mp.path₂.nodes ⟨i + 1 - k₁⟩ = mp.path₁.nodes ⟨j + 1⟩
                -- Since i = k₁ - 1, we have i + 1 = k₁, so i + 1 - k₁ = 0
                have h_eq_0 : (⟨i.val + 1 - k₁, by omega⟩ : Fin (k₂ + 1)) = 0 := by ext; simp; omega
                rw [h_eq_0, ← mp.connects₁] at h_second
                -- h_second now has mp.path₁.nodes ⟨k₁⟩ = mp.path₁.nodes ⟨j + 1⟩
                -- We need mp.path₁.nodes ⟨k₁ - 1 + 1⟩ = mp.path₁.nodes ⟨j + 1⟩
                -- But ⟨k₁⟩ = ⟨k₁ - 1 + 1⟩
                have : (⟨k₁, by omega⟩ : Fin (k₁ + 1)) = (⟨k₁ - 1 + 1, by omega⟩ : Fin (k₁ + 1)) := by ext; simp; omega
                rw [← this]; exact h_second
            have : (⟨k₁ - 1, by omega⟩ : Fin k₁) = (⟨j.val, h_j_val_lt_k₁⟩ : Fin k₁) :=
              mp.path₁.distinct_edges _ _ h_path_eq
            simp at this
            omega
          · -- Both edges are boundary - only one boundary edge exists
            -- i and j must be the same boundary edge
            have h_i_val : i.val = k₁ - 1 := by
              have : i.castSucc.val = i.val := by simp [Fin.castSucc]
              have : i.succ.val = i.val + 1 := by simp [Fin.succ]
              omega
            have h_j_val : j.val = k₁ - 1 := by
              have : j.castSucc.val = j.val := by simp [Fin.castSucc]
              have : j.succ.val = j.val + 1 := by simp [Fin.succ]
              omega
            ext
            omega
        · -- Edge i is boundary, edge j is in path₂
          -- Edge i: boundary edge (i.val = k₁ - 1), last edge of path₁
          -- Edge j: entirely in path₂ (j.val ≥ k₁)
          -- By h_disjoint, these can't be equal
          simp only [dif_pos h_i_start, dif_neg h_i_end, dif_neg h_j_start] at h_eq
          exfalso
          have h_i_val_eq : i.val = k₁ - 1 := by
            have : i.castSucc.val = i.val := by simp [Fin.castSucc]
            have : i.succ.val = i.val + 1 := by simp [Fin.succ]
            omega
          have h_j_idx : k₁ ≤ j.val := by
            have : j.castSucc.val = j.val := by simp [Fin.castSucc]
            omega
          have h_j_succ : ¬(j.succ.val < k₁) := by
            have : j.castSucc.val ≤ j.succ.val := by simp [Fin.castSucc, Fin.succ]
            omega
          simp only [dif_neg h_j_succ] at h_eq
          -- Edge i is the last edge of path₁: (path₁.nodes (k₁-1), path₁.nodes k₁)
          -- Edge j is an edge of path₂: (path₂.nodes (j.val - k₁), path₂.nodes (j.val - k₁ + 1))
          -- From h_eq, extract that path₁.nodes k₁ = path₂.nodes (j.val - k₁)
          have h_i_eq_k₁ : i.val = k₁ - 1 := h_i_val_eq
          have h_i_succ_eq : i.succ.val = k₁ := by simp [Fin.succ]; omega
          have h_first : mp.path₁.nodes ⟨i.castSucc, by omega⟩ =
                         mp.path₂.nodes ⟨j.castSucc.val - k₁, by omega⟩ :=
            congr_arg Prod.fst h_eq
          have h_second : mp.path₂.nodes ⟨i.succ.val - k₁, by omega⟩ =
                          mp.path₂.nodes ⟨j.succ.val - k₁, by omega⟩ :=
            congr_arg Prod.snd h_eq
          -- Since i.succ.val = k₁, we have i.succ.val - k₁ = 0
          have h_i_succ_sub : i.succ.val - k₁ = 0 := by omega
          -- So mp.path₂.nodes 0 = mp.path₂.nodes ⟨j.succ.val - k₁, _⟩
          -- But mp.path₂.nodes 0 = mp.path₁.nodes k₁ (by connects₁)
          -- This gives us the path equality we need
          have h_path_eq : (mp.path₁.nodes (⟨k₁ - 1, by omega⟩ : Fin k₁).castSucc,
                            mp.path₁.nodes (⟨k₁ - 1, by omega⟩ : Fin k₁).succ) =
                           (mp.path₂.nodes (⟨j.val - k₁, by omega⟩ : Fin k₂).castSucc,
                            mp.path₂.nodes (⟨j.val - k₁, by omega⟩ : Fin k₂).succ) := by
            simp [Fin.castSucc, Fin.succ]
            simp at h_first h_second
            -- i.val = k₁ - 1 and i.succ.val = k₁
            constructor
            · have : (⟨i.val, by omega⟩ : Fin (k₁ + 1)) = (⟨k₁ - 1, by omega⟩ : Fin (k₁ + 1)) := by ext; omega
              rw [← this]; exact h_first
            · -- h_second: mp.path₂.nodes ⟨i + 1 - k₁⟩ = mp.path₂.nodes ⟨j + 1 - k₁⟩
              -- i + 1 = k₁, so i + 1 - k₁ = 0
              have : (⟨i.val + 1 - k₁, by omega⟩ : Fin (k₂ + 1)) = 0 := by ext; simp; omega
              rw [this, ← mp.connects₁] at h_second
              -- h_second now has: mp.path₁.nodes ⟨k₁⟩ = mp.path₂.nodes ⟨j + 1 - k₁⟩
              -- We need: mp.path₁.nodes ⟨k₁ - 1 + 1⟩ = mp.path₂.nodes ⟨j - k₁ + 1⟩
              have h_lhs : (⟨k₁, by omega⟩ : Fin (k₁ + 1)) = (⟨k₁ - 1 + 1, by omega⟩ : Fin (k₁ + 1)) := by ext; simp; omega
              have h_rhs : (⟨j.val + 1 - k₁, by omega⟩ : Fin (k₂ + 1)) = (⟨j.val - k₁ + 1, by omega⟩ : Fin (k₂ + 1)) := by
                ext; simp; omega
              rw [← h_lhs, ← h_rhs]; exact h_second
          exact mp.h_disjoint (⟨k₁ - 1, by omega⟩ : Fin k₁) (⟨j.val - k₁, by omega⟩ : Fin k₂) h_path_eq
    · -- Edge i comes from path₂
      by_cases h_j : j.castSucc.val < k₁
      · -- Edge i from path₂, edge j from path₁
        -- Symmetric to "edge i from path₁, edge j from path₂"
        -- By h_disjoint, these can't be equal
        exfalso
        -- Determine whether j is in path₁ interior or boundary
        by_cases h_j_end : j.succ.val < k₁
        · -- Edge j entirely in path₁
          simp only [dif_neg h_i_start, dif_pos h_j, dif_pos h_j_end] at h_eq
          have h_i_idx : k₁ ≤ i.val := by
            have : i.castSucc.val = i.val := by simp [Fin.castSucc]
            omega
          have h_j_idx : j.val < k₁ := by
            have : j.castSucc.val = j.val := by simp [Fin.castSucc]
            omega
          have h_i_succ : ¬(i.succ.val < k₁) := by
            have : i.castSucc.val ≤ i.succ.val := by simp [Fin.castSucc, Fin.succ]
            omega
          simp only [dif_neg h_i_succ] at h_eq
          have h_first := congr_arg Prod.fst h_eq
          have h_second := congr_arg Prod.snd h_eq
          have h_path_eq : (mp.path₂.nodes (⟨i.val - k₁, by omega⟩ : Fin k₂).castSucc,
                            mp.path₂.nodes (⟨i.val - k₁, by omega⟩ : Fin k₂).succ) =
                           (mp.path₁.nodes (⟨j.val, h_j_idx⟩ : Fin k₁).castSucc,
                            mp.path₁.nodes (⟨j.val, h_j_idx⟩ : Fin k₁).succ) := by
            simp [Fin.castSucc, Fin.succ]
            simp at h_first h_second
            constructor
            · exact h_first
            · have : (⟨i.val + 1 - k₁, by omega⟩ : Fin (k₂ + 1)) = (⟨i.val - k₁ + 1, by omega⟩ : Fin (k₂ + 1)) := by
                ext; simp; omega
              rw [← this]; exact h_second
          exact mp.h_disjoint (⟨j.val, h_j_idx⟩ : Fin k₁) (⟨i.val - k₁, by omega⟩ : Fin k₂) h_path_eq.symm
        · -- Edge j is the boundary edge
          simp only [dif_neg h_i_start, dif_pos h_j, dif_neg h_j_end] at h_eq
          have h_j_val_eq : j.val = k₁ - 1 := by
            have : j.castSucc.val = j.val := by simp [Fin.castSucc]
            have : j.succ.val = j.val + 1 := by simp [Fin.succ]
            omega
          have h_i_idx : k₁ ≤ i.val := by
            have : i.castSucc.val = i.val := by simp [Fin.castSucc]
            omega
          have h_i_succ : ¬(i.succ.val < k₁) := by
            have : i.castSucc.val ≤ i.succ.val := by simp [Fin.castSucc, Fin.succ]
            omega
          simp only [dif_neg h_i_succ] at h_eq
          -- Edge j is the boundary edge, edge i is in path₂
          -- Symmetric to the previous case
          have h_j_succ_eq : j.succ.val = k₁ := by simp [Fin.succ]; omega
          have h_first : mp.path₂.nodes ⟨i.castSucc.val - k₁, by omega⟩ =
                         mp.path₁.nodes ⟨j.castSucc, by omega⟩ :=
            congr_arg Prod.fst h_eq
          have h_second : mp.path₂.nodes ⟨i.succ.val - k₁, by omega⟩ =
                          mp.path₂.nodes ⟨j.succ.val - k₁, by omega⟩ :=
            congr_arg Prod.snd h_eq
          have h_path_eq : (mp.path₂.nodes (⟨i.val - k₁, by omega⟩ : Fin k₂).castSucc,
                            mp.path₂.nodes (⟨i.val - k₁, by omega⟩ : Fin k₂).succ) =
                           (mp.path₁.nodes (⟨k₁ - 1, by omega⟩ : Fin k₁).castSucc,
                            mp.path₁.nodes (⟨k₁ - 1, by omega⟩ : Fin k₁).succ) := by
            simp [Fin.castSucc, Fin.succ]
            simp at h_first h_second
            constructor
            · -- h_first: mp.path₂.nodes ⟨i - k₁⟩ = mp.path₁.nodes ⟨j⟩
              -- We need: mp.path₂.nodes ⟨i - k₁⟩ = mp.path₁.nodes ⟨k₁ - 1⟩
              -- But j = k₁ - 1
              have : (⟨j.val, by omega⟩ : Fin (k₁ + 1)) = (⟨k₁ - 1, by omega⟩ : Fin (k₁ + 1)) := by ext; omega
              rw [← this]; exact h_first
            · -- h_second: mp.path₂.nodes ⟨i + 1 - k₁⟩ = mp.path₂.nodes ⟨j + 1 - k₁⟩
              -- j + 1 = k₁, so j + 1 - k₁ = 0
              have : mp.path₂.nodes ⟨j.val + 1 - k₁, by omega⟩ = mp.path₂.nodes 0 := by
                congr 1; ext; simp; omega
              rw [this, ← mp.connects₁] at h_second
              -- h_second now has: mp.path₂.nodes ⟨i + 1 - k₁⟩ = mp.path₁.nodes ⟨k₁⟩
              -- We need: mp.path₂.nodes ⟨i - k₁ + 1⟩ = mp.path₁.nodes ⟨k₁ - 1 + 1⟩
              have h_lhs : (⟨i.val + 1 - k₁, by omega⟩ : Fin (k₂ + 1)) = (⟨i.val - k₁ + 1, by omega⟩ : Fin (k₂ + 1)) := by
                ext; simp; omega
              have h_rhs : (⟨k₁, by omega⟩ : Fin (k₁ + 1)) = (⟨k₁ - 1 + 1, by omega⟩ : Fin (k₁ + 1)) := by ext; simp; omega
              rw [← h_lhs, ← h_rhs]; exact h_second
          exact mp.h_disjoint (⟨k₁ - 1, by omega⟩ : Fin k₁) (⟨i.val - k₁, by omega⟩ : Fin k₂) h_path_eq.symm
      · -- Both edges from path₂
        -- Symmetric to "both edges from path₁"
        -- Use path₂.distinct_edges
        simp only [dif_neg h_i_start, dif_neg h_j] at h_eq
        have h_i_idx : k₁ ≤ i.val := by
          have : i.castSucc.val = i.val := by simp [Fin.castSucc]
          omega
        have h_j_idx : k₁ ≤ j.val := by
          have : j.castSucc.val = j.val := by simp [Fin.castSucc]
          omega
        have h_i_succ : ¬(i.succ.val < k₁) := by
          have : i.castSucc.val ≤ i.succ.val := by simp [Fin.castSucc, Fin.succ]
          omega
        have h_j_succ : ¬(j.succ.val < k₁) := by
          have : j.castSucc.val ≤ j.succ.val := by simp [Fin.castSucc, Fin.succ]
          omega
        simp only [dif_neg h_i_succ, dif_neg h_j_succ] at h_eq
        -- Build path₂ edge equality
        have h_first := congr_arg Prod.fst h_eq
        have h_second := congr_arg Prod.snd h_eq
        have h_path_eq : (mp.path₂.nodes (⟨i.val - k₁, by omega⟩ : Fin k₂).castSucc,
                          mp.path₂.nodes (⟨i.val - k₁, by omega⟩ : Fin k₂).succ) =
                         (mp.path₂.nodes (⟨j.val - k₁, by omega⟩ : Fin k₂).castSucc,
                          mp.path₂.nodes (⟨j.val - k₁, by omega⟩ : Fin k₂).succ) := by
          simp [Fin.castSucc, Fin.succ]
          simp at h_first h_second
          constructor
          · exact h_first
          · -- h_second has i + 1 - k₁ but we need i - k₁ + 1
            have : (⟨i.val + 1 - k₁, by omega⟩ : Fin (k₂ + 1)) = (⟨i.val - k₁ + 1, by omega⟩ : Fin (k₂ + 1)) := by
              ext; simp; omega
            have h_j_arith : (⟨j.val + 1 - k₁, by omega⟩ : Fin (k₂ + 1)) = (⟨j.val - k₁ + 1, by omega⟩ : Fin (k₂ + 1)) := by
              ext; simp; omega
            rw [← this, ← h_j_arith]; exact h_second
        -- Apply path₂.distinct_edges
        have : (⟨i.val - k₁, by omega⟩ : Fin k₂) = (⟨j.val - k₁, by omega⟩ : Fin k₂) :=
          mp.path₂.distinct_edges _ _ h_path_eq
        -- Conclude i = j
        ext
        simp at this
        omega
}

/-- **Law of Emergence**: K_cycle = K_path₁ + K_path₂

This is the conservation law for dynamic topology:
when open paths merge to create a cycle, latent holonomy becomes manifest,
and the total holonomy is preserved (summed).
-/
theorem law_of_emergence {n k₁ k₂ : ℕ} (X : ConfigSpace n)
    (mp : MergeablePaths n X.graph k₁ k₂) :
    cycle_holonomy X (merge_to_cycle mp) =
      latent_holonomy X mp.path₁ + latent_holonomy X mp.path₂ := by
  unfold cycle_holonomy latent_holonomy
  -- The cycle sum is over (k₁ + k₂) edges
  -- Split this into two parts: edges from path₁ and edges from path₂

  -- Key insight: The cycle's edges come from concatenating the two paths
  -- First k₁ edges correspond to path₁, next k₂ edges to path₂

  have split_sum : ∑ i : Fin (k₁ + k₂),
        X.constraints
          ((merge_to_cycle mp).nodes i.castSucc)
          ((merge_to_cycle mp).nodes i.succ)
          ((merge_to_cycle mp).adjacent i) =
      (∑ i : Fin k₁, X.constraints
          (mp.path₁.nodes i.castSucc)
          (mp.path₁.nodes i.succ)
          (mp.path₁.adjacent i)) +
      (∑ i : Fin k₂, X.constraints
          (mp.path₂.nodes i.castSucc)
          (mp.path₂.nodes i.succ)
          (mp.path₂.adjacent i)) := by
    -- Split the sum over Fin (k₁ + k₂) into two parts using Fin.sum_univ_add
    conv_lhs => rw [Fin.sum_univ_add]
    congr 1
    · -- First k₁ terms: show constraint at (castAdd k₂ i) matches path₁ at i
      congr 1
      ext i
      -- The constraint function is the same, so we just need to show the node arguments match
      congr 1
      · -- First node: (merge_to_cycle mp).nodes (castAdd k₂ i).castSucc = path₁.nodes i.castSucc
        unfold merge_to_cycle
        simp only [Fin.castSucc_castAdd]
        -- Show i.val < k₁ so the if picks the path₁ branch
        have h : (Fin.castAdd (k₂ + 1) i).val < k₁ := by
          simp only [Fin.castAdd]
          exact i.isLt
        rw [dif_pos h]
        rfl
      · -- Second node: (merge_to_cycle mp).nodes (castAdd k₂ i).succ = path₁.nodes i.succ
        unfold merge_to_cycle
        -- Check if we're at the boundary
        by_cases h_boundary : i.succ = Fin.last k₁
        · -- Case: i.succ = Fin.last k₁, boundary between path₁ and path₂
          -- At this boundary, the path connects to path₂
          simp [Fin.succ_castAdd, h_boundary]
          have : Fin.last k₁ = ⟨k₁, Nat.lt_succ_self k₁⟩ := rfl
          rw [this]
          exact mp.connects₁.symm
        · -- Case: i.succ ≠ Fin.last k₁, stays within path₁
          have h_val : (i : ℕ).succ < k₁ := by
            by_contra h_not
            push_neg at h_not
            have : i.succ = Fin.last k₁ := by
              ext
              simp only [Fin.last, Fin.succ]
              omega
            contradiction
          simp [Fin.succ_castAdd, h_boundary, h_val]
          rfl
    · -- Next k₂ terms: show constraint at (natAdd k₁ i) matches path₂ at i
      congr 1
      ext i
      congr 1
      · -- First node: (merge_to_cycle mp).nodes (natAdd k₁ i).castSucc = path₂.nodes i.castSucc
        unfold merge_to_cycle
        simp only [Fin.castSucc_natAdd]
        have h : ¬((Fin.natAdd k₁ i.castSucc).val < k₁) := by simp only [Fin.natAdd]; omega
        rw [dif_neg h]
        -- Need: path₂.nodes ⟨(natAdd k₁ i.castSucc).val - k₁, _⟩ = path₂.nodes i.castSucc
        -- Since (natAdd k₁ i.castSucc).val = k₁ + i.val, we have (k₁ + i.val) - k₁ = i.val
        congr 1
        ext
        simp only [Fin.natAdd]
        omega
      · -- Second node: (merge_to_cycle mp).nodes (natAdd k₁ i).succ = path₂.nodes i.succ
        unfold merge_to_cycle
        simp only [Fin.succ_natAdd]
        have h : ¬((Fin.natAdd k₁ i.succ).val < k₁) := by simp only [Fin.natAdd]; omega
        rw [dif_neg h]
        -- Need: path₂.nodes ⟨(natAdd k₁ i.succ).val - k₁, _⟩ = path₂.nodes i.succ
        -- Since (natAdd k₁ i.succ).val = k₁ + i.succ.val = k₁ + (i.val + 1)
        -- We have (k₁ + i.val + 1) - k₁ = i.val + 1 = i.succ.val
        congr
        · simp only [Fin.natAdd, Fin.succ]
          omega

  exact split_sum

/-! ## Part 3: Law of Averaging (Static Topology)

When two systems with a shared cycle are merged, the manifest holonomy
of the merged cycle equals the average of the two parent holonomies.

This proves conservation during static merging: (K₁ + K₂) → 2 × (K_avg).
-/

/-- Two configurations sharing the same cycle topology -/
structure SharedCycle (n k : ℕ) where
  /-- First configuration -/
  X₁ : ConfigSpace n
  /-- Second configuration -/
  X₂ : ConfigSpace n
  /-- Shared graph structure -/
  same_graph : X₁.graph = X₂.graph
  /-- The shared cycle in the first system -/
  cycle₁ : Cycle n X₁.graph k
  /-- The shared cycle in the second system (same nodes, transported adjacent proofs) -/
  cycle₂ : Cycle n X₂.graph k
  /-- Cycles have the same nodes -/
  same_nodes : cycle₁.nodes = cycle₂.nodes

/-- Merge two configurations by averaging their constraints -/
noncomputable def merge_configs {n k : ℕ} (sc : SharedCycle n k) : ConfigSpace n := {
  graph := sc.X₁.graph
  adj_decidable := sc.X₁.adj_decidable
  node_phases := fun i => (sc.X₁.node_phases i + sc.X₂.node_phases i) / 2
  constraints := fun i j h =>
    (sc.X₁.constraints i j h + sc.X₂.constraints i j (sc.same_graph ▸ h)) / 2
}

/-- **Law of Averaging**: K_merged = (K₁ + K₂)/2

This is the conservation law for static topology:
when two systems with a shared cycle merge, their frustrations average out,
conserving total holonomy as 2 × K_avg = K₁ + K₂.
-/
theorem law_of_averaging {n k : ℕ} (sc : SharedCycle n k) :
    cycle_holonomy (merge_configs sc) sc.cycle₁ =
      (cycle_holonomy sc.X₁ sc.cycle₁ +
       cycle_holonomy sc.X₂ sc.cycle₂) / 2 := by
  unfold cycle_holonomy

  -- First, establish what the merged constraints are
  have h_constraint_avg : ∀ (i : Fin k),
      (merge_configs sc).constraints
        (sc.cycle₁.nodes i.castSucc)
        (sc.cycle₁.nodes i.succ)
        (sc.cycle₁.adjacent i) =
      (sc.X₁.constraints
        (sc.cycle₁.nodes i.castSucc)
        (sc.cycle₁.nodes i.succ)
        (sc.cycle₁.adjacent i) +
       sc.X₂.constraints
        (sc.cycle₂.nodes i.castSucc)
        (sc.cycle₂.nodes i.succ)
        (sc.cycle₂.adjacent i)) / 2 := by
    intro i
    unfold merge_configs
    -- Use same_nodes to relate cycle₁ and cycle₂ nodes
    simp only [sc.same_nodes]
    -- Goal is closed by simp!

  -- Now prove the sum equality using the constraint averaging
  simp only [h_constraint_avg]
  -- Now LHS is: ∑ ((X₁.constraints ... + X₂.constraints ...) / 2)
  rw [← Finset.sum_div, Finset.sum_add_distrib]

/-! ## Part 4: Unified Conservation Law

Both laws are instances of a single conservation principle:
**Holonomy is neither created nor destroyed, only transformed.**

- In dynamic topology (emergence): latent → manifest via K_final = ∑ K_i
- In static topology (averaging): manifest ⊕ manifest → manifest via K_final = avg(K_i)
-/

/-- The unified conservation principle -/
theorem conservation_of_holonomy :
    (∀ n k₁ k₂ (X : ConfigSpace n) (mp : MergeablePaths n X.graph k₁ k₂),
      cycle_holonomy X (merge_to_cycle mp) =
        latent_holonomy X mp.path₁ + latent_holonomy X mp.path₂) ∧
    (∀ n k (sc : SharedCycle n k),
      cycle_holonomy (merge_configs sc) sc.cycle₁ =
        (cycle_holonomy sc.X₁ sc.cycle₁ +
         cycle_holonomy sc.X₂ sc.cycle₂) / 2) := by
  constructor
  · exact fun _ _ _ X mp => law_of_emergence X mp
  · exact fun _ _ sc => law_of_averaging sc

end ConservationOfHolonomy
