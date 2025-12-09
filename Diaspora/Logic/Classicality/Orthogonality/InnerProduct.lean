/-
General inner product formula for cycle forms.
-/
import Diaspora.Logic.Classicality.Orthogonality.Overlap

namespace Diaspora.Logic

open Diaspora.Core Diaspora.Hodge

variable {n : ℕ} [Fintype (Fin n)]

/-- Inner product of cycle forms = signedOverlap / (len₁ × len₂). -/
theorem cycle_inner_product_formula {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n) :
    inner_product_C1 (general_cycle_form c₁) (general_cycle_form c₂) =
    (c₁.signedOverlap c₂ : ℝ) / (c₁.len * c₂.len) := by
  have h_len₁_pos : (c₁.len : ℝ) > 0 := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₁.len_ge_3)
  have h_len₂_pos : (c₂.len : ℝ) > 0 := by
    simp only [GeneralCycle.len]; exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega) c₂.len_ge_3)
  have h_len₁_ne : (c₁.len : ℝ) ≠ 0 := ne_of_gt h_len₁_pos
  have h_len₂_ne : (c₂.len : ℝ) ≠ 0 := ne_of_gt h_len₂_pos
  have h_prod_ne : (c₁.len : ℝ) * c₂.len ≠ 0 := mul_ne_zero h_len₁_ne h_len₂_ne

  unfold inner_product_C1 GeneralCycle.signedOverlap

  have h_c1_fwd : ∀ k : Fin c₁.verts.length,
      (general_cycle_form c₁).val (c₁.vertex k.val) (c₁.nextVertex k.val) = 1 / c₁.len := by
    intro k
    unfold general_cycle_form
    have h_ex : ∃ k' : Fin c₁.verts.length, c₁.vertex k'.val = c₁.vertex k.val ∧
                c₁.nextVertex k'.val = c₁.nextVertex k.val := ⟨k, rfl, rfl⟩
    simp only [h_ex, ↓reduceIte]

  have h_c1_rev : ∀ k : Fin c₁.verts.length,
      (general_cycle_form c₁).val (c₁.nextVertex k.val) (c₁.vertex k.val) = -(1 / c₁.len) := by
    intro k
    have h := (general_cycle_form c₁).skew (c₁.vertex k.val) (c₁.nextVertex k.val)
    rw [h_c1_fwd] at h
    linarith

  have h_c1_zero : ∀ i j : Fin n,
      (¬∃ k : Fin c₁.verts.length, c₁.vertex k.val = i ∧ c₁.nextVertex k.val = j) →
      (¬∃ k : Fin c₁.verts.length, c₁.vertex k.val = j ∧ c₁.nextVertex k.val = i) →
      (general_cycle_form c₁).val i j = 0 := by
    intro i j h1 h2
    unfold general_cycle_form
    simp only [h1, h2, ↓reduceIte]

  have h_sum_eq : ∑ i : Fin n, ∑ j : Fin n, (general_cycle_form c₁).val i j *
      (general_cycle_form c₂).val i j =
      2 * (c₁.sameDirectionEdges c₂ : ℝ) / (c₁.len * c₂.len) -
      2 * (c₁.oppositeDirectionEdges c₂ : ℝ) / (c₁.len * c₂.len) := by
    -- Step 1: Terms where c₁ is zero contribute 0
    have h_zero_terms : ∀ i j : Fin n,
        (¬∃ k : Fin c₁.verts.length, c₁.vertex k.val = i ∧ c₁.nextVertex k.val = j) →
        (¬∃ k : Fin c₁.verts.length, c₁.vertex k.val = j ∧ c₁.nextVertex k.val = i) →
        (general_cycle_form c₁).val i j * (general_cycle_form c₂).val i j = 0 := by
      intro i j h1 h2
      rw [h_c1_zero i j h1 h2]
      ring

    -- Step 2: Compute γ₂ values on c₁ edges
    have h_c2_fwd : ∀ k : Fin c₂.verts.length,
        (general_cycle_form c₂).val (c₂.vertex k.val) (c₂.nextVertex k.val) = 1 / c₂.len := by
      intro k
      unfold general_cycle_form
      have h_ex : ∃ k' : Fin c₂.verts.length, c₂.vertex k'.val = c₂.vertex k.val ∧
                  c₂.nextVertex k'.val = c₂.nextVertex k.val := ⟨k, rfl, rfl⟩
      simp only [h_ex, ↓reduceIte]

    have h_c2_rev : ∀ k : Fin c₂.verts.length,
        (general_cycle_form c₂).val (c₂.nextVertex k.val) (c₂.vertex k.val) = -(1 / c₂.len) := by
      intro k
      have h := (general_cycle_form c₂).skew (c₂.vertex k.val) (c₂.nextVertex k.val)
      rw [h_c2_fwd] at h
      linarith

    -- Step 3: Sum over forward edges of c₁
    -- For each k, we get contribution from (v_k, v_{k+1}) and (v_{k+1}, v_k)
    -- Forward: (1/len₁) * γ₂(v_k, v_{k+1})
    -- Reverse: (-1/len₁) * γ₂(v_{k+1}, v_k) = (-1/len₁) * (-γ₂(v_k, v_{k+1})) = (1/len₁) * γ₂(v_k, v_{k+1})
    -- Total per edge: (2/len₁) * γ₂(v_k, v_{k+1})

    -- We use that the sum over all (i,j) equals sum over edges of c₁
    -- Each edge of c₁ appears twice: once as (v_k, v_{k+1}) and once as (v_{k+1}, v_k)

    -- Let's compute the sum over forward edges of c₁
    let fwd_contrib := ∑ k : Fin c₁.verts.length,
        (general_cycle_form c₁).val (c₁.vertex k.val) (c₁.nextVertex k.val) *
        (general_cycle_form c₂).val (c₁.vertex k.val) (c₁.nextVertex k.val)

    let rev_contrib := ∑ k : Fin c₁.verts.length,
        (general_cycle_form c₁).val (c₁.nextVertex k.val) (c₁.vertex k.val) *
        (general_cycle_form c₂).val (c₁.nextVertex k.val) (c₁.vertex k.val)

    -- Simplify forward contribution
    have h_fwd : fwd_contrib = ∑ k : Fin c₁.verts.length,
        (1 / c₁.len) * (general_cycle_form c₂).val (c₁.vertex k.val) (c₁.nextVertex k.val) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [h_c1_fwd k]

    -- Simplify reverse contribution using skew-symmetry
    have h_rev : rev_contrib = ∑ k : Fin c₁.verts.length,
        (1 / c₁.len) * (general_cycle_form c₂).val (c₁.vertex k.val) (c₁.nextVertex k.val) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [h_c1_rev k]
      have h_skew := (general_cycle_form c₂).skew (c₁.vertex k.val) (c₁.nextVertex k.val)
      rw [h_skew]
      ring

    -- The sum over all pairs decomposes into these two contributions
    -- (because other pairs have c₁ = 0)

    -- Now compute ∑_k γ₂(v_k, v_{k+1}) in terms of S⁺ and S⁻
    let γ₂_on_c1 := ∑ k : Fin c₁.verts.length,
        (general_cycle_form c₂).val (c₁.vertex k.val) (c₁.nextVertex k.val)

    -- γ₂(v_k, v_{k+1}) = 1/len₂ if same direction, -1/len₂ if opposite, 0 otherwise
    have h_γ₂_decomp : γ₂_on_c1 = (c₁.sameDirectionEdges c₂ : ℝ) / c₂.len -
                                   (c₁.oppositeDirectionEdges c₂ : ℝ) / c₂.len := by
      -- For each k in c₁, γ₂(edge k) is either:
      --   +1/len₂ if same-direction match exists
      --   -1/len₂ if opposite-direction match exists
      --   0 otherwise

      -- Uniqueness: use the helper lemmas
      have h_unique_same : ∀ k₁ : Fin c₁.verts.length,
          ∀ k₂ k₂' : Fin c₂.verts.length,
          (c₁.vertex k₁.val = c₂.vertex k₂.val ∧ c₁.nextVertex k₁.val = c₂.nextVertex k₂.val) →
          (c₁.vertex k₁.val = c₂.vertex k₂'.val ∧ c₁.nextVertex k₁.val = c₂.nextVertex k₂'.val) →
          k₂ = k₂' := fun k₁ k₂ k₂' => unique_same_direction_match c₁ c₂ k₁ k₂ k₂'

      have h_unique_opp : ∀ k₁ : Fin c₁.verts.length,
          ∀ k₂ k₂' : Fin c₂.verts.length,
          (c₁.vertex k₁.val = c₂.nextVertex k₂.val ∧ c₁.nextVertex k₁.val = c₂.vertex k₂.val) →
          (c₁.vertex k₁.val = c₂.nextVertex k₂'.val ∧ c₁.nextVertex k₁.val = c₂.vertex k₂'.val) →
          k₂ = k₂' := fun k₁ k₂ k₂' => unique_opposite_direction_match c₁ c₂ k₁ k₂ k₂'

      -- The γ₂ value at each edge of c₁
      have h_γ₂_val : ∀ k : Fin c₁.verts.length,
          (general_cycle_form c₂).val (c₁.vertex k.val) (c₁.nextVertex k.val) =
          if ∃ k₂ : Fin c₂.verts.length, c₁.vertex k.val = c₂.vertex k₂.val ∧
                                          c₁.nextVertex k.val = c₂.nextVertex k₂.val
          then (1 : ℝ) / c₂.len
          else if ∃ k₂ : Fin c₂.verts.length, c₁.vertex k.val = c₂.nextVertex k₂.val ∧
                                               c₁.nextVertex k.val = c₂.vertex k₂.val
          then -(1 : ℝ) / c₂.len
          else 0 := by
        intro k
        -- The conditions in general_cycle_form are swapped versions of ours
        have h_eq_fwd : (∃ k₂ : Fin c₂.verts.length, c₂.vertex k₂.val = c₁.vertex k.val ∧
                         c₂.nextVertex k₂.val = c₁.nextVertex k.val) ↔
                        (∃ k₂ : Fin c₂.verts.length, c₁.vertex k.val = c₂.vertex k₂.val ∧
                         c₁.nextVertex k.val = c₂.nextVertex k₂.val) := by
          constructor <;> (intro ⟨k₂, h1, h2⟩; exact ⟨k₂, h1.symm, h2.symm⟩)
        have h_eq_rev : (∃ k₂ : Fin c₂.verts.length, c₂.vertex k₂.val = c₁.nextVertex k.val ∧
                         c₂.nextVertex k₂.val = c₁.vertex k.val) ↔
                        (∃ k₂ : Fin c₂.verts.length, c₁.vertex k.val = c₂.nextVertex k₂.val ∧
                         c₁.nextVertex k.val = c₂.vertex k₂.val) := by
          constructor <;> (intro ⟨k₂, h1, h2⟩; exact ⟨k₂, h2.symm, h1.symm⟩)
        unfold general_cycle_form
        simp only [h_eq_fwd, h_eq_rev]
        -- The remaining difference is -(1/x) vs -1/x
        split_ifs <;> ring

      -- Rewrite the sum using this classification
      have h_sum_split : γ₂_on_c1 = ∑ k : Fin c₁.verts.length,
          (if ∃ k₂ : Fin c₂.verts.length, c₁.vertex k.val = c₂.vertex k₂.val ∧
                                          c₁.nextVertex k.val = c₂.nextVertex k₂.val
           then (1 : ℝ) / c₂.len
           else if ∃ k₂ : Fin c₂.verts.length, c₁.vertex k.val = c₂.nextVertex k₂.val ∧
                                                c₁.nextVertex k.val = c₂.vertex k₂.val
           then -(1 : ℝ) / c₂.len
           else 0) := by
        unfold γ₂_on_c1
        apply Finset.sum_congr rfl
        intro k _
        exact h_γ₂_val k

      -- Count same-direction k's
      let same_set := Finset.univ.filter (fun k : Fin c₁.verts.length =>
        ∃ k₂ : Fin c₂.verts.length, c₁.vertex k.val = c₂.vertex k₂.val ∧
                                     c₁.nextVertex k.val = c₂.nextVertex k₂.val)

      let opp_set := Finset.univ.filter (fun k : Fin c₁.verts.length =>
        (¬∃ k₂ : Fin c₂.verts.length, c₁.vertex k.val = c₂.vertex k₂.val ∧
                                       c₁.nextVertex k.val = c₂.nextVertex k₂.val) ∧
        ∃ k₂ : Fin c₂.verts.length, c₁.vertex k.val = c₂.nextVertex k₂.val ∧
                                     c₁.nextVertex k.val = c₂.vertex k₂.val)

      -- The sum splits into contributions from same_set and opp_set
      have h_sum_parts : γ₂_on_c1 = same_set.card * ((1 : ℝ) / c₂.len) +
                                    opp_set.card * (-(1 : ℝ) / c₂.len) := by
        rw [h_sum_split]
        -- Each term is either 1/len, -1/len, or 0 based on membership
        have h_term : ∀ k : Fin c₁.verts.length,
            (if ∃ k₂ : Fin c₂.verts.length, c₁.vertex k.val = c₂.vertex k₂.val ∧
                                            c₁.nextVertex k.val = c₂.nextVertex k₂.val
             then (1 : ℝ) / c₂.len
             else if ∃ k₂ : Fin c₂.verts.length, c₁.vertex k.val = c₂.nextVertex k₂.val ∧
                                                  c₁.nextVertex k.val = c₂.vertex k₂.val
             then -(1 : ℝ) / c₂.len
             else 0) =
            (if k ∈ same_set then (1 : ℝ) / c₂.len else 0) +
            (if k ∈ opp_set then -(1 : ℝ) / c₂.len else 0) := by
          intro k
          -- Unfold the let definitions for same_set and opp_set
          show _ = (if k ∈ Finset.univ.filter (fun k => ∃ k₂ : Fin c₂.verts.length,
                        c₁.vertex k.val = c₂.vertex k₂.val ∧
                        c₁.nextVertex k.val = c₂.nextVertex k₂.val) then _ else _) +
                   (if k ∈ Finset.univ.filter (fun k =>
                        (¬∃ k₂ : Fin c₂.verts.length, c₁.vertex k.val = c₂.vertex k₂.val ∧
                         c₁.nextVertex k.val = c₂.nextVertex k₂.val) ∧
                        ∃ k₂ : Fin c₂.verts.length, c₁.vertex k.val = c₂.nextVertex k₂.val ∧
                         c₁.nextVertex k.val = c₂.vertex k₂.val) then _ else _)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hP : ∃ k₂ : Fin c₂.verts.length, c₁.vertex k.val = c₂.vertex k₂.val ∧
                        c₁.nextVertex k.val = c₂.nextVertex k₂.val
          · simp only [if_pos hP, if_neg (fun h : (¬_) ∧ _ => h.1 hP), add_zero]
          · by_cases hQ : ∃ k₂ : Fin c₂.verts.length, c₁.vertex k.val = c₂.nextVertex k₂.val ∧
                          c₁.nextVertex k.val = c₂.vertex k₂.val
            · have h_opp_mem : (¬∃ k₂ : Fin c₂.verts.length, c₁.vertex k.val = c₂.vertex k₂.val ∧
                                c₁.nextVertex k.val = c₂.nextVertex k₂.val) ∧
                              ∃ k₂ : Fin c₂.verts.length, c₁.vertex k.val = c₂.nextVertex k₂.val ∧
                                c₁.nextVertex k.val = c₂.vertex k₂.val := ⟨hP, hQ⟩
              simp only [if_neg hP, if_pos hQ, if_pos h_opp_mem, zero_add]
            · simp only [if_neg hP, if_neg hQ, if_neg (fun h : (¬_) ∧ _ => hQ h.2), add_zero]
        rw [Finset.sum_congr rfl (fun k _ => h_term k)]
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_mem, Finset.univ_inter]
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]

      -- Bijection: same_set.card = sameDirectionEdges
      have h_same_card : same_set.card = c₁.sameDirectionEdges c₂ := by
        unfold GeneralCycle.sameDirectionEdges
        -- For k₁ ∈ same_set, extract the witness k₂ and map to (k₁, k₂)
        apply Finset.card_bij (fun k₁ hk₁ => (k₁, Classical.choose (Finset.mem_filter.mp hk₁).2))
        · -- Membership: (k₁, chosen_k₂) ∈ sameDirectionEdges
          intro k₁ hk₁
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact Classical.choose_spec (Finset.mem_filter.mp hk₁).2
        · -- Injectivity: first component determines k₁
          intro k₁ _ k₁' _ h_eq
          simp only [Prod.mk.injEq] at h_eq
          exact h_eq.1
        · -- Surjectivity: every (k₁, k₂) comes from some k₁ ∈ same_set
          intro ⟨k₁, k₂⟩ hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          refine ⟨k₁, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨k₂, hp⟩
          · simp only [Prod.mk.injEq, true_and]
            -- The chosen k₂' equals k₂ by uniqueness
            have h_exists : ∃ k₂' : Fin c₂.verts.length, c₁.vertex k₁.val = c₂.vertex k₂'.val ∧
                                    c₁.nextVertex k₁.val = c₂.nextVertex k₂'.val := ⟨k₂, hp⟩
            have h_spec := Classical.choose_spec h_exists
            exact h_unique_same k₁ (Classical.choose h_exists) k₂ h_spec hp

      -- Bijection: opp_set.card = oppositeDirectionEdges
      have h_opp_card : opp_set.card = c₁.oppositeDirectionEdges c₂ := by
        unfold GeneralCycle.oppositeDirectionEdges
        -- For k₁ ∈ opp_set, extract the opposite-direction witness k₂
        apply Finset.card_bij (fun k₁ hk₁ => (k₁, Classical.choose (Finset.mem_filter.mp hk₁).2.2))
        · -- Membership: (k₁, chosen_k₂) ∈ oppositeDirectionEdges
          intro k₁ hk₁
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact Classical.choose_spec (Finset.mem_filter.mp hk₁).2.2
        · -- Injectivity: first component determines k₁
          intro k₁ _ k₁' _ h_eq
          simp only [Prod.mk.injEq] at h_eq
          exact h_eq.1
        · -- Surjectivity: every (k₁, k₂) comes from some k₁ ∈ opp_set
          intro ⟨k₁, k₂⟩ hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          refine ⟨k₁, ?_, ?_⟩
          · -- Show k₁ ∈ opp_set (need to prove ¬same ∧ ∃opposite)
            -- opp_set is a let-binding, so unfold it with show
            show k₁ ∈ Finset.univ.filter (fun k =>
              (¬∃ k₂ : Fin c₂.verts.length, c₁.vertex k.val = c₂.vertex k₂.val ∧
                                            c₁.nextVertex k.val = c₂.nextVertex k₂.val) ∧
              ∃ k₂ : Fin c₂.verts.length, c₁.vertex k.val = c₂.nextVertex k₂.val ∧
                                          c₁.nextVertex k.val = c₂.vertex k₂.val)
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨?_, k₂, hp⟩
            -- k₁ is not in same-direction set (would contradict nodup)
            intro h_same
            obtain ⟨k₂' : Fin c₂.verts.length, h_same'⟩ := h_same
            -- edge(c₁,k₁) = edge(c₂,k₂') same direction AND edge(c₂,k₂) opposite direction
            -- hp: c₁.vertex k₁ = c₂.nextVertex k₂, c₁.nextVertex k₁ = c₂.vertex k₂
            -- h_same': c₁.vertex k₁ = c₂.vertex k₂', c₁.nextVertex k₁ = c₂.nextVertex k₂'
            -- So: c₂.vertex k₂' = c₂.nextVertex k₂ and c₂.nextVertex k₂' = c₂.vertex k₂
            have h_eq1 : c₂.vertex k₂'.val = c₂.nextVertex k₂.val := by
              calc c₂.vertex k₂'.val = c₁.vertex k₁.val := h_same'.1.symm
                _ = c₂.nextVertex k₂.val := hp.1
            have h_eq2 : c₂.nextVertex k₂'.val = c₂.vertex k₂.val := by
              calc c₂.nextVertex k₂'.val = c₁.nextVertex k₁.val := h_same'.2.symm
                _ = c₂.vertex k₂.val := hp.2
            -- This means k₂' = k₂+1 (mod len) and k₂ = k₂'+1 (mod len), so len ≤ 2, contradiction
            have h_nodup := c₂.nodup
            unfold GeneralCycle.nextVertex GeneralCycle.vertex at h_eq1 h_eq2
            have h_idx1 := h_nodup.get_inj_iff.mp h_eq1
            have h_idx2 := h_nodup.get_inj_iff.mp h_eq2
            simp only [Fin.ext_iff] at h_idx1 h_idx2
            have h_len := c₂.len_ge_3
            have h_k2'_mod : k₂'.val = (k₂.val + 1) % c₂.verts.length := by
              rw [Nat.mod_eq_of_lt k₂'.isLt] at h_idx1; exact h_idx1
            have h_k2_mod : k₂.val = (k₂'.val + 1) % c₂.verts.length := by
              rw [Nat.mod_eq_of_lt k₂.isLt] at h_idx2; exact h_idx2.symm
            have h_cycle : (k₂.val + 2) % c₂.verts.length = k₂.val := by
              have h1_mod : 1 % c₂.verts.length = 1 := Nat.mod_eq_of_lt (by omega)
              calc (k₂.val + 2) % c₂.verts.length
                  = ((k₂.val + 1) + 1) % c₂.verts.length := by ring_nf
                _ = ((k₂.val + 1) % c₂.verts.length + 1) % c₂.verts.length := by
                    rw [Nat.add_mod (k₂.val + 1) 1, h1_mod]
                _ = (k₂'.val + 1) % c₂.verts.length := by rw [← h_k2'_mod]
                _ = k₂.val := h_k2_mod.symm
            cases Nat.lt_or_ge (k₂.val + 2) c₂.verts.length with
            | inl h_small => rw [Nat.mod_eq_of_lt h_small] at h_cycle; omega
            | inr h_big =>
              have h_sub_lt : k₂.val + 2 - c₂.verts.length < c₂.verts.length := by
                have : k₂.val < c₂.verts.length := k₂.isLt; omega
              rw [Nat.mod_eq_sub_mod h_big, Nat.mod_eq_of_lt h_sub_lt] at h_cycle; omega
          · simp only [Prod.mk.injEq, true_and]
            -- The chosen k₂' equals k₂ by uniqueness
            have h_not_same : ¬∃ k₂' : Fin c₂.verts.length, c₁.vertex k₁.val = c₂.vertex k₂'.val ∧
                                       c₁.nextVertex k₁.val = c₂.nextVertex k₂'.val := by
              intro h_same
              obtain ⟨k₂' : Fin c₂.verts.length, h_same'⟩ := h_same
              have h_eq1 : c₂.vertex k₂'.val = c₂.nextVertex k₂.val := by
                calc c₂.vertex k₂'.val = c₁.vertex k₁.val := h_same'.1.symm
                  _ = c₂.nextVertex k₂.val := hp.1
              have h_eq2 : c₂.nextVertex k₂'.val = c₂.vertex k₂.val := by
                calc c₂.nextVertex k₂'.val = c₁.nextVertex k₁.val := h_same'.2.symm
                  _ = c₂.vertex k₂.val := hp.2
              have h_nodup := c₂.nodup
              unfold GeneralCycle.nextVertex GeneralCycle.vertex at h_eq1 h_eq2
              have h_idx1 := h_nodup.get_inj_iff.mp h_eq1
              have h_idx2 := h_nodup.get_inj_iff.mp h_eq2
              simp only [Fin.ext_iff] at h_idx1 h_idx2
              have h_len := c₂.len_ge_3
              have h_k2'_mod : k₂'.val = (k₂.val + 1) % c₂.verts.length := by
                rw [Nat.mod_eq_of_lt k₂'.isLt] at h_idx1; exact h_idx1
              have h_k2_mod : k₂.val = (k₂'.val + 1) % c₂.verts.length := by
                rw [Nat.mod_eq_of_lt k₂.isLt] at h_idx2; exact h_idx2.symm
              have h_cycle : (k₂.val + 2) % c₂.verts.length = k₂.val := by
                have h1_mod : 1 % c₂.verts.length = 1 := Nat.mod_eq_of_lt (by omega)
                calc (k₂.val + 2) % c₂.verts.length
                    = ((k₂.val + 1) + 1) % c₂.verts.length := by ring_nf
                  _ = ((k₂.val + 1) % c₂.verts.length + 1) % c₂.verts.length := by
                      rw [Nat.add_mod (k₂.val + 1) 1, h1_mod]
                  _ = (k₂'.val + 1) % c₂.verts.length := by rw [← h_k2'_mod]
                  _ = k₂.val := h_k2_mod.symm
              cases Nat.lt_or_ge (k₂.val + 2) c₂.verts.length with
              | inl h_small => rw [Nat.mod_eq_of_lt h_small] at h_cycle; omega
              | inr h_big =>
                have h_sub_lt : k₂.val + 2 - c₂.verts.length < c₂.verts.length := by
                  have : k₂.val < c₂.verts.length := k₂.isLt; omega
                rw [Nat.mod_eq_sub_mod h_big, Nat.mod_eq_of_lt h_sub_lt] at h_cycle; omega
            have h_exists : (¬∃ k₂' : Fin c₂.verts.length, c₁.vertex k₁.val = c₂.vertex k₂'.val ∧
                                      c₁.nextVertex k₁.val = c₂.nextVertex k₂'.val) ∧
                            ∃ k₂' : Fin c₂.verts.length, c₁.vertex k₁.val = c₂.nextVertex k₂'.val ∧
                                   c₁.nextVertex k₁.val = c₂.vertex k₂'.val := ⟨h_not_same, k₂, hp⟩
            have h_spec := Classical.choose_spec h_exists.2
            exact h_unique_opp k₁ (Classical.choose h_exists.2) k₂ h_spec hp

      -- Final computation
      rw [h_sum_parts, h_same_card, h_opp_card]
      ring

    -- Now relate back to the double sum
    -- The double sum equals 2 * (1/len₁) * γ₂_on_c1 = (2/len₁) * γ₂_on_c1
    -- Which equals 2*S⁺/(len₁*len₂) - 2*S⁻/(len₁*len₂)

    have h_total : fwd_contrib + rev_contrib = 2 * (1 / c₁.len) * γ₂_on_c1 := by
      rw [h_fwd, h_rev]
      -- Both sums are identical, so we need to show 2 * (∑_k (1/len) * f(k)) = 2 * (1/len) * ∑_k f(k)
      have h_factor : ∀ s : Finset (Fin c₁.verts.length),
          ∑ k ∈ s, (1 / (c₁.len : ℝ)) * (general_cycle_form c₂).val (c₁.vertex k.val) (c₁.nextVertex k.val) =
          (1 / c₁.len) * ∑ k ∈ s, (general_cycle_form c₂).val (c₁.vertex k.val) (c₁.nextVertex k.val) := by
        intro s
        rw [Finset.mul_sum]
      simp only [h_factor Finset.univ]
      ring

    -- The double sum equals fwd_contrib + rev_contrib (other terms are 0)
    have h_sum_decomp : ∑ i : Fin n, ∑ j : Fin n,
        (general_cycle_form c₁).val i j * (general_cycle_form c₂).val i j =
        fwd_contrib + rev_contrib := by
      -- Pairs where c₁ is 0 contribute 0 to the sum.
      -- The only nonzero pairs are:
      --   Forward edges: (vertex k, nextVertex k) for k in Fin c₁.len
      --   Reverse edges: (nextVertex k, vertex k) for k in Fin c₁.len
      -- We decompose the double sum by showing most terms are 0.

      -- The sum restricted to zero terms of c₁
      have h_most_zero : ∀ i j : Fin n,
          (general_cycle_form c₁).val i j = 0 →
          (general_cycle_form c₁).val i j * (general_cycle_form c₂).val i j = 0 := by
        intro i j h; rw [h]; ring

      -- We need to show the double sum equals the sum over edges
      -- This is a counting/reindexing argument

      -- The set of forward edges is exactly {(vertex k, nextVertex k) | k ∈ Fin c₁.len}
      -- The set of reverse edges is exactly {(nextVertex k, vertex k) | k ∈ Fin c₁.len}

      -- Use Finset.sum_eq_sum_filter to isolate nonzero terms
      have h_filter_equiv : ∑ i : Fin n, ∑ j : Fin n,
          (general_cycle_form c₁).val i j * (general_cycle_form c₂).val i j =
          ∑ i : Fin n, ∑ j : Fin n,
            if (∃ k : Fin c₁.verts.length, c₁.vertex k.val = i ∧ c₁.nextVertex k.val = j) ∨
               (∃ k : Fin c₁.verts.length, c₁.vertex k.val = j ∧ c₁.nextVertex k.val = i)
            then (general_cycle_form c₁).val i j * (general_cycle_form c₂).val i j
            else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        split_ifs with h
        · rfl
        · -- When neither condition holds, c₁ is 0
          -- h : ¬((∃ k, fwd) ∨ (∃ k, rev)) = (¬∃ k, fwd) ∧ (¬∃ k, rev)
          have h_not_fwd : ¬∃ k : Fin c₁.verts.length, c₁.vertex k.val = i ∧ c₁.nextVertex k.val = j := by
            intro hfwd; exact h (Or.inl hfwd)
          have h_not_rev : ¬∃ k : Fin c₁.verts.length, c₁.vertex k.val = j ∧ c₁.nextVertex k.val = i := by
            intro hrev; exact h (Or.inr hrev)
          have h0 := h_c1_zero i j h_not_fwd h_not_rev
          rw [h0]; ring

      rw [h_filter_equiv]

      -- For simple cycles, each edge (i,j) is EITHER forward OR reverse, not both.
      -- This is because if (i,j) is forward with index k, then j = nextVertex k,
      -- and for it to also be reverse we'd need vertex (k+2) = vertex k, contradiction for len ≥ 3.

      -- First, show forward and reverse edges are disjoint
      have h_disjoint : ∀ i j : Fin n,
          (∃ k : Fin c₁.verts.length, c₁.vertex k.val = i ∧ c₁.nextVertex k.val = j) →
          (∃ k : Fin c₁.verts.length, c₁.vertex k.val = j ∧ c₁.nextVertex k.val = i) → False := by
        intro i j ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩
        -- k₁: (i,j) = (vertex k₁, nextVertex k₁)
        -- k₂: (j,i) = (vertex k₂, nextVertex k₂)
        -- So vertex k₂ = nextVertex k₁, meaning k₂ = (k₁+1) % len
        -- And nextVertex k₂ = vertex k₁
        have h1 : c₁.vertex k₂.val = c₁.nextVertex k₁.val := by rw [hk₂.1, hk₁.2]
        have h2 : c₁.nextVertex k₂.val = c₁.vertex k₁.val := by rw [hk₂.2, hk₁.1]
        have h_nodup := c₁.nodup
        unfold GeneralCycle.nextVertex GeneralCycle.vertex at h1 h2
        have h_idx1 := h_nodup.get_inj_iff.mp h1
        have h_idx2 := h_nodup.get_inj_iff.mp h2
        simp only [Fin.ext_iff] at h_idx1 h_idx2
        have h_len := c₁.len_ge_3
        have h_k2_mod : k₂.val = (k₁.val + 1) % c₁.verts.length := by
          rw [Nat.mod_eq_of_lt k₂.isLt] at h_idx1; exact h_idx1
        have h_k1_mod : k₁.val = (k₂.val + 1) % c₁.verts.length := by
          rw [Nat.mod_eq_of_lt k₁.isLt] at h_idx2; exact h_idx2.symm
        have h_cycle : (k₁.val + 2) % c₁.verts.length = k₁.val := by
          have h1_mod : 1 % c₁.verts.length = 1 := Nat.mod_eq_of_lt (by omega)
          calc (k₁.val + 2) % c₁.verts.length
              = ((k₁.val + 1) + 1) % c₁.verts.length := by ring_nf
            _ = ((k₁.val + 1) % c₁.verts.length + 1) % c₁.verts.length := by
                rw [Nat.add_mod (k₁.val + 1) 1, h1_mod]
            _ = (k₂.val + 1) % c₁.verts.length := by rw [← h_k2_mod]
            _ = k₁.val := h_k1_mod.symm
        cases Nat.lt_or_ge (k₁.val + 2) c₁.verts.length with
        | inl h_small => rw [Nat.mod_eq_of_lt h_small] at h_cycle; omega
        | inr h_big =>
          have h_sub_lt : k₁.val + 2 - c₁.verts.length < c₁.verts.length := by
            have : k₁.val < c₁.verts.length := k₁.isLt; omega
          rw [Nat.mod_eq_sub_mod h_big, Nat.mod_eq_of_lt h_sub_lt] at h_cycle; omega

      -- Now we split the sum based on whether it's forward or reverse
      -- The key is that the condition splits into exactly two disjoint cases
      have h_split_sum : ∑ i : Fin n, ∑ j : Fin n,
          (if (∃ k : Fin c₁.verts.length, c₁.vertex k.val = i ∧ c₁.nextVertex k.val = j) ∨
              (∃ k : Fin c₁.verts.length, c₁.vertex k.val = j ∧ c₁.nextVertex k.val = i)
           then (general_cycle_form c₁).val i j * (general_cycle_form c₂).val i j
           else 0) =
          ∑ i : Fin n, ∑ j : Fin n,
            (if ∃ k : Fin c₁.verts.length, c₁.vertex k.val = i ∧ c₁.nextVertex k.val = j
             then (general_cycle_form c₁).val i j * (general_cycle_form c₂).val i j
             else 0) +
          ∑ i : Fin n, ∑ j : Fin n,
            (if ∃ k : Fin c₁.verts.length, c₁.vertex k.val = j ∧ c₁.nextVertex k.val = i
             then (general_cycle_form c₁).val i j * (general_cycle_form c₂).val i j
             else 0) := by
        -- Split ∑∑(if A∨B then x else 0) = ∑∑(if A then x else 0) + ∑∑(if B then x else 0)
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hfwd : ∃ k : Fin c₁.verts.length, c₁.vertex k.val = i ∧ c₁.nextVertex k.val = j
        · -- Forward case
          simp only [hfwd, true_or, ↓reduceIte]
          by_cases hrev : ∃ k : Fin c₁.verts.length, c₁.vertex k.val = j ∧ c₁.nextVertex k.val = i
          · exfalso; exact h_disjoint i j hfwd hrev
          · simp only [hrev, ↓reduceIte, add_zero]
        · -- Not forward
          simp only [hfwd, false_or, ↓reduceIte]
          by_cases hrev : ∃ k : Fin c₁.verts.length, c₁.vertex k.val = j ∧ c₁.nextVertex k.val = i
          · simp only [hrev, ↓reduceIte, zero_add]
          · simp only [hrev, ↓reduceIte, add_zero]

      rw [h_split_sum]

      -- Now we need to show each sum equals fwd_contrib and rev_contrib respectively
      -- Forward sum: reindex by k
      have h_fwd_sum : ∑ i : Fin n, ∑ j : Fin n,
          (if ∃ k : Fin c₁.verts.length, c₁.vertex k.val = i ∧ c₁.nextVertex k.val = j
           then (general_cycle_form c₁).val i j * (general_cycle_form c₂).val i j
           else 0) = fwd_contrib := by
        -- Reindex: the sum over (i,j) pairs where (i,j) is a forward edge
        -- equals the sum over k of the value at edge k
        symm
        unfold fwd_contrib
        -- Use sum_bij: k ↦ (vertex k, nextVertex k)
        rw [show ∑ k : Fin c₁.verts.length, _ = ∑ k ∈ Finset.univ, _ from rfl]
        rw [show (∑ i : Fin n, ∑ j : Fin n, _) =
            ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n =>
              ∃ k : Fin c₁.verts.length, c₁.vertex k.val = p.1 ∧ c₁.nextVertex k.val = p.2),
            (general_cycle_form c₁).val p.1 p.2 * (general_cycle_form c₂).val p.1 p.2 by
          rw [← Finset.sum_product']
          -- Convert: ∑ x, (if p x then f x else 0) = ∑ x in filter p, f x
          rw [← Finset.sum_filter]
          congr 1]
        apply Finset.sum_bij (fun k _ => (c₁.vertex k.val, c₁.nextVertex k.val))
        · -- hi: image is in target set
          intro k _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨k, rfl, rfl⟩
        · -- i_inj: injectivity
          intro k₁ _ k₂ _ h_eq
          simp only [Prod.mk.injEq] at h_eq
          have h_nodup := c₁.nodup
          unfold GeneralCycle.vertex at h_eq
          have h_inj := h_nodup.get_inj_iff.mp h_eq.1
          simp only [Fin.ext_iff, Nat.mod_eq_of_lt k₁.isLt, Nat.mod_eq_of_lt k₂.isLt] at h_inj
          exact Fin.ext h_inj
        · -- i_surj: surjectivity
          intro ⟨i, j⟩ hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          obtain ⟨k, hk⟩ := hp
          use k
          simp only [Finset.mem_univ, Prod.mk.injEq]
          exact ⟨trivial, hk⟩
        · -- h: function preserves value
          intro k _; rfl

      have h_rev_sum : ∑ i : Fin n, ∑ j : Fin n,
          (if ∃ k : Fin c₁.verts.length, c₁.vertex k.val = j ∧ c₁.nextVertex k.val = i
           then (general_cycle_form c₁).val i j * (general_cycle_form c₂).val i j
           else 0) = rev_contrib := by
        symm
        unfold rev_contrib
        rw [show ∑ k : Fin c₁.verts.length, _ = ∑ k ∈ Finset.univ, _ from rfl]
        rw [show (∑ i : Fin n, ∑ j : Fin n, _) =
            ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n =>
              ∃ k : Fin c₁.verts.length, c₁.vertex k.val = p.2 ∧ c₁.nextVertex k.val = p.1),
            (general_cycle_form c₁).val p.1 p.2 * (general_cycle_form c₂).val p.1 p.2 by
          rw [← Finset.sum_product']
          rw [← Finset.sum_filter]
          congr 1]
        apply Finset.sum_bij (fun k _ => (c₁.nextVertex k.val, c₁.vertex k.val))
        · -- hi: image is in target set
          intro k _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨k, rfl, rfl⟩
        · -- i_inj: injectivity
          intro k₁ _ k₂ _ h_eq
          simp only [Prod.mk.injEq] at h_eq
          have h_nodup := c₁.nodup
          unfold GeneralCycle.vertex at h_eq
          have h_inj := h_nodup.get_inj_iff.mp h_eq.2
          simp only [Fin.ext_iff, Nat.mod_eq_of_lt k₁.isLt, Nat.mod_eq_of_lt k₂.isLt] at h_inj
          exact Fin.ext h_inj
        · -- i_surj: surjectivity
          intro ⟨i, j⟩ hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          obtain ⟨k, hk⟩ := hp
          use k
          simp only [Finset.mem_univ, Prod.mk.injEq]
          exact ⟨trivial, hk.2, hk.1⟩
        · -- h: function preserves value
          intro k _; rfl

      rw [h_fwd_sum, h_rev_sum]

    rw [h_sum_decomp, h_total, h_γ₂_decomp]
    field_simp

  rw [h_sum_eq]
  have h_final : (1 / 2 : ℝ) * (2 * ↑(c₁.sameDirectionEdges c₂) / (↑c₁.len * ↑c₂.len) -
      2 * ↑(c₁.oppositeDirectionEdges c₂) / (↑c₁.len * ↑c₂.len)) =
      (↑(c₁.sameDirectionEdges c₂) - ↑(c₁.oppositeDirectionEdges c₂)) / (↑c₁.len * ↑c₂.len) := by
    field_simp
  rw [h_final]
  congr 1
  -- Need to show ℤ cast equals ℕ subtraction casts
  simp only [Int.cast_sub, Int.cast_natCast]

/-- Corollary: edge_disjoint_cycles_orthogonal follows from the inner product formula. -/
theorem edge_disjoint_cycles_orthogonal' {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)] [NeZero n]
    (c₁ c₂ : GeneralCycle n)
    (h_disjoint : GeneralCycle.EdgeDisjoint c₁ c₂) :
    inner_product_C1 (general_cycle_form c₁) (general_cycle_form c₂) = 0 := by
  rw [cycle_inner_product_formula]
  rw [edge_disjoint_signedOverlap_zero c₁ c₂ h_disjoint]
  simp

end Diaspora.Logic
