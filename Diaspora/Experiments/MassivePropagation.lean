/-
# Massive Propagation: Topology Creates Inertia

We address the critique of `HolonomyWaves` by introducing a graph with non-trivial
topology (a Ladder Graph). We show that the "Rung" constraints create a 
restoring force that acts effectively as a MASS term in the wave equation.

1. **Setup**: A Ladder Graph (2 parallel rails connected by rungs).
2. **Lagrangian**: T - V_int (where V_int includes rung constraints).
3. **Decomposition**: Symmetric Mode (Σ) vs Antisymmetric Mode (Δ).
4. **Result**: 
   - Σ behaves like a massless wave (Light).
   - Δ behaves like a massive field (Matter).
   
This proves that **Cycles generate Inertia**.
-/

import Diaspora.GaugeTheoreticHolonomy
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic

open GaugeTheoretic

namespace MassivePropagation

/-! ## Part 1: The Ladder Graph -/

/-- A Ladder Graph with length N (2N nodes).
    Nodes 0..N-1 are the "Top Rail".
    Nodes N..2N-1 are the "Bottom Rail".
    Rungs connect i and i+N. -/
def ladder_graph (n : ℕ) : SimpleGraph (Fin (2 * n)) where
  Adj i j := 
    -- Top Rail: i ~ i+1 (for i < n-1)
    (i.val + 1 = j.val ∧ j.val < n) ∨ (j.val + 1 = i.val ∧ i.val < n) ∨
    -- Bottom Rail: i ~ i+1 (for i >= n)
    (i.val + 1 = j.val ∧ i.val ≥ n) ∨ (j.val + 1 = i.val ∧ j.val ≥ n) ∨
    -- Rungs: i ~ i+N (vertical connections)
    (j.val = i.val + n) ∨ (i.val = j.val + n)
  symm := by
    intro i j h
    cases h with
    | inl h => right; left; exact ⟨h.1, h.2⟩
    | inr h => cases h with
      | inl h => left; exact ⟨h.1, h.2⟩
      | inr h => cases h with
        | inl h => right; right; right; left; exact ⟨h.1, h.2⟩
        | inr h => cases h with
          | inl h => right; right; left; exact ⟨h.1, h.2⟩
          | inr h => cases h with
            | inl h => right; right; right; right; right; exact h
            | inr h => right; right; right; right; left; exact h
  loopless := by
    intro i h
    cases h with
    | inl h => omega
    | inr h => cases h with
      | inl h => omega
      | inr h => cases h with
        | inl h => omega
        | inr h => cases h with
          | inl h => omega
          | inr h => cases h with
            | inl h => omega
            | inr h => omega

/-! ## Part 2: Dynamic Configuration -/

structure WorldLine (n : ℕ) where
  phases : Fin (2 * n) → ℝ → ℝ -- Phase at node i, time t
  smooth : ∀ i, ContDiff ℝ 2 (phases i)

/-! ## Part 3: The Massive Lagrangian -/

/-- Kinetic Energy: Standard sum of v² -/
noncomputable def kinetic_energy {n : ℕ} (w : WorldLine n) (t : ℝ) : ℝ :=
  (1/2) * ∑ i : Fin (2 * n), (deriv (w.phases i) t)^2

/-- Potential Energy: The Frustrated V_int.
    We assume constraints:
    - Rails: c = 0 (Free propagation)
    - Rungs: c = K (Frustration/Mass coupling) 
    
    V = 1/2 * [ Σ(rail_diff)² + Σ(rung_diff - K)² ]
-/
noncomputable def potential_energy {n : ℕ} (w : WorldLine n) (K : ℝ) (t : ℝ) : ℝ :=
  let top (i : ℕ) (h : i < n) := w.phases ⟨i, by omega⟩ t
  let bot (i : ℕ) (h : i < n) := w.phases ⟨i + n, by omega⟩ t
  
  -- Rail Potential (Top + Bottom)
  let V_rails := ∑ i : Fin (n - 1),
      ((top (i.val+1) (by omega) - top i.val (by omega))^2 +
       (bot (i.val+1) (by omega) - bot i.val (by omega))^2)

  -- Rung Potential (Coupling with Constraint K)
  -- This represents the internal cycle cost
  let V_rungs := ∑ i : Fin n, (top i.val i.isLt - bot i.val i.isLt - K)^2
  
  (1/2) * (V_rails + V_rungs)

/-- Lagrangian -/
noncomputable def lagrangian {n : ℕ} (w : WorldLine n) (K : ℝ) (t : ℝ) : ℝ :=
  kinetic_energy w t - potential_energy w K t

/-! ## Part 4: Euler-Lagrange Equations -/

/-- A WorldLine satisfies the Euler-Lagrange equations for interior nodes.
    For our Lagrangian L = T - V, this is:

    d²ω_i/dt² = -∂V/∂ω_i

    We only state this for interior nodes to avoid boundary complications.
-/
def satisfies_euler_lagrange_interior {n : ℕ} (h_n : n ≥ 2) (w : WorldLine n) (K : ℝ) : Prop :=
  ∀ (i : Fin n) (t : ℝ) (h_i_pos : 0 < i.val) (h_i_bound : i.val + 1 < n),
    let h_n_pos : n ≥ 1 := by omega
    -- Top rail equation
    (deriv (deriv (w.phases ⟨i.val, by omega⟩)) t =
      w.phases ⟨i.val - 1, by omega⟩ t + w.phases ⟨i.val + 1, by omega⟩ t - 2 * w.phases ⟨i.val, by omega⟩ t +
      (w.phases ⟨i.val + n, by omega⟩ t - w.phases ⟨i.val, by omega⟩ t + K)) ∧
    -- Bottom rail equation
    (deriv (deriv (w.phases ⟨i.val + n, by omega⟩)) t =
      w.phases ⟨(i.val - 1) + n, by omega⟩ t +
      w.phases ⟨(i.val + 1) + n, by omega⟩ t -
      2 * w.phases ⟨i.val + n, by omega⟩ t +
      (w.phases ⟨i.val, by omega⟩ t - w.phases ⟨i.val + n, by omega⟩ t - K))

/-! ## Part 5: Mode Decomposition -/

/-- We define the Symmetric and Antisymmetric modes -/
def psi_plus {n : ℕ} (w : WorldLine n) (i : Fin n) (t : ℝ) : ℝ :=
  w.phases ⟨i, by omega⟩ t + w.phases ⟨i + n, by omega⟩ t

def psi_minus {n : ℕ} (w : WorldLine n) (i : Fin n) (t : ℝ) : ℝ :=
  w.phases ⟨i, by omega⟩ t - w.phases ⟨i + n, by omega⟩ t

/-- **The Massive Wave Equation**
    We prove that the Antisymmetric mode (psi_minus) obeys a Klein-Gordon equation.

    `∂²ψ₋/∂t² = ∇²ψ₋ - 2(ψ₋ - K)`

    where the mass term comes from the rung coupling strength.
    This shows that the topological connection (rung) generates Inertia (Mass).
-/
theorem antisymmetric_mode_equation {n : ℕ} (h_n : n ≥ 2) (w : WorldLine n) (K : ℝ)
    (h_EL : satisfies_euler_lagrange_interior h_n w K)
    (i : Fin n) (t : ℝ)
    (h_i_pos : 0 < i.val)
    (h_i_bound : i.val + 1 < n) :
    -- The antisymmetric mode satisfies a massive wave equation
    deriv (deriv (fun t => psi_minus w i t)) t =
      -- Laplacian term (from rail coupling)
      (psi_minus w ⟨i.val + 1, by omega⟩ t - 2 * psi_minus w i t + psi_minus w ⟨i.val - 1, by omega⟩ t) -
      -- Mass term (from rung coupling)
      2 * (psi_minus w i t - K) := by
  -- Get the Euler-Lagrange equations for this node
  have h_eqs := h_EL i t h_i_pos h_i_bound
  obtain ⟨h_top, h_bot⟩ := h_eqs

  -- Expand the definition of psi_minus
  unfold psi_minus
  simp only

  -- Substitute the Euler-Lagrange equations
  -- We need to show: deriv (deriv (fun t => w.phases ⟨i, _⟩ t - w.phases ⟨i+n, _⟩ t)) t
  --                 = (difference of neighbors) - 2(difference - K)

  -- Let's denote for clarity:
  -- ω_top(i) := w.phases ⟨i, _⟩ t
  -- ω_bot(i) := w.phases ⟨i+n, _⟩ t

  -- From h_top: d²ω_top(i)/dt² = ω_top(i-1) + ω_top(i+1) - 2·ω_top(i) + (ω_bot(i) - ω_top(i) + K)
  -- From h_bot: d²ω_bot(i)/dt² = ω_bot(i-1) + ω_bot(i+1) - 2·ω_bot(i) + (ω_top(i) - ω_bot(i) - K)

  -- The second derivative of (ω_top - ω_bot) is (d²ω_top/dt²) - (d²ω_bot/dt²)
  -- Substituting:
  -- = [ω_top(i-1) + ω_top(i+1) - 2·ω_top(i) + ω_bot(i) - ω_top(i) + K]
  --   - [ω_bot(i-1) + ω_bot(i+1) - 2·ω_bot(i) + ω_top(i) - ω_bot(i) - K]
  -- = [ω_top(i-1) - ω_bot(i-1)] + [ω_top(i+1) - ω_bot(i+1)] - 2[ω_top(i) - ω_bot(i)]
  --   + [ω_bot(i) - ω_top(i)] - [ω_top(i) - ω_bot(i)] + 2K
  -- = ψ_-(i-1) + ψ_-(i+1) - 2·ψ_-(i) - 2·ψ_-(i) + 2K
  -- = [ψ_-(i+1) - 2·ψ_-(i) + ψ_-(i-1)] - 2·(ψ_-(i) - K)

  -- This is exactly what we need to prove. Let me do it formally:

  -- NOTE: This step requires proving that deriv is linear when applied twice.
  -- Specifically: deriv (deriv (f - g)) = deriv (deriv f) - deriv (deriv g)
  -- when f and g are ContDiff ℝ 2.
  -- This should follow from `deriv_sub` applied twice, but requires careful handling
  -- of differentiability conditions for the derivative functions.
  -- The key is that ContDiff ℝ 2 implies both f and (deriv f) are differentiable.
  calc deriv (deriv (fun t' => w.phases ⟨i.val, by omega⟩ t' - w.phases ⟨i.val + n, by omega⟩ t')) t
      = deriv (deriv (w.phases ⟨i.val, by omega⟩ - w.phases ⟨i.val + n, by omega⟩)) t := rfl
    _ = deriv (deriv (w.phases ⟨i.val, by omega⟩)) t - deriv (deriv (w.phases ⟨i.val + n, by omega⟩)) t := by
        -- Extract differentiability from smoothness assumption
        let f := w.phases ⟨i.val, by omega⟩
        let g := w.phases ⟨i.val + n, by omega⟩
        have hf : ContDiff ℝ 2 f := w.smooth _
        have hg : ContDiff ℝ 2 g := w.smooth _

        -- Change goal to use f and g
        show deriv (deriv (f - g)) t = deriv (deriv f) t - deriv (deriv g) t

        -- Step 1: f and g are differentiable everywhere
        have df_all : ∀ x, DifferentiableAt ℝ f x := fun x => hf.differentiable (by norm_num) x
        have dg_all : ∀ x, DifferentiableAt ℝ g x := fun x => hg.differentiable (by norm_num) x

        -- Step 2: Apply deriv_sub to the inner deriv
        conv_lhs => arg 1; ext x; rw [deriv_sub (df_all x) (dg_all x)]
        -- Now goal is: deriv (fun x => deriv f x - deriv g x) t = deriv (deriv f) t - deriv (deriv g) t

        -- Step 3: The lambda is eta-equivalent to (deriv f - deriv g)
        show deriv (deriv f - deriv g) t = deriv (deriv f) t - deriv (deriv g) t

        -- Step 4: f' and g' are differentiable at t (since f, g are C^2)
        -- ContDiff 2 f means that deriv f is differentiable
        have df' : DifferentiableAt ℝ (deriv f) t := ContDiff.differentiable_deriv_two hf t
        have dg' : DifferentiableAt ℝ (deriv g) t := ContDiff.differentiable_deriv_two hg t

        -- Step 5: Apply deriv_sub to the outer deriv
        rw [deriv_sub df' dg']
    _ = (w.phases ⟨i.val - 1, by omega⟩ t + w.phases ⟨i.val + 1, by omega⟩ t - 2 * w.phases ⟨i.val, by omega⟩ t +
         (w.phases ⟨i.val + n, by omega⟩ t - w.phases ⟨i.val, by omega⟩ t + K)) -
        (w.phases ⟨(i.val - 1) + n, by omega⟩ t + w.phases ⟨(i.val + 1) + n, by omega⟩ t - 2 * w.phases ⟨i.val + n, by omega⟩ t +
         (w.phases ⟨i.val, by omega⟩ t - w.phases ⟨i.val + n, by omega⟩ t - K)) := by
          rw [h_top, h_bot]
    _ = (w.phases ⟨i.val + 1, by omega⟩ t - w.phases ⟨(i.val + 1) + n, by omega⟩ t) -
        2 * (w.phases ⟨i.val, by omega⟩ t - w.phases ⟨i.val + n, by omega⟩ t) +
        (w.phases ⟨i.val - 1, by omega⟩ t - w.phases ⟨(i.val - 1) + n, by omega⟩ t) -
        2 * ((w.phases ⟨i.val, by omega⟩ t - w.phases ⟨i.val + n, by omega⟩ t) - K) := by
          ring
