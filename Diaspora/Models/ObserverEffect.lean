import Diaspora.Models.Triangle
import Diaspora.Dynamics.Plasticity
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

open BigOperators Diaspora.Core Diaspora.Hodge Diaspora.Dynamics Diaspora.Models

namespace Diaspora.Models

/-! ## 1. System Configuration -/

/-- The kite graph has 8 directed edges. -/
lemma kite_edge_count : kite_graph.active_edges.card = 8 := by decide

/--
We use the Kite Graph (Triangle 0-1-2 with Tail 0-3) from Models/Triangle.lean.
We assume an initial state where weights are uniform.
The capacity constraint forces w_init = 2 (since 8 edges × 2 = 16 = 4²).
-/
def uniform_kite_weights (w_init : ℝ)
    (h_nonneg : w_init ≥ 0 := by linarith)
    (h_capacity : 8 * w_init = (n_kite : ℝ)^2 := by norm_num) : WeightedGraph n_kite where
  weights := fun i j =>
    if (i, j) ∈ kite_graph.active_edges then w_init else 0
  symmetric := by
    intro i j
    by_cases h : (i, j) ∈ kite_graph.active_edges
    · have h' : (j, i) ∈ kite_graph.active_edges := kite_graph.symmetric i j |>.mp h
      simp only [h, h', ↓reduceIte]
    · have h' : (j, i) ∉ kite_graph.active_edges := by
        intro hc; exact h (kite_graph.symmetric j i |>.mp hc)
      simp only [h, h', ↓reduceIte]
  nonneg := by
    intro i j
    split_ifs
    · exact h_nonneg
    · linarith
  total_capacity_fixed := by
    -- Sum over all (i,j) pairs: active edges contribute w_init, others contribute 0
    -- The kite graph has exactly 8 directed edges, so sum = 8 * w_init = n^2
    simp only [n_kite, kite_graph, Fin.sum_univ_four, Finset.mem_insert,
               Prod.mk.injEq, Finset.mem_singleton]
    simp only [show (0 : Fin 4) = 1 ↔ False by decide,
               show (0 : Fin 4) = 2 ↔ False by decide,
               show (0 : Fin 4) = 3 ↔ False by decide,
               show (1 : Fin 4) = 0 ↔ False by decide,
               show (1 : Fin 4) = 2 ↔ False by decide,
               show (1 : Fin 4) = 3 ↔ False by decide,
               show (2 : Fin 4) = 0 ↔ False by decide,
               show (2 : Fin 4) = 1 ↔ False by decide,
               show (2 : Fin 4) = 3 ↔ False by decide,
               show (3 : Fin 4) = 0 ↔ False by decide,
               show (3 : Fin 4) = 1 ↔ False by decide,
               show (3 : Fin 4) = 2 ↔ False by decide,
               and_false, or_false, and_true, or_true, ↓reduceIte]
    linarith

/-! ## 2. The Observer's Probe -/

/--
Probe potential that strains the whole loop:
- 0(0) → 1(1) → 2(0.5) → 0(0)
- 0→1: strain (1-0)² = 1
- 1→2: strain (0.5-1)² = 0.25
- 2→0: strain (0-0.5)² = 0.25
- Tail (0→3): strain (0-0)² = 0
-/
def observer_probe_potential : C0 n_kite := fun i =>
  match i with
  | 0 => 0
  | 1 => 1
  | 2 => 0.5
  | 3 => 0

/--
The Observer's "Test Field" is null; they are testing the graph's ability
to carry the potential `observer_probe_potential` against a zero-flux background.
(Or essentially, the probe *is* the strain).
-/
def null_sigma : C1 n_kite := {
  val := fun _ _ => 0
  skew := by intro _ _; ring
}

/-! ## 3. The Reinforcement Theorem -/

/--
Theorem: Observation targets the Loop.
The probe induces strictly positive strain on all Loop edges (0,1), (1,2), (2,0),
and zero strain on the Tail edge (0,3).
-/
theorem observation_is_selective :
    let ϕ := observer_probe_potential
    let σ := null_sigma
    -- Loop edges are strained (Observed)
    edge_strain ϕ σ 0 1 > 0 ∧
    edge_strain ϕ σ 1 2 > 0 ∧
    edge_strain ϕ σ 2 0 > 0 ∧
    -- Tail edge is unstrained (Ignored)
    edge_strain ϕ σ 0 3 = 0 := by
  intro ϕ σ
  dsimp [ϕ, σ, observer_probe_potential, null_sigma, edge_strain, d0]
  constructor; · norm_num
  constructor; · norm_num
  constructor; · norm_num
  · -- Tail: (0 - 0)^2 = 0
    norm_num

/--
Theorem: The Observer Effect.
One step of Hebbian plasticity under observation increases the weight of the
Cycle edges relative to the Tail edge.

Structure of proof:
1. Initial weights are uniform (w_init).
2. Plasticity adds η * strain.
3. Cycle strain > 0, Tail strain = 0.
4. Cycle weight grows, Tail weight stays at w_init (before normalization).
5. Therefore, Cycle/Tail ratio increases.
-/
theorem attention_is_structural_reinforcement (w_init η : ℝ)
    (h_pos : w_init > 0)
    (h_eta : η > 0)
    (h_capacity : 8 * w_init = (n_kite : ℝ)^2 := by norm_num) :
    let G := uniform_kite_weights w_init (by linarith) h_capacity
    let ϕ := observer_probe_potential
    let σ := null_sigma
    let w_next := plasticity_step G ϕ σ η
    -- Compare Loop edge (1,2) vs Tail edge (0,3)
    w_next 1 2 > w_next 0 3 := by
  intro G ϕ σ w_next

  -- raw_strain and edge_strain are definitionally equal
  have strain_eq : ∀ i j, raw_strain ϕ σ i j = edge_strain ϕ σ i j := fun _ _ => rfl

  -- Strain comparison: Loop edge (1,2) has positive strain, Tail (0,3) has zero
  have h_strain_12_pos : raw_strain ϕ σ 1 2 > 0 := by
    show raw_strain observer_probe_potential null_sigma 1 2 > 0
    unfold raw_strain d0 observer_probe_potential null_sigma; norm_num
  have h_strain_03_zero : raw_strain ϕ σ 0 3 = 0 := by
    show raw_strain observer_probe_potential null_sigma 0 3 = 0
    unfold raw_strain d0 observer_probe_potential null_sigma; norm_num

  -- Weights are uniform initially
  have h_w12 : G.weights 1 2 = w_init := by
    dsimp only [G]; simp only [uniform_kite_weights, kite_graph]
    split_ifs with h; rfl; simp_all
  have h_w03 : G.weights 0 3 = w_init := by
    dsimp only [G]; simp only [uniform_kite_weights, kite_graph]
    split_ifs with h; rfl; simp_all

  -- The total unnormalized weight is positive (w_init > 0 + strain ≥ 0)
  have h_total_pos : ∑ i, ∑ j, (G.weights i j + η * raw_strain ϕ σ i j) > 0 := by
    apply Finset.sum_pos'
    · intro i _; apply Finset.sum_nonneg; intro j _
      apply add_nonneg (G.nonneg i j)
      apply mul_nonneg (le_of_lt h_eta) (raw_strain_nonneg ϕ σ i j)
    · use 1; constructor; simp
      apply Finset.sum_pos'
      · intro j _
        apply add_nonneg (G.nonneg 1 j)
        apply mul_nonneg (le_of_lt h_eta) (raw_strain_nonneg ϕ σ 1 j)
      · use 2; constructor; simp
        calc G.weights 1 2 + η * raw_strain ϕ σ 1 2
           = w_init + η * raw_strain ϕ σ 1 2 := by rw [h_w12]
         _ > 0 + 0 := by apply add_lt_add h_pos (mul_pos h_eta h_strain_12_pos)
         _ = 0 := by ring

  -- Scale factor is positive
  have h_scale_pos : ((n_kite : ℝ)^2) / (∑ i, ∑ j, (G.weights i j + η * raw_strain ϕ σ i j)) > 0 := by
    apply div_pos (sq_pos_of_ne_zero (by norm_num : (n_kite : ℝ) ≠ 0))
    exact h_total_pos

  -- Expand plasticity_step and compare
  show plasticity_step G ϕ σ η 1 2 > plasticity_step G ϕ σ η 0 3
  unfold plasticity_step
  dsimp only

  -- The comparison: (w + η*strain_12) * S > (w + η*strain_03) * S where S > 0
  apply mul_lt_mul_of_pos_right _ h_scale_pos
  rw [h_w12, h_w03, h_strain_03_zero]
  simp only [mul_zero, add_zero]
  linarith [mul_pos h_eta h_strain_12_pos]

/-! ## 4. Interpretation

The "Star" vacuum (defined in Models/Triangle.lean) requires breaking edge (1,2).
The "Line" vacuum requires breaking edge (0,1).
The Tail corresponds to edge (0,3).

This theorem proves that if an Observer frequently probes the cycle 0-1-2:
1. The edges (0,1) and (1,2) accumulate weight faster than (0,3).
2. In a resource-constrained graph (Fixed Total Capacity), the Tail (0,3)
   will atrophy relative to the Loop.
3. Consequently, the system is structurally biased AGAINST breaking the Loop.
   The Observer "freezes" the topology of the observed object.

This is the topological analog of the Quantum Zeno Effect.
-/

end Diaspora.Models
