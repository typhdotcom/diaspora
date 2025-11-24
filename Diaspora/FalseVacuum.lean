import Diaspora.TopologyDynamics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

set_option maxHeartbeats 500000

namespace DiscreteHodge

open BigOperators

abbrev n_theta : ℕ := 4
@[simp] lemma fin_0 : (0 : Fin n_theta) = ⟨0, by decide⟩ := rfl
@[simp] lemma fin_1 : (1 : Fin n_theta) = ⟨1, by decide⟩ := rfl
@[simp] lemma fin_2 : (2 : Fin n_theta) = ⟨2, by decide⟩ := rfl
@[simp] lemma fin_3 : (3 : Fin n_theta) = ⟨3, by decide⟩ := rfl

-- The edge set defined explicitly
def theta_active : Finset (Fin n_theta × Fin n_theta) := {
    (0,1), (1,0), (1,2), (2,1), (2,0), (0,2), -- Left Loop
    (1,3), (3,1), (3,2), (2,3)                -- Right Loop
  }

def theta_graph : DynamicGraph n_theta where
  active_edges := theta_active
  symmetric := by 
    intro i j
    simp [theta_active]
    tauto
  no_loops := by 
    intro i
    simp [theta_active]
    fin_cases i <;> decide

/-! ## Parameterized Fields -/

/--
Construct a constraint field (Sigma) based on three flux parameters:
- Ft: Flux across the Trap (1,2)
- Fs: Flux across the Smart Edge (1,3)
- Fa: Flux (Pre-tension) on Anchors (0,1)
-/
def make_sigma (Ft Fs Fa : ℝ) : C1 n_theta := {
  val := fun i j =>
    if (i=1 ∧ j=2) then Ft else if (i=2 ∧ j=1) then -Ft      
    else if (i=1 ∧ j=3) then Fs else if (i=3 ∧ j=1) then -Fs  
    else if (i=3 ∧ j=2) then Fs else if (i=2 ∧ j=3) then -Fs
    else if (i=0 ∧ j=1) then -Fa else if (i=1 ∧ j=0) then Fa
    else if (i=0 ∧ j=2) then Fa else if (i=2 ∧ j=0) then -Fa
    else 0
  skew := by intro i j; fin_cases i <;> fin_cases j <;> simp
}

/--
Construct a relaxation potential (Phi) based on a magnitude P.
Symmetric relaxation: Node 1 lowers by P, Node 2 raises by P.
-/
noncomputable def make_phi (P : ℝ) : C0 n_theta :=
  fun i =>
    if i = 0 then 0
    else if i = 1 then -P
    else if i = 2 then P
    else 0

/-! ## Strain Analysis Theorems -/

-- Lemma: In the Greedy limit (phi=0), strain is exactly flux squared.
lemma greedy_strain_is_flux_sq (Ft Fs Fa : ℝ) (i j : Fin n_theta) : 
  edge_strain (fun _ => 0) (make_sigma Ft Fs Fa) i j = ((make_sigma Ft Fs Fa).val i j)^2 := by
  unfold edge_strain d0; simp

/--
Theorem: The Quenched Instability.
If the Trap Flux (Ft) is higher than the Anchor Flux (Fa) and Smart Flux (Fs),
and the system cannot relax (Greedy), the Trap (1,2) sustains the highest strain.
-/
theorem quenched_instability (Ft Fs Fa : ℝ)
  (h_trap_dominant : Ft > Fs ∧ Ft > Fa)
  (h_pos : Ft > 0 ∧ Fs > 0 ∧ Fa > 0) :
  let σ := make_sigma Ft Fs Fa
  let ϕ := fun (_ : Fin n_theta) => (0 : ℝ)
  edge_strain ϕ σ 1 2 > edge_strain ϕ σ 1 3 ∧
  edge_strain ϕ σ 1 2 > edge_strain ϕ σ 0 1 := by
  intro σ ϕ
  rw [greedy_strain_is_flux_sq, greedy_strain_is_flux_sq, greedy_strain_is_flux_sq]
  simp only [make_sigma]
  norm_num
  simp
  constructor
  · apply sq_lt_sq.mpr; rw [abs_of_pos h_pos.1, abs_of_pos h_pos.2.1]; exact h_trap_dominant.1
  · apply sq_lt_sq.mpr; rw [abs_of_pos h_pos.1, abs_of_pos h_pos.2.2]; exact h_trap_dominant.2

set_option linter.unusedSimpArgs false in
/--
Theorem: The Annealed Crossover (False Vacuum Protection).
There exists a relaxation magnitude P such that the Trap (1,2) becomes
safer than the Smart Edge (1,3), even though Ft > Fs.
-/
theorem annealed_crossover (Ft Fs Fa : ℝ) (P : ℝ)
  (h_relax : P = Ft / 2 + 1)
  (h_smart_weak : Fs < P - 2) :
  let σ := make_sigma Ft Fs Fa
  let ϕ := make_phi P
  edge_strain ϕ σ 1 2 < edge_strain ϕ σ 1 3 := by
  intro σ ϕ
  unfold edge_strain d0
  simp only [C1.val]
  have hϕ1 : ϕ 1 = -P := rfl
  have hϕ2 : ϕ 2 = P := rfl
  have hϕ3 : ϕ 3 = 0 := rfl
  have hσ12 : σ.val 1 2 = Ft := rfl
  have hσ13 : σ.val 1 3 = Fs := rfl
  rw [hϕ2, hϕ1, hϕ3, hσ12, hσ13]
  simp only [sub_neg_eq_add, zero_add]
  rw [h_relax]
  have lhs : (Ft / 2 + 1 + (Ft / 2 + 1) - Ft) ^ 2 = 4 := by field_simp; ring
  rw [lhs]
  have : (4:ℝ) = 2^2 := by norm_num
  rw [this, sq_lt_sq]
  rw [abs_of_pos (by norm_num : (2:ℝ) > 0)]
  have h_ineq : Ft / 2 + 1 - Fs > 2 := by
    rw [h_relax] at h_smart_weak
    linarith
  rw [abs_of_pos (by linarith)]
  exact h_ineq

end DiscreteHodge
