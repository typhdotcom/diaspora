import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith

open BigOperators Complex

namespace Diaspora.Core

/-! ## Dynamic Graph Structure -/

/--
A graph with fixed vertices but dynamic edges.
Vertices persist while edges can break under strain.
-/
structure DynamicGraph (n : ℕ) where
  /-- Active (unbroken) edges -/
  active_edges : Finset (Fin n × Fin n)
  /-- Active edges are symmetric (undirected graph) -/
  symmetric : ∀ i j, (i, j) ∈ active_edges ↔ (j, i) ∈ active_edges
  /-- No self-loops -/
  no_loops : ∀ i, (i, i) ∉ active_edges
deriving DecidableEq

/-- The complete graph on n vertices (all edges active) -/
def DynamicGraph.complete (n : ℕ) : DynamicGraph n where
  active_edges := Finset.univ.filter (fun (i, j) => i ≠ j)
  symmetric := by
    intro i j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  no_loops := by
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]

/-! ## Classical Cochains -/

/-- A 0-cochain is a function on vertices (Phases) -/
def C0 (n : ℕ) := Fin n → ℝ

/-- A 1-cochain is a skew-symmetric function on edges (Constraints/Flux) -/
structure C1 (n : ℕ) where
  val : Fin n → Fin n → ℝ
  skew : ∀ i j, val i j = -val j i

@[ext]
lemma C1.ext {n : ℕ} {σ τ : C1 n} (h : ∀ i j, σ.val i j = τ.val i j) : σ = τ := by
  cases σ; cases τ; congr; ext i j; exact h i j

/-- The Coboundary Operator d⁰: C⁰ → C¹ (Gradient) -/
def d0 {n : ℕ} (ϕ : C0 n) : C1 n := {
  val := fun i j => ϕ j - ϕ i
  skew := by intro i j; ring
}

/-- Inner product on 1-cochains (sum over unique edges) -/
noncomputable def inner_product_C1 {n : ℕ} [Fintype (Fin n)] (σ τ : C1 n) : ℝ :=
  (1/2) * ∑ i : Fin n, ∑ j : Fin n, (σ.val i j) * (τ.val i j)

/-- Squared Norm of a 1-cochain -/
noncomputable def norm_sq {n : ℕ} [Fintype (Fin n)] (σ : C1 n) : ℝ := inner_product_C1 σ σ

/-! ## Active Forms (Topology-Aware Cochains) -/

/--
Active forms on a dynamic graph: cochains that vanish on broken edges.
This is the mathematically correct type for constraints that respect topology.
-/
def ActiveForm {n : ℕ} (G : DynamicGraph n) : Type :=
  { σ : C1 n // ∀ i j, (i, j) ∉ G.active_edges → σ.val i j = 0 }

namespace Diaspora.Core.ActiveForm

variable {n : ℕ} {G : DynamicGraph n}

/-- Embed ActiveForm into C1 -/
def toC1 (σ : ActiveForm G) : C1 n := σ.val

/-- Extensionality for active forms -/
@[ext]
lemma ext {σ τ : ActiveForm G} (h : ∀ i j, σ.val.val i j = τ.val.val i j) : σ = τ := by
  cases σ; cases τ
  congr
  ext i j
  exact h i j

instance : Zero (ActiveForm G) where
  zero := ⟨{ val := fun _ _ => 0, skew := by intro i j; ring }, by intro i j _; rfl⟩

instance : Add (ActiveForm G) where
  add σ τ := ⟨{ val := fun i j => σ.val.val i j + τ.val.val i j,
                 skew := by intro i j; rw [σ.val.skew, τ.val.skew]; ring },
               by intro i j h; simp only; rw [σ.property _ _ h, τ.property _ _ h]; ring⟩

instance : Neg (ActiveForm G) where
  neg σ := ⟨{ val := fun i j => -σ.val.val i j,
              skew := by intro i j; rw [σ.val.skew] },
            by intro i j h; simp only; rw [σ.property _ _ h]; norm_num⟩

instance : Sub (ActiveForm G) where
  sub σ τ := σ + (-τ)

instance : AddCommGroup (ActiveForm G) where
  add_assoc := by intro a b c; ext i j; show (a.val.val i j + b.val.val i j) + c.val.val i j = a.val.val i j + (b.val.val i j + c.val.val i j); ring
  zero_add := by intro a; ext i j; show 0 + a.val.val i j = a.val.val i j; ring
  add_zero := by intro a; ext i j; show a.val.val i j + 0 = a.val.val i j; ring
  add_comm := by intro a b; ext i j; show a.val.val i j + b.val.val i j = b.val.val i j + a.val.val i j; ring
  neg_add_cancel := by intro a; ext i j; show -(a.val.val i j) + a.val.val i j = 0; ring
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : SMul ℝ (ActiveForm G) where
  smul r σ := ⟨{ val := fun i j => r * σ.val.val i j,
                 skew := by intro i j; rw [σ.val.skew]; ring },
               by intro i j h; simp only; rw [σ.property _ _ h]; ring⟩

instance : Module ℝ (ActiveForm G) where
  one_smul := by intro a; ext i j; show 1 * a.val.val i j = a.val.val i j; ring
  mul_smul := by intro r s a; ext i j; show (r * s) * a.val.val i j = r * (s * a.val.val i j); ring
  smul_zero := by intro r; ext i j; show r * 0 = 0; ring
  smul_add := by intro r a b; ext i j; show r * (a.val.val i j + b.val.val i j) = r * a.val.val i j + r * b.val.val i j; ring
  add_smul := by intro r s a; ext i j; show (r + s) * a.val.val i j = r * a.val.val i j + s * a.val.val i j; ring
  zero_smul := by intro a; ext i j; show 0 * a.val.val i j = 0; ring

/-- Inner product on active forms (restriction of inner_product_C1) -/
noncomputable def inner [Fintype (Fin n)] (σ τ : ActiveForm G) : ℝ :=
  inner_product_C1 σ.val τ.val

noncomputable instance [Fintype (Fin n)] : Inner ℝ (ActiveForm G) where
  inner := inner

lemma inner_add_left [Fintype (Fin n)] (σ τ ρ : ActiveForm G) :
    inner (σ + τ) ρ = inner σ ρ + inner τ ρ := by
  unfold inner inner_product_C1
  have : ∀ i j, (σ + τ).val.val i j = σ.val.val i j + τ.val.val i j := by intro i j; rfl
  simp only [this, add_mul, Finset.sum_add_distrib]
  ring

lemma inner_smul_left [Fintype (Fin n)] (r : ℝ) (σ τ : ActiveForm G) :
    inner (r • σ) τ = r * inner σ τ := by
  unfold inner inner_product_C1
  have : ∀ i j, (r • σ).val.val i j = r * σ.val.val i j := by intro i j; rfl
  simp only [this]
  have h1 : ∀ i, ∑ j, r * σ.val.val i j * τ.val.val i j = r * ∑ j, σ.val.val i j * τ.val.val i j := by
    intro i
    conv_lhs => arg 2; intro j; rw [mul_assoc]
    rw [←Finset.mul_sum]
  simp only [h1, ←Finset.mul_sum]
  ring

lemma inner_comm [Fintype (Fin n)] (σ τ : ActiveForm G) :
    inner σ τ = inner τ σ := by
  unfold inner inner_product_C1
  congr 1
  congr 1; ext i
  congr 1; ext j
  ring

lemma inner_self_nonneg [Fintype (Fin n)] (σ : ActiveForm G) :
    0 ≤ inner σ σ := by
  unfold inner inner_product_C1
  apply mul_nonneg; norm_num
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  exact mul_self_nonneg _

lemma inner_self_eq_zero [Fintype (Fin n)] (σ : ActiveForm G) :
    inner σ σ = 0 ↔ σ = 0 := by
  constructor
  · intro h
    ext i j
    unfold inner inner_product_C1 at h
    have h_nonneg : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, σ.val.val i j * σ.val.val i j := by
      apply Finset.sum_nonneg; intro k _
      apply Finset.sum_nonneg; intro l _
      exact mul_self_nonneg _
    have h_sum_zero : ∑ i : Fin n, ∑ j : Fin n, σ.val.val i j * σ.val.val i j = 0 := by
      have : (1/2) * ∑ i : Fin n, ∑ j : Fin n, σ.val.val i j * σ.val.val i j = 0 := h
      linarith
    have h_term : σ.val.val i j * σ.val.val i j = 0 := by
      have : ∀ k ∈ Finset.univ, ∀ l ∈ Finset.univ, σ.val.val k l * σ.val.val k l = 0 := by
        intro k _ l _
        by_contra h_ne
        have h_pos : 0 < σ.val.val k l * σ.val.val k l := by
          apply mul_self_pos.mpr
          intro h_eq; apply h_ne; rw [h_eq]; ring
        have : 0 < ∑ i : Fin n, ∑ j : Fin n, σ.val.val i j * σ.val.val i j := by
          apply Finset.sum_pos'
          · intro i _; apply Finset.sum_nonneg; intro m _; exact mul_self_nonneg _
          · use k; constructor; simp
            apply Finset.sum_pos'
            · intro m _; exact mul_self_nonneg _
            · exact ⟨l, by simp, h_pos⟩
        linarith
      exact this i (by simp) j (by simp)
    have : σ.val.val i j = 0 := by
      by_contra h_ne
      have : 0 < σ.val.val i j * σ.val.val i j := mul_self_pos.mpr h_ne
      linarith
    exact this
  · intro h; rw [h]; unfold inner inner_product_C1
    have : ∀ i j, (0 : ActiveForm G).val.val i j = 0 := by intro i j; rfl
    simp [this]

noncomputable instance [Fintype (Fin n)] : Norm (ActiveForm G) where
  norm σ := Real.sqrt (inner σ σ)

noncomputable instance [Fintype (Fin n)] : Dist (ActiveForm G) where
  dist σ τ := ‖σ - τ‖

lemma cauchy_schwarz [Fintype (Fin n)] (σ τ : ActiveForm G) :
    inner σ τ * inner σ τ ≤ inner σ σ * inner τ τ := by
  by_cases h : inner τ τ = 0
  · have : τ = 0 := inner_self_eq_zero τ |>.mp h
    rw [this]
    unfold inner inner_product_C1
    have : ∀ i j, (0 : ActiveForm G).val.val i j = 0 := by intro i j; rfl
    simp [this]
  · have h_pos : 0 < inner τ τ := by
      have h_nn := inner_self_nonneg τ
      cases h_nn.lt_or_eq with
      | inl hlt => exact hlt
      | inr heq => exact absurd heq.symm h
    let t := -(inner σ τ / inner τ τ)
    have key : 0 ≤ inner (σ + t • τ) (σ + t • τ) := inner_self_nonneg _
    have expand : inner (σ + t • τ) (σ + t • τ) = inner σ σ + 2 * t * inner σ τ + t * t * inner τ τ := by
      unfold inner inner_product_C1
      have h : ∀ i j, (σ + t • τ).val.val i j * (σ + t • τ).val.val i j =
                      σ.val.val i j * σ.val.val i j + 2 * t * (σ.val.val i j * τ.val.val i j) + t * t * (τ.val.val i j * τ.val.val i j) := by
        intro i j
        have : (σ + t • τ).val.val i j = σ.val.val i j + t * τ.val.val i j := rfl
        rw [this]
        ring
      simp only [h, Finset.sum_add_distrib, Finset.mul_sum]
      simp_rw [← Finset.mul_sum]; ring
    rw [expand] at key
    simp only [t] at key
    field_simp at key
    nlinarith [sq_nonneg (inner σ τ), sq_nonneg (inner τ τ), inner_self_nonneg σ, inner_self_nonneg τ, key, h_pos]

lemma sqrt_inner_triangle [Fintype (Fin n)] (σ τ : ActiveForm G) :
    Real.sqrt (inner (σ + τ) (σ + τ)) ≤ Real.sqrt (inner σ σ) + Real.sqrt (inner τ τ) := by
  have h_nn_lhs : 0 ≤ inner (σ + τ) (σ + τ) := inner_self_nonneg _
  have h_nn_σ : 0 ≤ inner σ σ := inner_self_nonneg _
  have h_nn_τ : 0 ≤ inner τ τ := inner_self_nonneg _
  have h_nn_rhs : 0 ≤ Real.sqrt (inner σ σ) + Real.sqrt (inner τ τ) := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [Real.sqrt_le_left h_nn_rhs]
  have expand : inner (σ + τ) (σ + τ) = inner σ σ + 2 * inner σ τ + inner τ τ := by
    calc inner (σ + τ) (σ + τ)
        = inner σ (σ + τ) + inner τ (σ + τ) := inner_add_left σ τ (σ + τ)
      _ = inner σ σ + inner σ τ + (inner τ σ + inner τ τ) := by
          rw [inner_comm σ (σ + τ), inner_add_left σ τ σ, inner_comm _ σ, inner_comm _ σ,
              inner_comm τ (σ + τ), inner_add_left σ τ τ, inner_comm _ τ, inner_comm _ τ]
      _ = inner σ σ + 2 * inner σ τ + inner τ τ := by rw [inner_comm τ σ]; ring
  rw [expand]
  have sqrt_sq_σ : Real.sqrt (inner σ σ) * Real.sqrt (inner σ σ) = inner σ σ := by rw [← sq]; exact Real.sq_sqrt h_nn_σ
  have sqrt_sq_τ : Real.sqrt (inner τ τ) * Real.sqrt (inner τ τ) = inner τ τ := by rw [← sq]; exact Real.sq_sqrt h_nn_τ
  rw [add_sq]
  simp only [sq, sqrt_sq_σ, sqrt_sq_τ]
  have cs := cauchy_schwarz σ τ
  have : inner σ τ ≤ Real.sqrt (inner σ σ) * Real.sqrt (inner τ τ) := by
    have h1 : inner σ τ * inner σ τ ≤ Real.sqrt (inner σ σ) * Real.sqrt (inner σ σ) * (Real.sqrt (inner τ τ) * Real.sqrt (inner τ τ)) := by
      rw [sqrt_sq_σ, sqrt_sq_τ]; exact cs
    by_cases h : 0 ≤ inner σ τ
    · have : Real.sqrt (inner σ τ * inner σ τ) ≤ Real.sqrt (Real.sqrt (inner σ σ) * Real.sqrt (inner σ σ) * (Real.sqrt (inner τ τ) * Real.sqrt (inner τ τ))) := by
        apply Real.sqrt_le_sqrt; exact h1
      rw [← sq, Real.sqrt_sq h] at this
      rw [sqrt_sq_σ, sqrt_sq_τ] at this
      rwa [Real.sqrt_mul h_nn_σ] at this
    · push_neg at h
      calc inner σ τ ≤ 0 := le_of_lt h
        _ ≤ Real.sqrt (inner σ σ) * Real.sqrt (inner τ τ) := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  linarith

noncomputable instance [Fintype (Fin n)] : MetricSpace (ActiveForm G) where
  dist_self := by
    intro σ
    show ‖σ - σ‖ = 0
    rw [sub_self]
    show Real.sqrt (inner 0 0) = 0
    have : inner (0 : ActiveForm G) 0 = 0 := by
      unfold inner inner_product_C1
      have : ∀ i j, (0 : ActiveForm G).val.val i j = 0 := by intro i j; rfl
      simp [this]
    rw [this, Real.sqrt_zero]
  dist_comm := by
    intro σ τ
    show ‖σ - τ‖ = ‖τ - σ‖
    show Real.sqrt (inner (σ - τ) (σ - τ)) = Real.sqrt (inner (τ - σ) (τ - σ))
    congr 1
    unfold inner inner_product_C1
    have : ∀ i j, (σ - τ).val.val i j * (σ - τ).val.val i j = (τ - σ).val.val i j * (τ - σ).val.val i j := by
      intro i j
      have h : (σ - τ).val.val i j = -(τ - σ).val.val i j := by
        show σ.val.val i j - τ.val.val i j = -(τ.val.val i j - σ.val.val i j)
        ring
      rw [h]; ring
    simp only [this]
  dist_triangle := by
    intro σ τ ρ
    show ‖σ - ρ‖ ≤ ‖σ - τ‖ + ‖τ - ρ‖
    have : σ - ρ = (σ - τ) + (τ - ρ) := by
      ext i j
      show (σ - ρ).val.val i j = ((σ - τ) + (τ - ρ)).val.val i j
      show σ.val.val i j - ρ.val.val i j = (σ.val.val i j - τ.val.val i j) + (τ.val.val i j - ρ.val.val i j)
      ring
    rw [this]
    show Real.sqrt (inner ((σ - τ) + (τ - ρ)) ((σ - τ) + (τ - ρ))) ≤ Real.sqrt (inner (σ - τ) (σ - τ)) + Real.sqrt (inner (τ - ρ) (τ - ρ))
    exact sqrt_inner_triangle (σ - τ) (τ - ρ)
  eq_of_dist_eq_zero := by
    intro σ τ h
    show σ = τ
    have h' : Real.sqrt (inner (σ - τ) (σ - τ)) = 0 := h
    rw [Real.sqrt_eq_zero (inner_self_nonneg _)] at h'
    have h_zero := inner_self_eq_zero (σ - τ) |>.mp h'
    ext i j
    have : (σ - τ).val.val i j = 0 := by rw [h_zero]; rfl
    have : σ.val.val i j - τ.val.val i j = 0 := this
    linarith

noncomputable instance [Fintype (Fin n)] : NormedAddCommGroup (ActiveForm G) where
  dist_eq := by intro σ τ; rfl

noncomputable instance [Fintype (Fin n)] : NormedSpace ℝ (ActiveForm G) where
  norm_smul_le := by
    intro r x
    show Real.sqrt (inner (r • x) (r • x)) ≤ |r| * Real.sqrt (inner x x)
    have h : inner (r • x) (r • x) = r^2 * inner x x := by
      calc inner (r • x) (r • x)
          = r * inner x (r • x) := inner_smul_left r x (r • x)
        _ = r * inner (r • x) x := by rw [inner_comm]
        _ = r * (r * inner x x) := by rw [inner_smul_left]
        _ = r^2 * inner x x := by ring
    rw [h, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

noncomputable instance [Fintype (Fin n)] : InnerProductSpace ℝ (ActiveForm G) where
  norm_sq_eq_re_inner := by intro σ; simp [Norm.norm]; rw [Real.sq_sqrt (inner_self_nonneg σ)]; rfl
  conj_inner_symm := by intro x y; show (starRingEnd ℝ) (inner y x) = inner x y; simp [starRingEnd]; exact inner_comm y x
  add_left := by intro x y z; show inner (x + y) z = inner x z + inner y z; exact inner_add_left x y z
  smul_left := by intro r x y; show inner (y • r) x = (starRingEnd ℝ) y * inner r x; simp [starRingEnd]; exact inner_smul_left y r x

end Diaspora.Core.ActiveForm

/-! ## Graph-Aware Operators -/

/--
The graph gradient d_G: takes a potential and returns the edge-wise differences,
respecting the topology (zero on broken edges).
-/
noncomputable def d_G {n : ℕ} (G : DynamicGraph n) (φ : C0 n) : ActiveForm G :=
  ⟨{ val := fun i j => if (i, j) ∈ G.active_edges then φ j - φ i else 0,
     skew := by
       intro i j
       by_cases h : (i, j) ∈ G.active_edges
       · have h' : (j, i) ∈ G.active_edges := G.symmetric i j |>.mp h
         simp only [h, h', ↓reduceIte]
         ring
       · have h' : (j, i) ∉ G.active_edges := by
           intro hcontra
           have := G.symmetric j i |>.mp hcontra
           exact h this
         simp only [h, h', ↓reduceIte, neg_zero] },
   by intro i j h_not_active
      simp only [h_not_active, ↓reduceIte]⟩

/--
The graph divergence δ_G: sums flow only from active neighbors.
-/
noncomputable def δ_G {n : ℕ} [Fintype (Fin n)] (G : DynamicGraph n) (σ : ActiveForm G) : C0 n :=
  fun i => ∑ j : Fin n, σ.val.val i j

/--
The graph Laplacian Δ_G: composition of divergence and gradient.
This is the fundamental operator encoding the topology's constraints.
-/
noncomputable def Δ_G {n : ℕ} [Fintype (Fin n)] (G : DynamicGraph n) (φ : C0 n) : C0 n :=
  δ_G G (d_G G φ)

/-- The residual: dϕ - σ -/
noncomputable def residual {n : ℕ} (ϕ : C0 n) (σ : C1 n) : C1 n :=
  { val := fun i j => (d0 ϕ).val i j - σ.val i j,
    skew := by intro i j; simp [d0]; rw [σ.skew]; ring }

/-- Harmonic forms: divergence-free at every node -/
def IsHarmonic {n : ℕ} [Fintype (Fin n)] (σ : C1 n) : Prop :=
  ∀ i : Fin n, ∑ j : Fin n, σ.val i j = 0

/--
Harmonic Flow Conservation (Kirchhoff's Current Law).

If a node `i` acts as a bridge strictly between `prev` and `next`
(meaning γ is zero on all other edges connected to `i`),
then the harmonic flow entering from `prev` must exactly equal the flow exiting to `next`.

This reduces solving harmonic forms on cycles from N linear equations to 1 variable.
-/
lemma harmonic_flow_transfer {n : ℕ} [Fintype (Fin n)]
  (γ : C1 n) (i prev next : Fin n)
  (h_harm : IsHarmonic γ)
  (h_isolation : ∀ x, x ≠ prev ∧ x ≠ next → γ.val i x = 0) :
  γ.val prev i = γ.val i next := by
  have h_div_zero := h_harm i
  unfold IsHarmonic at h_div_zero

  let relevant : Finset (Fin n) := {prev, next}

  rw [←Finset.sum_subset (s₁ := relevant)] at h_div_zero
  swap
  · simp
  swap
  · intro x _ hx
    have : x ≠ prev ∧ x ≠ next := by
      unfold relevant at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      push_neg at hx
      exact hx
    exact h_isolation x this

  by_cases h : prev = next
  · subst h
    have : γ.val i prev = 0 := by
      have eq : ({prev, prev} : Finset (Fin n)) = {prev} := by simp
      have : ∑ x ∈ relevant, γ.val i x = ∑ x ∈ ({prev} : Finset (Fin n)), γ.val i x := by
        unfold relevant
        rw [eq]
      rw [this] at h_div_zero
      simp at h_div_zero
      exact h_div_zero
    rw [γ.skew prev i, this]
    linarith
  · simp only [relevant, Finset.sum_insert, Finset.mem_singleton, h, not_false_eq_true, Finset.sum_singleton] at h_div_zero
    rw [γ.skew i prev] at h_div_zero
    linarith

/-- The divergence operator d*: C¹ → C⁰ (negative adjoint of coboundary) -/
noncomputable def divergence {n : ℕ} [Fintype (Fin n)] (σ : C1 n) : C0 n :=
  fun i => - ∑ j : Fin n, σ.val i j

/-- divergence is the (negative) adjoint of d0 under the inner product -/
lemma divergence_is_adjoint {n : ℕ} [Fintype (Fin n)] (ϕ : C0 n) (σ : C1 n) :
  inner_product_C1 (d0 ϕ) σ = ∑ i : Fin n, ϕ i * divergence σ i := by
  unfold inner_product_C1 d0 divergence
  simp only
  have key : ∑ i : Fin n, ∑ j : Fin n, (ϕ j - ϕ i) * σ.val i j = 2 * ∑ i : Fin n, ϕ i * (-∑ j : Fin n, σ.val i j) := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    conv_lhs =>
      enter [1]
      rw [Finset.sum_comm]
    conv_lhs =>
      enter [1, 2, i, 2, j]
      rw [σ.skew]
    simp only [mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, two_mul, Finset.sum_add_distrib]
    ring
  rw [key]
  ring

/-- The graph Laplacian Δ = d* ∘ d: C⁰ → C⁰ -/
noncomputable def graph_laplacian {n : ℕ} [Fintype (Fin n)] (ϕ : C0 n) : C0 n :=
  divergence (d0 ϕ)

/-- The basis vector at index k (1 at k, 0 elsewhere) -/
def basis_vector {n : ℕ} (k : Fin n) : C0 n :=
  fun i => if i = k then 1 else 0

/-- Δϕ = lam·ϕ -/
def IsEigenvector {n : ℕ} [Fintype (Fin n)] (ϕ : C0 n) (lam : ℝ) : Prop :=
  ∀ i : Fin n, graph_laplacian ϕ i = lam * ϕ i

/-! ## Chains -/

/--
  A 1-chain is a formal integer linear combination of oriented edges.

  We represent this as an antisymmetric function Fin n → Fin n → ℤ,
  where c i j represents the coefficient of the oriented edge (i,j).

  For example, a path 0→1→2 is represented as:
  - c 0 1 = 1, c 1 2 = 1, all others = 0
-/
structure Chain1 (n : ℕ) where
  coeff : Fin n → Fin n → ℤ
  antisym : ∀ i j, coeff i j = -coeff j i

/-- The zero 1-chain (no edges) -/
def Chain1.zero (n : ℕ) : Chain1 n := {
  coeff := fun _ _ => 0
  antisym := by intro i j; ring
}

/-- Addition of 1-chains (formal sum) -/
def Chain1.add {n : ℕ} (c₁ c₂ : Chain1 n) : Chain1 n := {
  coeff := fun i j => c₁.coeff i j + c₂.coeff i j
  antisym := by intro i j; rw [c₁.antisym, c₂.antisym]; ring
}

/-- A 1-chain is a cycle if it has no boundary (each vertex has equal in-degree and out-degree) -/
def Chain1.IsCycle {n : ℕ} [Fintype (Fin n)] (c : Chain1 n) : Prop :=
  ∀ i : Fin n, ∑ j : Fin n, c.coeff i j = 0

/-- ⟨σ, c⟩ = (1/2) ∑ᵢⱼ σ(i,j) · c(i,j) -/
noncomputable def eval {n : ℕ} [Fintype (Fin n)] (σ : C1 n) (c : Chain1 n) : ℝ :=
  (1/2) * ∑ i : Fin n, ∑ j : Fin n, σ.val i j * (c.coeff i j : ℝ)

/-- Holonomy: evaluation of a 1-cochain on a 1-chain -/
noncomputable def holonomy {n : ℕ} [Fintype (Fin n)]
    (σ : C1 n) (c : Chain1 n) : ℝ :=
  eval σ c

/-! ## Quantum Cochains -/

/-- A quantum 0-cochain: complex-valued wavefunction on vertices -/
def QC0 (n : ℕ) := Fin n → ℂ

/-- A quantum 1-cochain: complex-valued skew-symmetric function on edges -/
structure QC1 (n : ℕ) where
  val : Fin n → Fin n → ℂ
  skew : ∀ i j, val i j = -val j i

/-- The quantum coboundary operator (gradient on ℂ) -/
def qd0 {n : ℕ} (ψ : QC0 n) : QC1 n := {
  val := fun i j => ψ j - ψ i
  skew := by intro i j; ring
}

/-- Hermitian inner product on quantum 0-cochains -/
noncomputable def inner_QC0 {n : ℕ} [Fintype (Fin n)] (ψ φ : QC0 n) : ℂ :=
  ∑ i : Fin n, star (ψ i) * φ i

/-- Hermitian inner product on quantum 1-cochains -/
noncomputable def inner_QC1 {n : ℕ} [Fintype (Fin n)] (σ τ : QC1 n) : ℂ :=
  (1/2) * ∑ i : Fin n, ∑ j : Fin n, star (σ.val i j) * τ.val i j

/-- Norm squared on QC0 (always real and non-negative) -/
noncomputable def norm_sq_QC0 {n : ℕ} [Fintype (Fin n)] (ψ : QC0 n) : ℝ :=
  (inner_QC0 ψ ψ).re

/-- Norm squared on QC1 -/
noncomputable def norm_sq_QC1 {n : ℕ} [Fintype (Fin n)] (σ : QC1 n) : ℝ :=
  (inner_QC1 σ σ).re

/-- The quantum divergence operator (adjoint of qd0) -/
noncomputable def qdivergence {n : ℕ} [Fintype (Fin n)] (σ : QC1 n) : QC0 n :=
  fun i => -∑ j : Fin n, σ.val i j

/-- The quantum graph Laplacian Δ = d* ∘ d -/
noncomputable def quantum_laplacian {n : ℕ} [Fintype (Fin n)] (ψ : QC0 n) : QC0 n :=
  qdivergence (qd0 ψ)

/--
Realized Capacity: The capacity on edges that are currently active.
-/
noncomputable def norm_sq_on_active {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (σ : C1 n) : ℝ :=
  (1/2) * ∑ i, ∑ j,
    if (i, j) ∈ G.active_edges then (σ.val i j)^2 else 0

/--
Latent Capacity: The capacity demand on edges that are currently broken.
-/
noncomputable def latent_capacity {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (σ : C1 n) : ℝ :=
  (1/2) * ∑ i, ∑ j,
    if (i, j) ∉ G.active_edges then (σ.val i j)^2 else 0

/--
Conservation of Representational Capacity.
The total capacity of the constraint σ is the sum of the 
Realized Capacity (on the graph) and the Latent Capacity (off the graph).
-/
theorem capacity_conservation {n : ℕ} [Fintype (Fin n)]
    (G : DynamicGraph n) (σ : C1 n) :
  norm_sq σ = (norm_sq_on_active G σ) + (latent_capacity G σ) := by
  rw [norm_sq, inner_product_C1, norm_sq_on_active, latent_capacity]
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  congr 1
  ext i
  rw [← Finset.sum_add_distrib]
  congr 1
  ext j
  by_cases h : (i, j) ∈ G.active_edges <;> simp [h, sq]

end Diaspora.Core
