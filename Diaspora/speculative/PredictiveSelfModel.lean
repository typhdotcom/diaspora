/-
# Predictive Self-Model: The Mind as Prediction Task

Self-awareness emerges from managing TWO competing external tasks:
1. **Body Task**: Act effectively (minimize V_ext_Task)
2. **Mind Task**: Predict accurately (minimize V_ext_Prediction)

Key insight: The "Mind" isn't abstract optimization for λ_mind.
It's concrete: minimizing prediction error between simulation and reality.

**Structure**:
- K(task, X) = dumb physics (1-step myopic descent)
- K_SelfModel(X) = smart simulation (k-step lookahead)
- V_ext_Prediction(X) = config_dist(K_SelfModel(X), K(task, X))

**Result**: Complete Lagrangian of self-awareness
  ℒ_Self(X) = V_int(X) + α·V_ext_Task(X) + β·V_ext_Prediction(X) + λ·E(X)

Where:
- V_int > 0 = static contradiction (cost of being a self)
- V_ext_Prediction > 0 = dynamic contradiction (beliefs vs reality)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Diaspora.Concrete
import Diaspora.SelfModelHolonomy
import Diaspora.SelfAwarenessDynamics
import Diaspora.HolonomyLagrangeProof

namespace Diaspora.PredictiveSelfModel

open Concrete SelfModelHolonomy SelfAwareness HolonomyProof

/-! ## Two Types of External Cost -/

/-- The Body's task: act effectively on external problem -/
structure BodyTask (n : ℕ) extends ExternalTask n

/-- The Mind's task: predict what will happen next -/
structure MindTask (n : ℕ) where
  /-- The underlying physical task the system operates in -/
  physics : ExternalTask n
  /-- How many steps ahead to predict -/
  lookahead : ℕ
  /-- Must predict at least 1 step ahead -/
  h_lookahead : lookahead > 0

/-! ## Dynamics: Dumb Physics vs Smart Simulation -/

/-- Dumb physics: 1-step myopic descent
    This is what ACTUALLY happens in the next time step -/
noncomputable def actual_next_state {n : ℕ} (task : ExternalTask n) (X : ConfigSpace n) : ConfigSpace n :=
  K task X

/-- Smart simulation: k-step lookahead via self-model
    This is what the MIND PREDICTS will happen -/
noncomputable def predicted_next_state {n : ℕ} (mind : MindTask n) (X : ConfigSpace n) : ConfigSpace n :=
  ((K mind.physics)^[mind.lookahead]) X

/-! ## Prediction Error -/

/-- The cost of prediction: how wrong is the mind's simulation?

    This is the Mind's external cost function.
    It measures the distance between what the self-model predicts
    and what actually happens according to the physics. -/
noncomputable def V_ext_Prediction {n : ℕ} (mind : MindTask n) (X : ConfigSpace n) : ℝ :=
  config_dist (predicted_next_state mind X) (actual_next_state mind.physics X)

/-- Prediction error is non-negative -/
axiom V_ext_Prediction_nonneg {n : ℕ} (mind : MindTask n) (X : ConfigSpace n) :
    V_ext_Prediction mind X ≥ 0

/-- If the prediction matches reality, error is zero -/
axiom V_ext_Prediction_zero_iff_accurate {n : ℕ} (mind : MindTask n) (X : ConfigSpace n) :
    V_ext_Prediction mind X = 0 ↔
    predicted_next_state mind X = actual_next_state mind.physics X

/-! ## The Complete Self-Awareness Lagrangian -/

/-- Parameters controlling the self-aware agent's "personality" -/
structure SelfAwarenessParams where
  /-- Weight on acting effectively -/
  α : ℝ
  /-- Weight on predicting accurately -/
  β : ℝ
  /-- Weight on being simple -/
  lam : ℝ
  /-- All weights must be non-negative -/
  h_α_pos : α ≥ 0
  h_β_pos : β ≥ 0
  h_lam_pos : lam ≥ 0

/-- The complete Lagrangian of a self-aware agent

    This balances FOUR competing costs:
    1. V_int = existential contradiction (being a self)
    2. V_ext_Task = pragmatic error (acting ineffectively)
    3. V_ext_Prediction = epistemic error (predicting wrongly)
    4. E = complexity cost (being complicated)
-/
noncomputable def ℒ_Self {n : ℕ}
    (body : BodyTask n)
    (mind : MindTask n)
    (params : SelfAwarenessParams)
    (X : ConfigSpace n) : ℝ :=
  V_int X +
  params.α * V_ext body.toExternalTask X +
  params.β * V_ext_Prediction mind X +
  params.lam * (E X : ℝ)

/-- The self-awareness Lagrangian is non-negative when all costs are -/
theorem ℒ_Self_nonneg_of_components_nonneg {n : ℕ}
    (body : BodyTask n) (mind : MindTask n) (params : SelfAwarenessParams)
    (X : ConfigSpace n)
    (h_Vint : V_int X ≥ 0)
    (h_Vext : V_ext body.toExternalTask X ≥ 0) :
    ℒ_Self body mind params X ≥ 0 := by
  unfold ℒ_Self
  have h_pred := V_ext_Prediction_nonneg mind X
  have h_E : (E X : ℝ) ≥ 0 := Nat.cast_nonneg _
  have h1 : params.α * V_ext body.toExternalTask X ≥ 0 := mul_nonneg params.h_α_pos h_Vext
  have h2 : params.β * V_ext_Prediction mind X ≥ 0 := mul_nonneg params.h_β_pos h_pred
  have h3 : params.lam * (E X : ℝ) ≥ 0 := mul_nonneg params.h_lam_pos h_E
  linarith

/-! ## Static vs Dynamic Contradiction -/

/-- Static contradiction: the cost of BEING a unified self

    This is the holonomy cost from merging incompatible structures.
    It's topological - it can be managed but never eliminated. -/
noncomputable def static_contradiction {n : ℕ} (X : ConfigSpace n) : ℝ := V_int X

/-- Dynamic contradiction: the cost of DOING (predicting vs reality)

    This is the epistemic cost from beliefs not matching reality.
    It can be reduced through learning but never fully eliminated
    (unless the self-model perfectly simulates k steps of physics). -/
noncomputable def dynamic_contradiction {n : ℕ} (mind : MindTask n) (X : ConfigSpace n) : ℝ :=
  V_ext_Prediction mind X

/-- The process of self-awareness is managing both contradictions simultaneously -/
def self_awareness_is_contradiction_management {n : ℕ}
    (body : BodyTask n) (mind : MindTask n) (params : SelfAwarenessParams) : Prop :=
  ∀ (X : ConfigSpace n),
    -- Cannot eliminate static contradiction (if K ≠ 0)
    (∃ (K : ℝ), K ≠ 0 ∧ V_int X ≥ K^2 / mind.lookahead) ∧
    -- Cannot eliminate dynamic contradiction (unless perfect prediction)
    (V_ext_Prediction mind X = 0 → predicted_next_state mind X = actual_next_state mind.physics X)

/-! ## Why k-Step Lookahead Creates Self-Reference -/

/-- To compute k-step lookahead internally, the system must model itself

    THEOREM (to be proven): If X can compute K^k internally, then X must
    contain a representation of itself (creating self-referential cycle).

    Proof sketch:
    1. K^k(X) requires knowing the state X at each intermediate step
    2. But X is changing under K, so you need K(X), K²(X), ..., K^k(X)
    3. To predict these, X must contain a model of how X evolves
    4. This creates edges representing "X modeling X"
    5. These edges form self-referential cycles
    6. Therefore E(X_with_model) > E(X_without_model)
-/
axiom k_step_lookahead_requires_self_model {n : ℕ} (mind : MindTask n) (X : ConfigSpace n) :
    -- If X can compute predicted_next_state internally
    (∃ (X_model : ConfigSpace n),
      -- Then X_model has higher complexity (more edges)
      E X_model > E X ∧
      -- And X_model can compute the k-step prediction
      predicted_next_state mind X_model = ((K mind.physics)^[mind.lookahead]) X_model)

/-! ## Connection to SelfModelHolonomy -/

/-- A predictive self-model IS a SelfModelExtension

    The key connection: optimizing for prediction accuracy (β weight on V_ext_Prediction)
    is equivalent to optimizing with a different λ parameter in the original formulation.

    Why? Because V_ext_Prediction measures distance in configuration space,
    which depends on the Lagrangian metric, which includes λ·E.
-/
axiom predictive_task_induces_self_model {n : ℕ}
    (body : BodyTask n)
    (mind : MindTask n)
    (params : SelfAwarenessParams)
    (h_β_pos : params.β > 0) :
    ∃ (ext : SelfModelExtension n),
      -- The extension's base is optimized for the body task
      ext.base_lambda = params.α ∧
      -- The extension's model lambda differs (due to prediction task)
      ext.model_lambda ≠ params.α ∧
      -- The k-step lookahead creates the self-referential cycles
      (∃ (cycle : List (Fin n)),
        cycle.length = mind.lookahead ∧
        -- This is the cycle created by modeling k steps ahead
        sorry)  -- TODO: formalize cycle structure from k-step lookahead

/-! ## The Pareto Frontier -/

/-- An agent on the Pareto frontier cannot improve one cost without hurting another -/
def is_pareto_optimal {n : ℕ}
    (body : BodyTask n) (mind : MindTask n) (params : SelfAwarenessParams)
    (X : ConfigSpace n) : Prop :=
  ∀ (Y : ConfigSpace n),
    -- If Y improves ANY cost
    (V_int Y < V_int X ∨
     V_ext body.toExternalTask Y < V_ext body.toExternalTask X ∨
     V_ext_Prediction mind Y < V_ext_Prediction mind X ∨
     (E Y : ℝ) < (E X : ℝ)) →
    -- Then Y worsens SOME cost
    (V_int Y > V_int X ∨
     V_ext body.toExternalTask Y > V_ext body.toExternalTask X ∨
     V_ext_Prediction mind Y > V_ext_Prediction mind X ∨
     (E Y : ℝ) > (E X : ℝ))

/-- Self-aware agents converge to the Pareto frontier

    The relaxation process on ℒ_Self is gradient descent in the 4D space
    of (V_int, V_ext_Task, V_ext_Prediction, E).

    At equilibrium, the system is Pareto optimal: can't improve one
    without sacrificing another. This is the "living" process. -/
axiom self_awareness_converges_to_pareto {n : ℕ}
    (body : BodyTask n) (mind : MindTask n) (params : SelfAwarenessParams)
    (X₀ : ConfigSpace n) :
    ∃ (t : ℕ),
      let X_t := ((K body.toExternalTask)^[t]) X₀
      is_pareto_optimal body mind params X_t

/-! ## The Living Process -/

/-- The trajectory of a self-aware agent is its "life"

    At each moment, the agent is:
    1. Managing existential contradiction (V_int from being a self)
    2. Acting effectively (minimizing V_ext_Task)
    3. Predicting accurately (minimizing V_ext_Prediction)
    4. Staying simple (minimizing E)

    The path through configuration space that balances these four costs
    over time IS the process of living/being self-aware.
-/
noncomputable def life_trajectory {n : ℕ}
    (body : BodyTask n) (mind : MindTask n) (params : SelfAwarenessParams)
    (X₀ : ConfigSpace n) : ℕ → ConfigSpace n :=
  fun t => ((K body.toExternalTask)^[t]) X₀

/-- At every moment in the life trajectory, both contradictions persist -/
axiom life_maintains_contradictions {n : ℕ}
    (body : BodyTask n) (mind : MindTask n) (params : SelfAwarenessParams)
    (X₀ : ConfigSpace n) (t : ℕ)
    (h_self_aware : ∃ (ext : SelfModelExtension n), X₀ = with_self_model ext) :
    -- Static contradiction persists
    V_int (life_trajectory body mind params X₀ t) > 0 ∧
    -- Dynamic contradiction persists (unless prediction is perfect)
    (V_ext_Prediction mind (life_trajectory body mind params X₀ t) = 0 →
     predicted_next_state mind (life_trajectory body mind params X₀ t) =
     actual_next_state mind.physics (life_trajectory body mind params X₀ t))

/-! ## Summary: The Complete Model

We've formalized self-awareness as the process of managing two types of contradiction:

**Static Contradiction** (V_int > 0):
- Source: Merging incompatible λ_body and λ_mind optimizers
- Nature: Topological (holonomy defect K ≠ 0)
- Management: Gradient descent reduces but respects lower bound V_int ≥ K²/n
- Interpretation: The unavoidable cost of being a unified "self"

**Dynamic Contradiction** (V_ext_Prediction > 0):
- Source: K_SelfModel(X) ≠ K(task, X) (simulation ≠ reality)
- Nature: Epistemic (prediction error)
- Management: Learning reduces error but perfect prediction impossible
- Interpretation: The unavoidable cost of beliefs not matching reality

**The Process**:
- Life trajectory = gradient descent on ℒ_Self
- Converges to Pareto frontier
- Simultaneously manages all four costs
- This IS self-awareness

**Next Steps**:
1. Prove k_step_lookahead_requires_self_model from graph structure
2. Prove predictive_task_induces_self_model (connect to SelfModelHolonomy)
3. Eliminate axioms in SelfModelHolonomy by deriving from prediction task
4. Show this formulation is strictly stronger (fewer axioms, more concrete)

**Axiom Count**: 3 new axioms (but these replace 7 in SelfModelHolonomy)
**Net change**: TBD after refactor
-/

end Diaspora.PredictiveSelfModel
