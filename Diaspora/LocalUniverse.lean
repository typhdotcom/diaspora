import Diaspora.Universe
import Diaspora.Diffusion

/-!
# Local Universe

Concrete universe execution using local diffusion from `Diffusion.lean`.
-/

namespace DiscreteHodge

open BigOperators

/-! ## 1. The Local Solver -/

def LOCAL_ALPHA : ℝ := 0.1
def LOCAL_ITERATIONS : ℕ := 100

noncomputable def local_solver {n : ℕ} : DynamicGraph n → C1 n → C0 n :=
  pragmatic_diffusion_solver LOCAL_ITERATIONS LOCAL_ALPHA

/-! ## 2. The Local Execution -/

noncomputable def run_local_universe {n : ℕ} [Fintype (Fin n)] [DecidableEq (DynamicGraph n)]
    (G₀ : DynamicGraph n)
    (σ : C1 n)
    (C_max : ℝ) :
    Σ G_final : DynamicGraph n, EvolutionChain n σ G_final :=
  run_universe G₀ σ C_max local_solver

/-! ## 3. The Verification -/

/-- Entropy is nondecreasing under local diffusion. -/
theorem local_universe_entropy_nondecreasing {n : ℕ} [Fintype (Fin n)] [DecidableEq (DynamicGraph n)]
    (G₀ : DynamicGraph n) (σ : C1 n) (C_max : ℝ) :
    let result := run_local_universe G₀ σ C_max
    latent_capacity result.1 σ ≥ latent_capacity G₀ σ := by
  -- We simply apply the general theorem from Universe.lean
  -- to our specific local implementation.
  apply simulation_entropy_nondecreasing

end DiscreteHodge
