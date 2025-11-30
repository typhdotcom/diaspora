<p align="center">
  <img src="img/logo.png" alt="Diaspora" height="100" />
</p>

# Diaspora

*A toy universe of topology*

Diaspora is a Lean 4 project that builds a discrete Hodge-theoretic toy model on finite graphs. It's an amateur effort, with LLM help, built solely to explore philosophical intuitions through topology.

* **Graphs** whose edges can break under strain
* **Diffusion** as the local mechanism for relaxation (Heat Equation)
* **Holonomy** as the local mechanism for measurement (Parallel Transport)
* **Constraints** living as 1-cochains (flux / tension)
* **Potentials** as 0-cochains (relaxation fields)
* **Harmonic forms** as the “irreducible frustration” left over when you’ve relaxed everything you can
* **Topology change** when edges snap
* **Plasticity** where edges strengthen under strain and atrophy from disuse (Hebbian learning + scarcity)
* A “**glassy**” landscape with multiple non-isomorphic stable vacua
* Quantum add-ons: discrete Schrödinger evolution, Berry phase, and holonomy-as-measurement
* **Spectral gap**: topological defects require minimum energy 1/n
* **Phase fields**: discrete calculus over cyclic groups (ZMod k)

Everything here is proved inside Lean + mathlib. The physics (`black hole`, `handshake`, `false vacuum`, `observer`, etc.) are metaphors layered on top of finite-dimensional linear algebra and graph theory.

---

## Big picture

At the core is a simple idea:

> Take a finite graph. Put a “desired flux” on each edge (a 1-cochain).
> Let the vertices carry a “relaxation potential” (a 0-cochain).
> Try to relax away as much strain as possible. Whatever you *cannot* relax
> is topological and shows up as a harmonic form.

This is formalized in two layers:

1. **The Mathematical Ideal (Global):**
   In `Hodge/Decomposition.lean`, we use global linear algebra to prove that a perfect potential `ϕ` exists and compute **Betti numbers** via the dimension formula
   `dim(H) + |V| = |E| + dim(Ker d)`.
   For a connected graph this recovers the usual cyclomatic number: `dim(H) = |E| - |V| + 1`.

2. **The Physical Mechanism (Local):**
   In `Dynamics/Diffusion.lean`, we show that the system doesn't *need* a global solver to find this state. Nodes simply push against their neighbors (Heat Equation) to minimize local strain. Observers measure topology locally via **Holonomy** (walking in loops).

Then we prove (for the complete graph) a discrete **Hodge decomposition**:

> Every 1-cochain `σ` splits as
> `σ = d0 ϕ + γ`
> where `d0 ϕ` is exact and `γ` is divergence-free (harmonic), and the two parts are orthogonal.

That’s standard math, but we make it formal in Lean and then build a whole story-universe out of the consequences.

A key quantitative result: **topological defects have a mass gap**. If γ has non-trivial winding around an n-cycle, then ‖γ‖² ≥ 1/n. This minimum energy is the "nucleation barrier" - you can't have a little bit of topology. Once your Betti number is non-zero, every nontrivial cycle carries a **discrete, quantized** minimum cost in the energy landscape.

---

## Under the hood: representational density

One way to read all of this is: the primitive object isn’t really the graph, it’s the
**representational demand** living on would-be edges.

* A 1-cochain `σ : C1 n` is "how much relation" each ordered pair of vertices wants to carry.
* The inner product / norm on 1-cochains is the total "capacity" of that demand.
* A `DynamicGraph G` just says which of those edges are currently allowed to exist.

Given `G` and `σ`, you can split the capacity into:

* realized capacity on active edges, and
* latent capacity on edges that are currently broken.

In parallel, `PhaseField.lean` repeats this story for **phase-valued** constraints in `ZMod k`, with geodesic distance on the phase circle playing the role of strain.

This is formalized in `WeightedGraph` via `total_capacity_fixed`, forcing a zero-sum competition for existence: edges must "pay rent" (carry strain) to survive renormalization.

---

## Project Structure

The codebase is organized into six layers:

```text
Diaspora/
├── Core/           # Foundations: calculus, phase fields, weighted graphs
├── Hodge/          # Static theory: decomposition, harmonic analysis, spectral gap
├── Logic/          # Bridge: formal logic ↔ topology (satisfiability as exactness)
├── Dynamics/       # Time evolution: diffusion, plasticity, topology change
├── Quantum/        # Complex extensions: Schrödinger, Berry phase, measurement
└── Models/         # Concrete examples and named stories
```

---

## Discrete calculus on graphs

### `Diaspora/Core/Calculus.lean`

Foundations:

* `DynamicGraph n`: graph with `n` fixed vertices and a *dynamic* set of active edges.
* 0- and 1-cochains:

  * `C0 n := Fin n → ℝ`
  * `C1 n`: skew-symmetric `Fin n → Fin n → ℝ`
* Classical coboundary / gradient:

  * `d0 : C0 n → C1 n`
* Inner product and norm on 1-cochains:

  * `inner_product_C1`, `norm_sq`
* **Active forms**:

  * `ActiveForm G`: 1-cochains that vanish on broken edges of a `DynamicGraph G`.
  * Equipped with an inner product, norm, and turned into an `InnerProductSpace`.

Graph-aware operators:

* `d_G : C0 n → ActiveForm G` - gradient respecting which edges exist.
* `δ_G : ActiveForm G → C0 n` - divergence.
* `Δ_G := δ_G ∘ d_G` - graph Laplacian.
* `IsHarmonic σ` - divergence-free 1-cochains.

Quantum flavor:

* `QC0 n`, `QC1 n` - complex analogues.
* Hermitian inner products `inner_QC0`, `inner_QC1`.
* `quantum_laplacian` and `IsEnergyEigenstate`.

### `Diaspora/Models/Duality.lean`

A small companion file:

* Defines a discrete Hodge-star–style operation on complete graphs.
* Proves basic duality lemmas that make the harmonic / energy statements cleaner.
* You can safely skip it on a first pass; it’s part of the underlying toolkit rather than a story file.

---

## Hodge decomposition (the heavy lifting)

### `Diaspora/Hodge/Decomposition.lean`

The core decomposition theorem with explicit algebraic topology.

Structure:

1. **Geometry of Active Forms** - inner product space on `ActiveForm G`
2. **Gradient Subspace** - `ImGradient G` (exact forms)
3. **Harmonic Subspace** - `HarmonicSubspace G := (ImGradient G)ᗮ`
4. **Decomposition Theorem** - `σ = d_G φ + γ` with `γ ⟂ ImGradient`
5. **Algebraic Topology (Betti Numbers)** - dimension formulas

Key results:

* `active_form_dimension`: dim(ActiveForm G) = |E| (undirected edge count)
* `harmonic_dimension_eq_cyclomatic`: `dim(H) + |V| = |E| + dim(Ker d)`

  * This is the "Algebraic Bridge" connecting linear algebra to graph topology.
  * For connected graphs: `dim(H) = |E| - |V| + 1` (cyclomatic number).

Specialization to the **complete graph** transfers everything to plain `C1 n`.

Main theorem:

```lean
theorem hodge_decomposition {n : ℕ} [Fintype (Fin n)] (σ : C1 n) :
  ∃ (ϕ : C0 n) (γ : C1 n),
    (∀ i j, σ.val i j = (d0 ϕ).val i j + γ.val i j) ∧
    IsHarmonic γ ∧
    inner_product_C1 (d0 ϕ) γ = 0
```

---

## Harmonic analysis and physical interpretations

### `Diaspora/Hodge/Harmonic.lean`

Once we have Hodge, we get a bunch of physical-sounding theorems:

* Energy as cohomological distance:

  * `V_int_is_cohomological_distance`
    expresses `‖d0 ϕ - σ‖²` explicitly as a sum over edges.

* Minimal energy achieved when you project onto exact forms:

  * `minimum_V_int_is_harmonic_norm`

* Linearity properties:

  * `harmonic_projection_is_linear`
  * `inheritance_is_linearity`

* “Pythagorean theorem” for cochains:

  * `‖σ‖² = ‖exact part‖² + ‖harmonic part‖²`

Stokes / holonomy:

* Chains `Chain1 n` represent directed cycles.
* `eval` / `holonomy`: pairings of cochains with chains.
* **Stokes theorem in this discrete setting**:

  * Exact forms vanish on cycles.
  * Holonomy of `σ` on a cycle depends only on its harmonic component.

Simple cycles & quantization:

* `SimpleCycle` structure encodes a simple loop.
* Harmonic forms supported on such a cycle are **constant along the loop**.
* Get **topological quantization** statements:

  * Winding number `m` implies energy levels like `m² / n`.
  * The fully sharpened “no small topology” and mass-gap bounds live in `Spectral.lean`.

Quantum:

* `quantum_laplacian_hermitian` - the discrete Laplacian is self-adjoint.
* `constant_is_zero_energy` - constant phases are zero-energy eigenstates.
* `quantum_exact_vanishes_on_cycles` - quantum version of Stokes.

---

## Spectral gap and quantization

### `Diaspora/Hodge/Spectral.lean`

Non-trivial topology implies a minimum energy cost.

* `HasNontrivialCohomology` - harmonic form with non-zero holonomy on some cycle.
* `spectral_gap_qualitative`: Non-trivial cohomology ⟹ ‖γ‖² > 0.
* `spectral_gap_quantitative`: For cycle-supported harmonic with winding m ≠ 0, **‖γ‖² ≥ 1/n**.
* `soliton_lower_bound`: Combines exact formula ‖γ‖² = m²/n with the lower bound.

Interpretation: topological defects have quantized energy levels with a **mass gap**. The `Twist` module then shows this lower bound is sharp by constructing a canonical winding-1 defect with energy exactly `1/n`.

### `Diaspora/Hodge/Twist.lean`

Canonical construction of harmonic forms with specified winding.

* `dehn_twist cycle`: Creates harmonic form with value 1/n on each forward edge.
* `dehn_twist_is_harmonic`: Divergence-free for n ≥ 3.
* `dehn_twist_winding_one`: Total winding around cycle = 1.
* `dehn_twist_energy`: **‖dehn_twist‖² = 1/n** (minimum non-zero energy).
* `dehn_twist_is_canonical`: Any harmonic form with winding 1 equals the Dehn twist.

---

## Phase fields and cyclic constraints

### `Diaspora/Core/Phase.lean`

Discrete calculus over finite cyclic groups (ZMod k).

* `PC0 n k`, `PC1 n k` - phase 0- and 1-cochains valued in `ZMod k`.
* `pd0` - phase coboundary operator.
* `geodesic_dist` - shortest path distance on the cycle `ZMod k`.
* `phase_winding_simple` - winding of a phase 1-cochain on a simple cycle.
* `phase_exact_vanishes_on_simple_cycles` - **Phase Stokes theorem**.
* `winding_number_is_topological_invariant` - adding an exact form preserves winding.

Interpretation: in phase fields, winding is enforced by the type system - you can't partially wind.

---

## Logic: constraints, paradox, and topology

The `Logic` layer rephrases everything in terms of **finite theories of constraints** and their satisfiability. Exact cochains become models; harmonic content becomes paradox that can’t be resolved away.

Roughly, the logic files walk through:

1. **Local theories ↔ exact cochains** (`Basic`, `Genesis`, `Omega`)
2. **Classicality and acyclicity** (`Foundations`)
3. **Matter as fossilized contradiction** (`Inverse`)
4. **How generic topology is** (`Probabilistic`, `Limit`)
5. **Universal cover and resolution of paradox** (`Universal`)

### `Diaspora/Logic/Basic.lean`

The bridge between formal logic and topology.

A `Theory` is a list of constraints, each demanding `ϕ(dst) - ϕ(src) = val`. A theory is `Satisfiable` if some potential ϕ satisfies all constraints. This is exactly the question of whether a 1-cochain is exact.

* `Constraint n`: a single demand `ϕ(dst) - ϕ(src) = val`
* `Theory n`: a list of constraints
* `Satisfiable T`: existence of a model (potential) satisfying all constraints
* `LocallyConsistent T`: no direct contradictions (same edge, different values)
* `theory_graph T`: the graph implied by a theory's constraints
* `realize T`: converts a theory into a 1-cochain (the representational demand)

**The Bridge Theorem:**

```lean
theorem satisfiable_iff_exact_on_graph (T : Theory n) (h_cons : LocallyConsistent T) :
  Satisfiable T ↔ (realize T) ∈ ImGradient (theory_graph T)
```

Satisfiability is exactness. Logical consistency is trivial cohomology.

**Corollary:** `inconsistency_implies_topology` - if a locally consistent theory is unsatisfiable, then its harmonic subspace is non-trivial. The logical contradiction has become geometric structure.

### `Diaspora/Logic/Omega.lean`

Chaitin's Ω reframed: the probability that a random constraint program "halts" (is satisfiable).

* `DiscreteVal`: constraints take values in {-1, +1}.
* `Program n`: a list of atomic constraints.
* `Halts P`: 1 if satisfiable, 0 otherwise.
* `Chaitins_Omega_Diaspora`: sum over all program lengths of halting probability.

The complementary quantity `1 - Ω` is the probability of **genesis**: randomly sampling constraint programs and landing in the non-exact sector.

* `genesis_requires_topology`: if a locally consistent program doesn't halt, harmonic content exists.

### `Diaspora/Logic/Genesis.lean`

The simplest unsatisfiable program: three constraints demanding +1 around a triangle.

* `rotational_program`: 0→1 (+1), 1→2 (+1), 2→0 (+1).
* `genesis_is_unsatisfiable`: Kirchhoff says 0 = 3, contradiction.
* `genesis_is_consistent`: no local contradictions.
* `structure_is_mandatory`: therefore harmonic content must exist.

This is the "Escher staircase" - locally coherent, globally impossible. The impossibility isn’t a bug; it’s the birth of topology.

### `Diaspora/Logic/Foundations.lean`

The connection between **set-theoretic well-foundedness** and **topological acyclicity**.

* `IsClassical G`: `dim(HarmonicSubspace G) = 0` - no harmonic modes, tree-like universe.
* `IsMember G ϕ child parent`: membership defined by gradient flow (parent at higher potential).
* `IsFaithfulPotential G ϕ`: the potential orients every edge (no ties).
* `GeneralCycle`: a cycle on k ≤ n distinct vertices within `Fin n`.

Key results:

* `matter_is_paradox`: A cycle on n vertices creates harmonic energy exactly 1/n.
* `russell_loop_creates_mass`: Embedded cycle ⟹ `finrank(H) ≥ 1`.
* `cycle_implies_nonclassical`: Cycles contradict classicality.
* `classical_implies_acyclic`: `dim(H) = 0` ⟹ the graph is acyclic.
* `classical_universe_admits_intrinsic_hierarchy`: Classical + connected ⟹ canonical height function gives well-founded membership.
* `classical_universe_admits_no_paradoxes`: In a classical universe, every ActiveForm is exact.

Interpretation: ZFC-style classical set theory plays the role of a vacuum. A classical universe admits well-founded membership hierarchies with no Russell-like paradoxes. Closing a loop is exactly the move that leaves this classical phase.

### `Diaspora/Logic/Inverse.lean`

The reverse direction: **topology → logic**. Every particle is a fossil of contradiction.

* `fossilize G σ`: Convert a physical 1-cochain into a constraint theory.

Key results:

* `fossil_is_consistent`: Fossilized theories are always locally consistent.
* `matter_is_fossilized_logic`: The realized theory matches the harmonic form on active edges.
* `harmonic_yields_unsatisfiable`: Non-zero harmonic ⟹ the fossil is unsatisfiable.
* `particle_is_paradox`: Every nonzero "particle" (harmonic form) corresponds to a locally consistent but globally unsatisfiable theory.

Read backwards, the theorems say that nonzero harmonic content always comes from an unsatisfiable but locally consistent theory. In Diaspora, mass is frozen logical contradiction: harmonic forms are **fossils** of impossible demands, and you can read the paradox back out of the geometry.

### `Diaspora/Logic/Probabilistic.lean`

How "generic" is topology in the space of all constraints?

* `dimensional_gap`: `dim(ActiveForm) − dim(ImGradient) = dim(HarmonicSubspace)`.
* `RobustlySatisfiable T`: the theory survives arbitrary single-constraint perturbation.

Key results:

* `genesis_is_generic`: Non-trivial topology ⟹ satisfiable constraints form a proper subspace.
* `void_is_fragile`: If a satisfiable theory has cycles (non-zero harmonic subspace), it is **not robustly satisfiable** - any perturbation breaks it.

Interpretation: the "void" (satisfiable vacuum) sits on a knife-edge in constraint space. Satisfiable theories live in a proper subspace, so generic noise pushes you into the non-exact sector, where harmonic content - and therefore mass - shows up almost automatically.

### `Diaspora/Logic/Limit.lean`

What happens as the universe grows?

* `bettiOne G`: first Betti number (cyclomatic complexity).
* `IsComplex G`: `bettiOne > 0` - the universe has cycles.
* `UniverseSequence`: a growing family of graphs indexed by ℕ.
* `HasAdditiveGrowth`: `|E| − n → ∞` (edges outpace vertices).
* `HasMultiplicativeGrowth`: `|E|/n → ∞` (edge density explodes).
* `classicalRatio G`: `dim(ImGradient) / dim(ActiveForm)` - the "probability" of landing in the exact sector.

Key results:

* `complexity_threshold`: `|E| ≥ n` + connected ⟹ `IsComplex`.
* `eventual_genesis`: Additive superlinear growth ⟹ eventually complex.
* `inevitable_genesis`: Multiplicative growth ⟹ `classicalRatio → 0` as `n → ∞`.

This is Diaspora’s **big bang**: as the universe grows under these connectivity assumptions, genesis becomes inevitable. The probability of staying in the classical (exact) sector goes to zero. Structure isn’t an accident here - it’s a statistical consequence of growth.

### `Diaspora/Logic/Universal.lean`

The **universal cover** of a graph and the resolution of paradox.

* `History G root`: A walk from root to current vertex - your "history" of how you arrived.
* `UniversalCover G root`: SimpleGraph on histories; two histories are adjacent if one extends the other by one step.
* `lift_form G σ root`: Lift a constraint field to the cover.
* `history_potential G σ root h`: Potential = cumulative strain along your history.

Key results:

* `universal_cover_is_classical`: The universal cover is **acyclic** (a tree).
* `paradox_dissolves_in_cover`: Every constraint field becomes exact when lifted to the cover.

Interpretation: the universal cover is a kind of **God’s-eye view** - reality unrolled into a tree, with no loops and no paradox. Distinct histories never collide upstairs, so every constraint field lifts to an exact form. When you project back down, different histories can land on the same edge; their "memory mismatch" is what shows up as energy. Diaspora treats ZFC-style foundations as something like a universal cover: a classical tree of sets that we mistake for the messy, cyclic, finite web of relations underneath.

---

## Mechanisms of relaxation & measurement

### `Diaspora/Dynamics/Diffusion.lean`

A local alternative to the global solver.

* `diffusion_step`: Discrete heat equation. Nodes adjust their potential based only on immediate neighbor strain.
* **Theorem:** `stationary_diffusion_is_optimal` - if every node is locally balanced, the global system has reached the Hodge energy minimum.
* `phase_synchronization_step`: **Kuramoto-style dynamics** for phase fields using geodesic distance.

Together they say: scalar potentials relax toward the Hodge optimum, while phase fields synchronize along geodesics on `ZMod k` without ever breaking their winding constraints.

### `Diaspora/Quantum/Witness.lean`

A local alternative to global energy summation.

* `measure_loop_distortion`: An observer walking a cycle tracks their internal phase shift.
* **Theorem:** `local_holonomy_predicts_global_energy` - the phase shift detected by a local walker predicts the total energy of the topological defect.

### `Diaspora/Dynamics/Local.lean`

* Runs the `Sim` simulation using `diffusion` as the solver, proving that local rules are sufficient to drive the global topology change.

---

## Topology, strain, and graph evolution

### `Diaspora/Dynamics/Strain.lean`

### `Diaspora/Dynamics/Transition.lean`

These files turn the math into a dynamics:

* Define **edge strain**:

  * `edge_strain ϕ σ i j := ((d0 ϕ).val i j - σ.val i j)²`

* Show **strain must localize** if total frustration is high:

  * `strain_must_localize`: a pigeonhole principle on edges.

* `BreakingThreshold` and `C_max`: when strain exceeds this, an edge “breaks”.

Graph metrics:

* `edge_count`
* `cyclomatic_number` - counts cycles (for connected graphs).

Edge removal and evolution:

* `remove_edge` - deletes an undirected edge (both orientations).
* `find_overstressed_edge` - pick an active edge with highest strain above threshold.
* `evolve_step` - perform one "break" if needed.

Dynamic energy:

* `dynamic_strain_energy G ϕ σ` - strain summed only over active edges.
* `energy_drop_on_break` - breaking an edge reduces this energy by exactly that edge’s strain.
* `is_equilibrium` - no edge exceeds `C_max`; `equilibrium_is_stable` shows that in this case `evolve_step` is a no-op.

Nucleation barrier:

* `nucleation_barrier n := 1/n` - minimum energy to sustain a topological defect.
* `vacuum_stability`: If ‖γ‖² < 1/n, then winding m = 0 (trapped in exact sector).
* `nucleation_necessity`: If m ≠ 0, then ‖γ‖² ≥ 1/n (energy had to exceed barrier).

So the universe can only “grow” genuine topological defects by first pushing enough strain through the graph to cross this barrier; below `1/n` you’re trapped in the exact (topologically trivial) sector.

There’s a simple entropy-like quantity hiding here: the **latent capacity** of `σ`
with respect to `G` (how much strain lives on broken edges). Along any valid
evolution chain, latent capacity is non-decreasing; breaking an edge moves some
capacity from "realized" to "latent" and never back. That gives a bare-bones
arrow of time: a partial order on graphs where history is exactly which edges
paid the price for the frustration.

### Universe evolution (the main loop)

#### `Diaspora/Dynamics/Sim.lean`

This is the abstract proof-carrying simulation engine:

* `EvolutionChain n σ G` - inductive type of valid histories, step-by-step edge breaks.
* `evolve` - given a **Solver** (either the Global Ideal or the Local Diffusion), it resolves potentials and breaks the most overstressed edge.
* `run_universe` - start from an initial graph `G₀` and run `evolve`.

Main structural statement:

* `simulation_entropy_nondecreasing` - latent capacity with respect to `σ`
  never decreases along this simulation. Once capacity has moved to broken edges,
  it doesn’t come back; the “time” of the universe is literally the accumulation
  of irreversibly latent strain.

(See `Dynamics/Local.lean` for the concrete implementation where the "Solver" is just local heat diffusion.)

“Black hole” metaphor (in the topology-change layer):

* `black_hole_formation` packages:

  1. Some edge must break under high frustration.
  2. A harmonic form with positive norm appears.
  3. External observers measuring holonomy “see only γ” (no-hair analogue).

---

## Weighted graphs and plasticity

### `Diaspora/Core/Weighted.lean`

### `Diaspora/Dynamics/Plasticity.lean`

This layer moves from binary topology (active/inactive) to continuous capacity. It treats the graph as an economic system with finite resources.

Foundations:

* `WeightedGraph n`: edges have continuous weights `w_ij ≥ 0`.
* **Conservation of attention**: the total capacity of the universe is fixed at `n²`.

  * `∑ w_ij = n²`
* `raw_strain`: the pure potential difference `(d0 ϕ - σ)²`, unmitigated by capacity.
* `phase_strain`: geodesic-aware strain for cyclic phase fields (respects `ZMod k` topology).
* `to_dynamic`: thresholding a weighted graph converts it back to a `DynamicGraph` (emergent topology).

The plasticity cycle: evolution happens in a loop of Growth, Scarcity, and Pruning (`plasticity_cycle`):

1. **Hebbian phase**: edges under high strain grow stronger (`w' = w + η·strain`).
2. **Scarcity phase**: the graph is renormalized to enforce the conservation of attention. If some edges grow, others must shrink.
3. **Pruning**: weights falling below `ε` are zeroed out.

Key theorem: "use it or lose it".

* `plasticity_atrophy_of_unstressed`: if the system is under stress, any edge with *zero* local strain will strictly decrease in weight (it is "taxed" to pay for the growth of stressed edges).

Dehn twists as attractors:

* `dehn_twist_preserves_symmetry`: uniform weights + Dehn twist strain → weights stay uniform.
* `dehn_twist_guarantees_existence`: positive learning rate ensures cycle edges remain active.

### `Diaspora/Models/Resilience.lean`

The converse question: what about edges *with* strain? This file proves that harmonic content is self-maintaining under plasticity.

* At the optimal potential (from Hodge decomposition), `raw_strain = γ²` - strain equals the harmonic component squared.
* Cycle edges with non-zero winding have `γ ≠ 0`, therefore positive strain.
* Positive strain means Hebbian reinforcement, not atrophy.

Main theorems:

* `harmonic_cycle_resists_atrophy`: cycle edges with harmonic content have positive strain.
* `zombie_stays_dead`: exact σ (no harmonic content) → dead edges stay dead. No "ghost strain" to resurrect them.
* `harmonic_resurrects`: harmonic σ → dead cycle edges get pulled back toward positive weight.
* `ghost_manifests` / `ghost_trapped`: whether a resurrecting edge survives pruning depends on whether `η * γ² ≥ ε`.

Interpretation: harmonic content protects the topology that carries it. Self-reference, once established, is stable - the irreducible frustration creates the strain that pays the rent. Dehn twists are the cleanest example: they sit right at the nucleation barrier `1/n`, but Hebbian plasticity still treats them as **tax-paying residents**, not ghosts to be pruned.

---

## Toy systems and named stories

These are the narrative / physics-inspired models built on top.

### The void: observation vs reality

#### `Diaspora/Models/Void.lean`

Formalizes the distinction between full state and observable state, plus dimensional analysis.

Micro/macro framework:

* `Microstate n`: weighted graph + constraint field σ + potential φ.
* `Macrostate n`: thresholded topology + visible fields + Laplacian spectrum.
* `observe`: projects microstate to macrostate via threshold ε.
* `evolve_micro`: evolves microstate via plasticity (uses full σ, including sub-threshold).
* `graphSpectrum`: eigenvalues of the graph Laplacian.

Dimensional analysis:

* `IsVoidTopology G`: `dim(HarmonicSubspace G) = 0` (tree/forest topology).
* `AllowsGenesis G`: `dim(HarmonicSubspace G) > 0` (supports topological defects).
* `void_implies_exactness`: in a tree, every constraint is exact - no frustration possible.
* `structure_is_generic`: if `dim(H) > 0`, then `dim(Exact) < dim(Active)`.

Cyclomatic condition:

* `HasObserver G`: `|E| ≥ |V|` (at least one extra edge beyond spanning tree).
* `observer_creates_mass`: `HasObserver` + connected ⟹ `AllowsGenesis`.

In other words, wiring in “enough” connectivity to host an observer also creates room in H for **mass-carrying topological modes**.

Main theorem:

* `observable_present_undetermines_future`: there exist microstates S₁, S₂ with same observation now but different observations after evolution.

Interpretation: observation doesn't commute with dynamics.

---

### Topological genesis: open vs closed line

#### `Diaspora/Models/Genesis.lean`

Two graphs on 3 nodes:

* `G_open`: line `0–1–2`
* `G_closed`: cycle `0–1–2–0`

A uniform “rotational” forcing field `sigma_forcing` wants +1 flow around the triangle.

Theorems:

* `open_state_is_exact`: on the open line, `sigma_forcing` is exact (`d0 ϕ`).
* `closed_state_is_not_exact`: on the closed loop, no `ϕ` can satisfy `d0 ϕ = σ` on all edges.
* `harmonic_genesis`: in the closed case, Hodge decomposition produces a non-zero harmonic γ whose holonomy around the cycle is 3.

Genesis from noise:

* `C1.IsExact σ`: σ equals `d0 ϕ` for some potential.
* `non_exact_has_nonzero_harmonic`: non-exact forms have positive-energy harmonic projection.
* `exact_forms_proper_subset`: there exist non-exact 1-cochains (`sigma_forcing` is a witness).
* `random_field_has_harmonic_component`: generic constraint fields have harmonic content.

Interpretation: closing the loop is exactly the topological move that makes "irremovable frustration" possible. Generic noise creates topology. Thanks to the spectral gap, any such harmonic component comes with a fixed minimum energy bill `1/n` - genesis isn’t just generic, it’s **energetically chunky**.

(Compare `Logic/Genesis.lean` for the same phenomenon from the formal logic perspective: the rotational constraint is an unsatisfiable theory whose unsatisfiability *is* the harmonic content.)

---

### Self-measurement & "introspection"

#### `Diaspora/Quantum/Measurement.lean`

* Parallel transport operator:

  * `transport_step σ i j ψ = exp(i σ_ij) ψ`

* `introspection_operator`: transport a phase around a fundamental cycle and compare.

Theorems:

* `zombie_cannot_see_self`: if `σ` is exact (`σ = d0 ϕ`), going around the loop returns the same phase. No observable holonomy → “no self-awareness”.
* `self_aware_detection`: if there is a harmonic component with winding number 3, then transport around the loop multiplies the phase by `exp(i·3)`.

This is a poetic way of saying: holonomy is the obstruction to being globally exact, recast as “self-measurement”.

---

### Glassy dynamics

#### `Diaspora/Dynamics/Glass.lean`

#### `Diaspora/Models/Triangle.lean`

Formal notion of **graph isomorphism** and “glassy system”:

* `IsIsomorphic G₁ G₂`: existence of a vertex permutation preserving edges.
* `StableLandscape σ C_max`: graphs that are equilibria for the constraints.
* `IsGlassySystem`: existence of at least two non-isomorphic stable graphs.

Tailed triangle example:

* A triangle `0–1–2` with a tail `0–3`.
* A frustrated constraint `frustrated_sigma` around the loop.

Two candidate vacua after one edge breaks:

* `star_graph`: break (1,2) → everything hangs off vertex 0.
* `line_graph`: break (0,1) → a 3–0–2–1 path.

Theorems:

* `star_has_zero_strain`, `line_has_zero_strain` - both have perfect local relaxation.
* `star_ne_line` - they are not isomorphic (different degree profiles).
* `tailed_triangle_is_glassy` - the system has at least two distinct stable vacua.

Interpretation: **glassy** = history-dependent: different break orders end in genuinely different topologies.

---

### The shape of contradiction

#### `Diaspora/Models/WeightedStrain.lean`

#### `Diaspora/Models/StrainDynamics.lean`

When constraints conflict, *where* does the strain land? Weighted optimization and constraint-counting give different answers.

Setup: a "bundle" graph with 5 nodes. One heavy edge (0↔1) demands flux 10. Six light edges (through witnesses 2,3,4) demand flux 0. The constraints contradict - you can't satisfy both.

* `asymmetric_weights`: heavy edge weighted 100:1 against light edges.
* `lazy_phi`: optimal potential under weighted energy - satisfies the heavy edge perfectly.
* `heavy_edge_relaxed`: strain on heavy edge = 0.
* `light_edges_strained`: strain on light edges = 25.

Theorem:

* `weight_determines_breaking`: at threshold `C_max = 20`, light edges break first, even though they're the majority (6 vs 1).

The second file explores how Hebbian plasticity responds:

* `dominance_causes_strain_asymmetry`: if heavy dominates, light edges bear more strain.
* `hebbian_favors_strained`: strained edges grow faster under plasticity.
* `ratio_correction`: the light/heavy weight ratio increases each step.

Interpretation: weighted optimization localizes contradiction onto low-weight edges. Hebbian dynamics provides a corrective - strain is attention, and attention builds capacity. The shape of contradiction shifts over time.

---

### Observation as structural reinforcement

#### `Diaspora/Models/ObserverEffect.lean`

Uses the kite graph (triangle 0–1–2 with tail 0–3) to show how observation reinforces topology.

* `observer_probe_potential`: a potential that strains the cycle but not the tail.
* `observation_is_selective`: cycle edges strained > 0, tail edge strained = 0.
* `attention_is_structural_reinforcement`: after one Hebbian step, cycle edges outweigh tail.

Interpretation: repeated observation (probing with a potential) causes the observed structure to accumulate weight. Under fixed total capacity, unobserved edges atrophy. This is a topological **Zeno effect** - attention freezes the topology it touches.

---

### False vacuum & protection

#### `Diaspora/Models/FalseVacuum.lean`

* A θ-graph (two loops sharing a pair of nodes).
* Parameterized constraints:

  * `Ft` (trap flux), `Fs` (smart edge flux), `Fa` (anchor tension).
* `make_sigma`, `make_phi` construct constraints and relaxation potentials.

Theorems:

* `quenched_instability`: in a non-relaxing limit, the trap edge carries the largest strain.
* `annealed_crossover`: there exists a relaxation magnitude `P` where the trap edge becomes *safer* than the smart edge, even if `Ft > Fs`.

Interpretation: a toy model of **false vacuum protection** via relaxation.

---

### Interaction & the handshake

#### `Diaspora/Models/Interaction.lean`

* Two disjoint triangles `{0,1,2}` and `{3,4,5}`:

  * `disjoint_worlds`
* One bridge → `bridged_worlds`
* Two bridges → `fused_worlds`

Using a simple Betti-number proxy, we prove:

* `isolation_betti_number`: two disconnected triangles → total “b₁” = 2.
* `contact_is_sterile`: adding a single bridge keeps the Betti number the same.
* `fusion_creates_shared_reality`: adding a second bridge creates a new independent cycle that threads both worlds.

Then we define a **communication cycle** and prove the “handshake theorem”:

* There exists a harmonic γ on the fused graph with non-zero holonomy around the cross-world cycle.

Interpretation: one bridge is just contact; two bridges create shared topology.

---

### Quantum dynamics & Berry phase

#### `Diaspora/Quantum/Evolution.lean`

Quantum layer:

* `SchrodingerEvolution`: a discrete Schrödinger equation with Hamiltonian `-Δ + V`.
* `ParametricState`: ψ depending on a parameter index.
* `DiscreteBerryConnection`: `A(R₁, R₂) = i ⟨ψ(R₁), ψ(R₂)⟩`.
* `BerryPhase`: holonomy of the Berry connection along a discrete parameter-space cycle.
* `GaugeTransform`: ψ ↦ `e^{iθ(R)} ψ`.

This is Berry phase on a finite parameter graph.

---

## How to build / run

This project targets **Lean 4 + mathlib**.

```bash
# Install Lean 4 & Lake (see leanprover-community docs)
# Then from the project root:
lake build
```

