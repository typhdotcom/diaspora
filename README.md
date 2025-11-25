<p align="center">
  <img src="img/logo.png" alt="Diaspora" height="100" />
</p>

# Diaspora

*A toy universe of topology*

Diaspora is a Lean 4 project that builds a discrete Hodge-theoretic toy model on finite graphs. It's an amateur effort, with LLM help, built solely to explore philosophical intuitions through topology.

- **Graphs** whose edges can break under strain  
- **Constraints** living as 1-cochains (flux / tension)  
- **Potentials** as 0-cochains (relaxation fields)  
- **Harmonic forms** as the “ irreducible frustration ” left over when you’ve relaxed everything you can  
- **Topology change** when edges snap  
- **Plasticity** where edges strengthen under strain and atrophy from disuse (Hebbian learning + scarcity)
- A “**glassy**” landscape with multiple non-isomorphic stable vacua
- Quantum add-ons: discrete Schrödinger evolution, Berry phase, and holonomy-as-measurement

Everything here is proved inside Lean + mathlib. The physics (`black hole`, `handshake`, `false vacuum`, `observer`, etc.) are metaphors layered on top of finite-dimensional linear algebra and graph theory.

## Big picture

At the core is a simple idea:

> Take a finite graph. Put a “desired flux” on each edge (a 1-cochain).  
> Let the vertices carry a “relaxation potential” (a 0-cochain).  
> Try to relax away as much strain as possible. Whatever you *cannot* relax
> is topological and shows up as a harmonic form.

This is expressed in a very classical way:

- `σ : C1 n` is a real skew-symmetric 1-cochain (edge constraints / flux).
- `ϕ : C0 n` is a real 0-cochain (vertex potential).
- The coboundary `d0 : C0 → C1` takes differences along edges.
- The “internal energy” is essentially `‖d0 ϕ - σ‖²` with a discrete inner product.

Then we prove (for the complete graph) a discrete **Hodge decomposition**:

> Every 1-cochain `σ` splits as  
> `σ = d0 ϕ + γ`  
> where `d0 ϕ` is exact and `γ` is divergence-free (harmonic), and the two parts are orthogonal.

That’s all standard math, but we make it **fully formal** in Lean and then build a whole story-universe out of the consequences.

## Under the hood: representational density

One way to read all of this is: the primitive object isn’t really the graph, it’s the
**representational demand** living on would-be edges.

- A 1-cochain `σ : C1 n` is "how much relation" each ordered pair of vertices wants to carry.
- The inner product / norm on 1-cochains is the total "capacity" of that demand.
- A `DynamicGraph G` just says which of those edges are currently allowed to exist.

Given `G` and `σ`, you can then split the capacity into:

- realized capacity on active edges, and
- latent capacity on edges that are currently broken.

This is formalized in `WeightedGraph` via `total_capacity_fixed`, forcing a zero-sum competition for existence: edges must "pay rent" (carry strain) to survive renormalization.

## What lives in this repo?

This is the “tour of files” version — you don’t need to read them in this order, but it gives you a mental map.

### Discrete calculus on graphs

**`Diaspora/DiscreteCalculus.lean`**

Foundations:

- `DynamicGraph n`: graph with `n` fixed vertices and a *dynamic* set of active edges.
- 0- and 1-cochains:
  - `C0 n := Fin n → ℝ`
  - `C1 n`: skew-symmetric `Fin n → Fin n → ℝ`
- Classical coboundary / gradient:
  - `d0 : C0 n → C1 n`
- Inner product and norm on 1-cochains:
  - `inner_product_C1`, `norm_sq`
- **Active forms**:
  - `ActiveForm G`: 1-cochains that vanish on broken edges of a `DynamicGraph G`.
  - Equipped with an inner product, norm, and turned into an `InnerProductSpace`.

Graph-aware operators:

- `d_G : C0 n → ActiveForm G` — gradient respecting which edges exist.
- `δ_G : ActiveForm G → C0 n` — divergence.
- `Δ_G := δ_G ∘ d_G` — graph Laplacian.
- `IsHarmonic σ` — divergence-free 1-cochains.

Quantum flavor:

- `QC0 n`, `QC1 n` — complex analogues.
- Hermitian inner products `inner_QC0`, `inner_QC1`.
- `quantum_laplacian` and `IsEnergyEigenstate`.

**`Diaspora/Duality.lean`**

A small companion file:

- Defines a discrete Hodge-star–style operation on complete graphs.
- Proves basic duality lemmas that make the harmonic / energy statements cleaner.
- You can safely skip it on a first pass; it’s part of the underlying toolkit rather than a story file.

### Hodge decomposition (the heavy lifting)

**`Diaspora/HodgeDecomposition.lean`**

This is where the real functional-analysis work happens.

- Builds an inner product space structure on `ActiveForm G`.
- Uses finite-dimensionality + orthogonal projection to define:
  - `ImGradient G` — the subspace of exact graph gradients.
  - An orthogonal decomposition `σ = d_G φ + γ` with `γ ⟂ ImGradient`.
- Specializes this to the **complete graph** and transfers everything back to plain `C1 n`.

Main theorem (for the complete graph):

```lean
theorem hodge_decomposition {n : ℕ} [Fintype (Fin n)] (σ : C1 n) :
  ∃ (ϕ : C0 n) (γ : C1 n),
    (∀ i j, σ.val i j = (d0 ϕ).val i j + γ.val i j) ∧
    IsHarmonic γ ∧
    inner_product_C1 (d0 ϕ) γ = 0
```

This is the core technical engine everything else leans on.

### Harmonic analysis and physical interpretations

**`Diaspora/HarmonicAnalysis.lean`**

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
* Show harmonic forms supported on such a cycle are **constant along the loop**.
* Get **topological quantization** statements:

  * Winding number `m` implies specific energy levels like `m² / n`.

Quantum:

* `quantum_laplacian_hermitian` — the discrete Laplacian is self-adjoint.
* `constant_is_zero_energy` — constant phases are zero-energy eigenstates.
* `quantum_exact_vanishes_on_cycles` — quantum version of Stokes.

### Topology, strain, and graph evolution

**`Diaspora/TopologyChange.lean`**
**`Diaspora/TopologyDynamics.lean`**

These files turn the math into a dynamics:

* Define **edge strain**:

  * `edge_strain ϕ σ i j := ((d0 ϕ).val i j - σ.val i j)²`
* Show **strain must localize** if total frustration is high:

  * `strain_must_localize`: a pigeonhole principle on edges.
* `BreakingThreshold` and `C_max`: when strain exceeds this, an edge “breaks”.

Graph metrics:

* `DynamicGraph.edge_count`
* `DynamicGraph.cyclomatic_number` — counts cycles (for connected graphs).

Edge removal and evolution:

* `remove_edge` — deletes an undirected edge (both orientations).
* `find_overstressed_edge` — pick an active edge with highest strain above threshold.
* `evolve_step` — perform one "break" if needed.

Dynamic energy:

* `dynamic_strain_energy G ϕ σ` — strain summed only over active edges.
* `energy_drop_on_break` — breaking an edge reduces this energy by exactly that edge’s strain.
* `is_equilibrium` — no edge exceeds `C_max`; `equilibrium_is_stable` shows that in this case `evolve_step` is a no-op.

There’s a simple entropy-like quantity hiding here: the **latent capacity** of `σ`
with respect to `G` (how much strain lives on broken edges). Along any valid
evolution chain, latent capacity is non-decreasing; breaking an edge moves some
capacity from "realized" to "latent" and never back. That gives a bare-bones
arrow of time: a partial order on graphs where history is exactly which edges
paid the price for the frustration.

#### Universe evolution (the main loop)

**`Diaspora/Universe.lean`**

This is the proof-carrying simulation engine:

* `EvolutionChain n σ G` — inductive type of valid histories, step-by-step edge breaks.
* `evolve` — given a solver `solver : DynamicGraph n → C1 n → C0 n`, repeatedly:

  1. Solve for a potential `ϕ`.
  2. Find an overstressed edge.
  3. Break it and extend the chain.
* `run_universe` — start from an initial graph `G₀` and run `evolve`.

Main structural statement:

* `simulation_entropy_nondecreasing` — latent capacity with respect to `σ`
  never decreases along this simulation. Once capacity has moved to broken edges,
  it doesn’t come back; the “time” of the universe is literally the accumulation
  of irreversibly latent strain.

“Black hole” metaphor (in the TopologyChange layer):

* `black_hole_formation` packages:

  1. **Some edge must break** under high frustration.
  2. A harmonic form with positive norm appears.
  3. External observers measuring holonomy “see only γ” (no-hair analogue).

### Weighted graphs and plasticity

**`Diaspora/WeightedGraph.lean`**
**`Diaspora/Plasticity.lean`**

This layer moves from binary topology (active/inactive) to continuous capacity. It treats the graph as an economic system with finite resources.

**Foundations:**

  * `WeightedGraph n`: Edges have continuous weights `w_ij ≥ 0`.
  * **Conservation of Attention**: The total capacity of the universe is fixed at `n²`.
      * `∑ w_ij = n²`
  * `raw_strain`: The pure potential difference `(d0 ϕ - σ)²`, unmitigated by capacity.
  * `to_dynamic`: Thresholding a weighted graph converts it back to a `DynamicGraph` (emergent topology).

**The Plasticity Cycle:**
Evolution happens in a loop of Growth, Scarcity, and Pruning (`plasticity_cycle`):

1.  **Hebbian Phase**: Edges under high strain grow stronger (`w' = w + η·strain`).
2.  **Scarcity Phase**: The graph is renormalized to enforce the conservation of attention. If some edges grow, others must shrink.
3.  **Pruning**: Weights falling below `ε` are zeroed out.

**Key Theorem:** "Use it or lose it."

  * `plasticity_atrophy_of_unstressed`: If the system is under stress, any edge with *zero* local strain will strictly decrease in weight (it is "taxed" to pay for the growth of stressed edges).

### Toy systems and named stories

These are the narrative / physics-inspired examples built on top.

#### Topological genesis: open vs closed line

**`Diaspora/TopologicalGenesis.lean`**

* Two graphs on 3 nodes:

  * `G_open`: line `0–1–2`
  * `G_closed`: cycle `0–1–2–0`
* A uniform “rotational” forcing field `sigma_forcing` which wants +1 flow around the triangle.

Theorems:

* `open_state_is_exact`: on the open line, `sigma_forcing` is exact (`d0 ϕ`).
* `closed_state_is_not_exact`: on the closed loop, no `ϕ` can satisfy `d0 ϕ = σ` on all edges.
* `harmonic_genesis`: in the closed case, Hodge decomposition produces a non-zero harmonic γ whose holonomy around the cycle is 3.

Interpretation: **closing the loop** is exactly the topological move that makes “irremovable frustration” possible.

#### Self-measurement & “introspection”

**`Diaspora/SelfMeasurement.lean`**

* Parallel transport operator:

  * `transport_step σ i j ψ = exp(i σ_ij) ψ`
* `introspection_operator`: transport a phase around a fundamental cycle and compare.

Theorems:

* `zombie_cannot_see_self`: if `σ` is exact (`σ = d0 ϕ`), going around the loop returns the same phase. No observable holonomy → “no self-awareness”.
* `self_aware_detection`: if there is a harmonic component with winding number 3, then transport around the loop multiplies the phase by `exp(i·3)`.

This is a poetic way of saying: **holonomy is the obstruction to being globally exact**, recast as “self-measurement.”

#### Glassy dynamics

**`Diaspora/GlassDynamics.lean`**
**`Diaspora/FrustratedTriangle.lean`**

* Formal notion of **graph isomorphism** and “glassy system”:

  * `IsIsomorphic G₁ G₂`: existence of a vertex permutation preserving edges.
  * `StableLandscape σ C_max`: graphs that are equilibria for the constraints.
  * `IsGlassySystem`: existence of at least two non-isomorphic stable graphs.

Tailed triangle example:

* A triangle `0–1–2` with a tail `0–3`.
* A frustrated constraint `frustrated_sigma` around the loop.
* Two candidate vacua after one edge breaks:

  * `star_graph`: break (1,2) → everything hangs off vertex 0.
  * `line_graph`: break (0,1) → a 3–0–2–1 path.

Theorems:

* `star_has_zero_strain`, `line_has_zero_strain` — both have perfect local relaxation.
* `star_ne_line` — they are not isomorphic (different degree profiles).
* `tailed_triangle_is_glassy` — the system has at least two distinct stable vacua.

Interpretation: **glassy** = history-dependent: different break orders end in genuinely different topologies.

#### False vacuum & protection

**`Diaspora/FalseVacuum.lean`**

* A θ-graph (two loops sharing a pair of nodes).
* Parameterized constraints:

  * `Ft` (trap flux), `Fs` (smart edge flux), `Fa` (anchor tension).
* `make_sigma`, `make_phi` construct constraints and relaxation potentials.

Theorems:

* `quenched_instability`: in a non-relaxing limit, the trap edge carries the largest strain.
* `annealed_crossover`: there exists a relaxation magnitude `P` where the trap edge becomes *safer* than the smart edge, even if `Ft > Fs`.

Interpretation: a toy model of **false vacuum protection** via relaxation.

#### Interaction & the handshake

**`Diaspora/Interaction.lean`**

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

Interpretation: **one bridge is just contact; two bridges create shared topology**.

#### Quantum dynamics & Berry phase

**`Diaspora/QuantumDynamics.lean`**

Quantum layer:

* `SchrodingerEvolution`: a discrete Schrödinger equation with Hamiltonian `-Δ + V`.
* `ParametricState`: ψ depending on a parameter index.
* `DiscreteBerryConnection`: `A(R₁, R₂) = i ⟨ψ(R₁), ψ(R₂)⟩`.
* `BerryPhase`: holonomy of the Berry connection along a discrete parameter-space cycle.
* `GaugeTransform`: ψ ↦ e^{iθ(R)} ψ.

This is the “Berry phase but on a finite parameter graph” version.

## How to build / run

This project targets **Lean 4 + mathlib**.

```bash
# Install Lean 4 & Lake (see leanprover-community docs)
# Then from the project root:
lake build
```

