<p align="center">
  <img src="img/logo.png" alt="Diaspora" height="100" />
</p>

# Diaspora

*A toy universe of topology*

Diaspora is a Lean 4 project that builds a discrete Hodge-theoretic toy model on finite graphs. It's an amateur effort, with LLM help, built solely to explore philosophical intuitions through topology. Everything is proved inside Lean + mathlib; the physics vocabulary is metaphor layered on linear algebra and graph theory.

---

## Big picture

At the core is a simple idea:

> Take a finite graph. Put a "desired flux" on each edge (a 1-cochain).
> Let the vertices carry a "relaxation potential" (a 0-cochain).
> Try to relax away as much strain as possible. Whatever you *cannot* relax
> is topological and shows up as a harmonic form.

This is formalized in three layers:

1. **The Mathematical Ideal (Global):**
   In `Hodge/Decomposition.lean`, we use global linear algebra to prove that a perfect potential `ϕ` exists and compute **Betti numbers** via the dimension formula
   `dim(H) + |V| = |E| + dim(Ker d)`.
   For a connected graph this recovers the usual cyclomatic number: `dim(H) = |E| - |V| + 1`.

2. **The Physical Mechanism (Local):**
   In `Dynamics/Diffusion.lean`, we show that the system doesn't *need* a global solver to find this state. Nodes simply push against their neighbors (Heat Equation) to minimize local strain. Observers measure topology locally via **Holonomy** (walking in loops).

3. **The Bridge (Index Theorem):**
   In `Hodge/IndexTheorem.lean`, we prove these views are equivalent via the discrete **McKean-Singer formula**: `b₀ - b₁ = |V| - |E|`. The supertrace of the heat kernel is constant for all time - watching diffusion at *any* instant reveals the Euler characteristic. The proof uses **spectral pairing**: d and δ intertwine the Laplacians (discrete supersymmetry), so non-zero eigenvalues cancel in pairs. Only harmonic modes contribute.

Then we prove a discrete **Hodge decomposition**:

> Every 1-cochain `σ` splits as `σ = d0 ϕ + γ`
> where `d0 ϕ` is exact and `γ` is divergence-free (harmonic), and the two parts are orthogonal.

A key quantitative result: **topological defects have a mass gap**. If γ has non-trivial winding around an n-cycle, then ‖γ‖² ≥ 1/n. This minimum energy is the "nucleation barrier" - you can't have a little bit of topology.

This Hodge machinery admits two natural interpretations:

* **Physical**: Strain, relaxation, and topology change. Exact forms are relaxable strain; harmonic forms are irreducible frustration that localizes as "mass" and drives graph evolution.

* **Logical**: Constraints and satisfiability. Exact forms correspond to satisfiable theories; harmonic forms correspond to locally consistent but globally unsatisfiable paradoxes. The bridge theorem: satisfiability ↔ exactness.

Both perspectives give you the same mathematics: structure creation, quantization, dynamics, and an arrow of time.

### The Grand Synthesis

`the_diaspora_correspondence` chains the full picture: **Paradox → Topology → Mass → Gravity**. Matter is the physical symptom of trapped logical inconsistency.

Gravity emerges from edge-sharing. Two cycles traversing shared edges in opposite directions have lower combined energy than the sum of their parts. Systems evolve toward this minimum. `gravity_is_edge_sharing` formalizes this: binding energy = 2k/(n₁·n₂) for k shared edges.

---

## Mathematical Foundations

The codebase is built on discrete exterior calculus. Understanding these types is essential:

### Cochains (the fields)

| Type | Definition | Physical Meaning |
| :--- | :--- | :--- |
| `C0 n` | `Fin n → ℝ` | **Potential** on vertices (phase, voltage, belief) |
| `C1 n` | Skew-symmetric `Fin n → Fin n → ℝ` | **Flux** on edges (constraint, current, tension) |
| `d0 ϕ` | `(i,j) ↦ ϕ j - ϕ i` | **Gradient**: potential differences |
| `ActiveForm G` | `{ σ : C1 // σ = 0 off G.active_edges }` | Flux respecting topology |

### Chains (the geometry)

| Type | Definition | Physical Meaning |
| :--- | :--- | :--- |
| `Chain1 n` | Skew-symmetric `Fin n → Fin n → ℤ` | Formal sum of oriented edges |
| `SimpleCycle` | Connected cycle with `next`/`prev` | A single closed loop |
| `GeneralCycle` | List of vertices forming a cycle | Arbitrary cycle (for overlap) |
| `DynamicGraph n` | `{ active_edges : Finset, symmetric, no_loops }` | Graph with breakable edges |

### Operators

| Operator | Type | Meaning |
| :--- | :--- | :--- |
| `d_G` | `C0 n → ActiveForm G` | Gradient on active edges |
| `δ_G` | `ActiveForm G → C0 n` | Divergence (sum of incoming flux) |
| `Δ_G` | `C0 n → C0 n` | Graph Laplacian = δ ∘ d |
| `holonomy σ c` | `C1 n → Chain1 n → ℝ` | Integral of flux around cycle |

### Key Subspaces

| Subspace | Definition | Physical Meaning |
| :--- | :--- | :--- |
| `ImGradient G` | `{ dϕ \| ϕ : C0 n }` | **Exact** forms (satisfiable constraints) |
| `HarmonicSubspace G` | `(ImGradient G)^⊥` | **Harmonic** forms (irreducible frustration) |

The **Hodge decomposition** says every `σ : ActiveForm G` splits uniquely as `σ = dϕ + γ` where `dϕ` is exact and `γ` is harmonic. The exact part can be "relaxed away" by choosing the right potential; the harmonic part cannot.

---

## Logic: Constraints as Geometry

The `Logic` layer proves an isomorphism between Constraint Satisfaction Problems (CSP) and Hodge Theory.

### The Central Isomorphisms

* **The Bridge Theorem** (`satisfiable_iff_exact_on_graph`): A theory is satisfiable iff its constraint cochain is Exact (`d_0 φ`).
* **The Paradox Theorem** (`inconsistency_implies_topology`): Locally consistent but globally unsatisfiable theories have non-trivial Harmonic content.
* **The Genesis Theorem** (`genesis_is_three_dehn`): The simplest paradox (triangle 0→1→2→0 with +1 strain) creates a harmonic form equal to exactly 3× the Dehn Twist. The Dehn twist has winding 1 and energy 1/3; genesis has winding 3 and energy 3.
* **The Monodromy Theorem** (`monodromy_exact_iff`): Exactness ↔ zero walk_sum on all closed walks.

### Universe.lean: The Causal Chain

A `Universe` bundles Theory T, DynamicGraph G (from T), and potential ϕ. When T is locally consistent but globally unsatisfiable:

1. `paradox_implies_deficit`: TopologicalDeficit > 0
2. `paradox_creates_mass`: Non-zero harmonic component
3. `matter_creates_gravity`: Irreducible strain energy > 0

`the_diaspora_correspondence` chains: logical contradiction → information deficit → mass → gravitational strain.

The key quantitative result (`harmonic_component_gives_energy_floor` in `Dynamics/Transition.lean`): if an ActiveForm has non-zero harmonic component γ, strain energy ≥ ‖γ‖² regardless of potential. Harmonic content is irreducible frustration.

### Universal Cover

* `universal_cover_is_classical`: The universal cover is acyclic (a tree).
* `paradox_dissolves_in_cover`: Every constraint field becomes exact when lifted.
* `history_potential_diff_is_holonomy`: Potential difference between histories = holonomy around their loop.

### Classicality

* `IsClassical G`: `dim(HarmonicSubspace G) = 0` - tree-like universe.
* `classical_implies_acyclic`: dim(H) = 0 ⟹ acyclic.
* `cycle_implies_nonclassical`: Cycles contradict classicality.

### Orthogonality & Overlap

This machinery is the foundation of gravity. The key concept is **signed overlap**:

| Definition | Formula | Meaning |
| :--- | :--- | :--- |
| `sameDirectionEdges c₁ c₂` | count of edges in both, same direction | Constructive interference |
| `oppositeDirectionEdges c₁ c₂` | count of edges in both, opposite direction | Destructive interference |
| `signedOverlap c₁ c₂` | same - opposite | Net alignment |

**The Inner Product Formula** (`cycle_inner_product_formula`):
> ⟨γ₁, γ₂⟩ = signedOverlap(c₁, c₂) / (len₁ × len₂)

This is the discrete analog of the electromagnetic field energy formula. Cycles sharing edges have non-zero inner product. The sign determines whether they attract (opposite direction) or repel (same direction).

Key results:
* `edge_disjoint_cycles_orthogonal`: Edge-disjoint cycles have orthogonal harmonic forms → energies add independently.
* `reverse_negates_form`: Reversing a cycle negates its harmonic form.
* `opposite_orientation_minimizes`: Overlapping cycles prefer opposite orientation (anti-ferromagnetic coupling).
* `signedOverlap_symm`: The overlap is symmetric.

### Information Theory (`Logic/Information.lean`)

The central insight: **topology is incompressible data**.

#### Capacity and Deficit

| Quantity | Definition | Meaning |
| :--- | :--- | :--- |
| `RawCapacity G` | dim(ActiveForm G) | Degrees of freedom in arbitrary constraint field |
| `ClassicalCapacity G` | dim(ImGradient G) | Degrees of freedom in satisfiable (exact) fields |
| `TopologicalDeficit G` | RawCapacity - ClassicalCapacity | Information that *cannot* be compressed into potentials |

**The Deficit Theorem** (`topological_deficit_eq_harmonic_dim`):
> TopologicalDeficit = dim(HarmonicSubspace) = Betti number b₁

When you force a constraint field to be satisfiable, you lose exactly dim(H) bits of information. This lost information *is* the harmonic content—the topology. Exact forms live in a smaller space; harmonic forms carry the residual complexity.

#### Kolmogorov Complexity of Genesis

How many constraints does it take to create topology?

* **Lower bound** (`minimum_complexity_of_genesis_connected`): Creating deficit k on a connected graph requires program length ≥ n + k - 1.
* **Upper bound** (`maximum_deficit_bound`): A program of length m creates deficit ≤ m - n + 1.

**The triangle saturates both bounds**: n = 3 vertices, m = 3 constraints, k = 1 deficit. It is the algorithmically simplest non-trivial topology.

#### Key Theorems

* `matter_is_incompressible_complexity`: When TopologicalDeficit > 0, there exist states σ that cannot be written as dϕ for any potential ϕ.
* `information_leak_is_inevitable`: As edge density grows (|E| > 2|V|), TopologicalDeficit > 0 is guaranteed. Dense graphs *must* carry mass.
* `deficit_complexity_characterization`: The lower and upper bounds together characterize exactly which (deficit, program length) pairs are achievable.

#### The Big Bang (`Logic/Limit.lean`)

Growing universes inevitably develop topology:

* `eventual_genesis`: Superlinear edge growth ⟹ eventually IsComplex (b₁ > 0).
* `inevitable_genesis`: As n → ∞ with multiplicative growth, classicalRatio → 0. The probability of remaining classical vanishes.

#### Fragility of the Void (`Logic/Probabilistic.lean`)

* `genesis_is_generic`: Non-trivial topology ⟹ satisfiable constraints form a proper subspace.
* `void_is_fragile`: A satisfiable theory with cycles is not robustly satisfiable—any single-constraint perturbation breaks it. The classical vacuum sits on a knife-edge.

---

## The Topological Zoo

We derive closed-form Betti numbers (b₁) for graph families. These confirm that topology scales with connectivity and dimension.

| Family | Notation | b₁ Formula | Interpretation |
| :--- | :--- | :--- | :--- |
| **Complete** | K_n | (n-1)(n-2)/2 | Max frustration; dominates all graphs on n vertices. |
| **Bipartite** | K_{m,n} | (m-1)(n-1) | "Fundamental squares" count; coincides with Grid formula. |
| **Tripartite** | K_{a,b,c} | ab+bc+ca-(a+b+c)+1 | Threefold opposition; octahedron K_{2,2,2} has b₁=7. |
| **Cycle** | C_n | 1 | Minimal non-trivial topology; home of the Dehn twist. |
| **Path** | P_n | 0 | Classical vacuum (tree); no paradox. |
| **Wheel** | W_n = cone(C_n) | n | Observation amplifies topology. Hub creates n cycles. |
| **Friendship** | F_n | n | Vertex-sharing is sterile; paradoxes stack additively. |
| **Book** | B_n | n | Edge-sharing (channels) is transparent; non-interacting pages. |
| **Prism** | Prism_n | n+1 | Fusing two n-cycles creates n-1 new entanglement cycles. |
| **Ladder** | L_n | n-1 | Open prism; closing adds 2 cycles (one per end). |
| **Grid** | G_{m,n} | (m-1)(n-1) | Local frustration matches global bipartite frustration. |
| **Torus** | T_{m,n} | mn+1 | Boundary removal adds m+n wrapping cycles. |
| **Hypercube** | Q_n | 2^{n-1}(n-2)+1 | Dimensions multiply frustration exponentially. |
| **Cone** | cone(G) | \|E(G)\| | Observation crystallizes edges into cycles. |
| **Suspension** | susp(G) | \|E(G)\|/2+(n-1) | Two isolated observers double the topology. |
| **Petersen** | - | 6 | Democratic paradox; blame cannot be assigned. |

### Topology Bounds (`MaximumTopology.lean`, `EdgeAddition.lean`)

* `betti_one_le_complete`: For any connected graph G, b₁(G) ≤ b₁(K_n) = (n-1)(n-2)/2. Complete graphs maximize frustration.
* `betti_monotone_in_edges`: G ⊆ H as edge sets ⟹ b₁(G) ≤ b₁(H). Topology is monotonic in connectivity.
* `edge_addition_increases_betti`: Adding one edge to a connected graph increases b₁ by exactly 1. Genesis is quantized at the edge level.
* `tree_characterization`: A connected graph is a tree iff |E| = n - 1.

---

## Dynamics & Stability

Strain creates topology change. Topology change creates entropy.

### Stability (`Stability.lean`, `GirthStability.lean`)

* `criticalCycleLength C_max = ⌈1/√C_max⌉`: Minimum cycle length that can exist stably.
* `minimum_stable_threshold`: Stability ↔ C_max ≥ 1/(girth G)².
* `triangle_threshold`: Triangles require C_max ≥ 1/9 (densest paradox).
* `evolution_dual_arrow`: b₁ drops by 1 per non-bridge break; entropy increases.

### Strain & Diffusion (`Strain.lean`, `Diffusion.lean`)

* `nucleation_barrier n := 1/n`: Minimum energy to sustain a topological defect.
* `harmonic_component_gives_energy_floor`: If γ ≠ 0, strain energy ≥ ‖γ‖² for any potential.
* `diffusion_step`: Discrete heat equation.
* `stationary_diffusion_is_optimal`: Local balance ⟹ global Hodge minimum.

### Plasticity (`Plasticity.lean`)

* `plasticity_atrophy_of_unstressed`: Zero-strain edges shrink.
* `harmonic_cycle_resists_atrophy`: Harmonic content creates strain, hence reinforcement.

### Gravity (`Gravity.lean`, `BoundStates.lean`, `PairProduction.lean`, `ChargeConservation.lean`, `GravitationalStability.lean`, `GravitationalInteraction.lean`, `AsymmetricBinding.lean`, `NBodyBinding.lean`, `InvariantMass.lean`, `Velocity.lean`)

The core gravity formulas:

| Quantity | Formula | Meaning |
| :--- | :--- | :--- |
| Mass | m = 1/n | Energy of n-cycle |
| Binding energy | 2k/(n₁·n₂) | Energy saved by k opposite-overlap edges |
| Force | F = 2·m₁·m₂ | Newton-like product law |
| Pair threshold | 2/n | Energy to create n-cycle pair |
| Genesis threshold | 2/3 | Minimum for any matter creation |
| Combined energy | ‖γ₁‖² + ‖γ₂‖² + 2⟨γ₁,γ₂⟩ | Pythagorean + interaction |

* `sharing_reduces_energy`: Opposite-direction edge sharing reduces combined energy.
* `gravity_binding_energy`: Energy saved = 2k/(n₁·n₂) for k shared edges.
* `complete_overlap_annihilation`: Same cycle, opposite direction → zero combined energy.
* `three_cycle_energy_pairwise`: No 3-body forces; energy decomposes into pairwise interactions.
* `binding_energy_eq_neg_inner`: Binding energy = -2 × inner product of harmonic forms.
* `binding_energy_symm`: Binding energy is symmetric in its arguments.
* `no_emergent_forces_principle`: Total binding of N cycles = sum of pairwise bindings (bilinearity).
* `all_disjoint_zero_total_binding`: N disjoint cycles have zero total binding.
* `gravitational_force_is_product_of_masses`: F = 2·m₁·m₂, where m = 1/n for an n-cycle.
* `mass_energy_equivalence`: Energy of a cycle equals its mass.
* `repulsion_is_same_direction`: Same-direction sharing increases energy.
* `mass_gap`: Mass spectrum is discrete: 1/3, 1/4, 1/5, ... with gaps 1/(n·(n+1)).
* `IsBoundPair`: Cycles sharing opposite-direction edges form gravitationally bound pairs.
* `escape_energy_equals_binding`: Separating a bound pair requires adding back the binding energy.
* `gravitational_equilibrium_principle`: Maximum opposite overlap minimizes combined energy.
* `total_annihilation_energy`: Complete annihilation releases energy equal to 2×mass.
* `pair_threshold`: Creating an n-cycle pair requires energy 2/n.
* `genesis_threshold`: Minimum energy for any matter creation is 2/3 (triangle pair).
* `genesis_is_minimum`: For all n ≥ 3, pair_threshold n ≤ genesis_threshold.
* `genesis_below_planck_energy`: The genesis threshold (2/3) is below the Planck energy (1/√2).
* `signed_mass`: Charge = orientation × mass; reversed cycles carry opposite charge.
* `charge_conserved_in_binding`: Binding changes energy but preserves total charge.
* `CPT_symmetry`: Reversing a cycle negates its charge.
* `shared_edge_combined_value`: Per-edge strain on shared opposite edges = 1/n₁ - 1/n₂.
* `equal_cycle_strain_cancellation`: Equal-size cycles have zero strain on shared edges.
* `schwarzschild_equal_masses`: Binding = rest mass ⟺ complete overlap (k = n).
* `heavier_cycles_stronger_binding`: Smaller cycles (larger mass) bind more strongly.
* `gravitational_neutrality`: Annihilated pairs (zero combined form) have zero interaction with other cycles.
* `reduced_mass_formula`: Two-body reduced mass μ = 1/(n₁ + n₂) for cycles of length n₁, n₂.
* `max_shared_edges`: A cycle can share at most n edges total with another cycle.
* `max_binding_unequal`: For n₁ ≤ n₂, maximum binding energy is 2/n₂ (twice the lighter mass).
* `unequal_no_schwarzschild`: Unequal cycles cannot reach Schwarzschild; binding < rest mass when n₁ ≠ n₂.
* `binding_efficiency_formula`: Efficiency = 2n₁/(n₁+n₂); equal masses achieve 100%.
* `equal_optimal_for_schwarzschild`: Schwarzschild (binding = rest mass) ⟺ equal masses.

Interpretation: Cycles sharing edges in opposite directions cancel strain. Force is proportional to the product of masses. Same-direction repels; opposite-direction attracts. Gravity is strictly bilinear: multi-body binding decomposes exactly into pairwise terms with no emergent N-body forces. Bound pairs sit in potential wells; escape requires the binding energy. Orientation acts like electric charge: matter and antimatter are the same cycle traversed in opposite directions. Complete overlap annihilates to zero energy and zero charge; the resulting "vacuum bubble" exerts no gravitational influence. The reverse process (pair production) requires energy 2m to create a cycle-anticycle pair. The triangle pair costs 2/3, the minimum for any matter creation. This genesis threshold is sub-Planckian: you can create topology without reaching the Planck scale. The Schwarzschild condition (binding = rest mass) occurs exactly at complete overlap, and only for equal-mass pairs. Unequal masses leave residual mass equal to the difference; the heavier particle's excess cannot be canceled.

### Wave-Particle Duality (`DeBroglie.lean`, `EnergyTime.lean`)

* `deBroglie_product`: m × λ = 1, where λ = n is the cycle length.
* `wavelength_from_mass`: λ = 1/m; mass determines wavelength and vice versa.
* `heavier_shorter_wavelength`: Smaller cycles have more mass and shorter wavelength.
* `heisenberg_uncertainty`: Δx × Δp = 1; position and momentum uncertainties are complementary.
* `energy_time_uncertainty`: ΔE × Δt = 1; energy and time uncertainties are complementary.
* `period_equals_wavelength`: T = λ; the period equals the wavelength (with c = 1).
* `uncertainty_tradeoff`: Decreasing Δx increases Δp; you cannot minimize both.
* `minimum_uncertainty_state`: The triangle (n=3) is the minimum uncertainty state.
* `effective_mass_bound`: Bound systems have effective mass m₁ + m₂ - binding.
* `binding_increases_wavelength`: Stronger binding lowers effective mass, increasing wavelength.
* `annihilation_infinite_wavelength`: Complete annihilation gives zero effective mass.

Interpretation: The cycle length n is the wavelength. A cycle of length n has mass 1/n and wavelength n, so m × λ = 1 in natural units. Since frequency f = 1/n, the period T = n equals the wavelength; temporal and spatial scales coincide when c = 1. Both conjugate pairs satisfy exact uncertainty: Δx × Δp = 1 (spatial) and ΔE × Δt = 1 (temporal). Shorter cycles are heavier with shorter wavelengths and faster oscillation; longer cycles are lighter with longer wavelengths and slower oscillation. The triangle is the most localized state. Bound systems have reduced effective mass and correspondingly longer effective wavelength; complete annihilation yields zero mass.

### The Speed of Light (`SpeedOfLight.lean`)

* `speed_of_light_eq_one`: c = λ/T = n/n = 1; the speed of light is exactly 1.
* `speed_is_mass_independent`: c(n₁) = c(n₂); all defects propagate at the same speed.
* `wave_equation`: f × λ = c = 1; the standard wave relation.
* `spacetime_symmetry`: T = λ; period equals wavelength.
* `natural_units`: c = ℏ = 1; both fundamental constants are unity.
* `the_speed_of_light_correspondence`: Unifies wave equation, spacetime symmetry, and mass independence.

Interpretation: The constancy of c emerges from the structure of the theory. For any cycle of length n, the wavelength λ = n and period T = n are identical, so c = λ/T = 1 regardless of mass. This is the discrete analog of special relativity's first postulate: the speed of light is universal. Heavy particles (small n) and light particles (large n) propagate at exactly the same speed. The identification λ = T is Diaspora's version of spacetime isotropy, with space and time measured in the same units (vertices), which is why c appears as a dimensionless 1.

### Dispersion Relation (`Dispersion.lean`)

* `dispersion_relation`: E = p for all cycles; the massless dispersion relation.
* `all_cycles_lightlike`: E² = p²; cycles sit on the light cone.
* `invariant_mass_squared_vanishes`: E² - p² = 0; the null condition.
* `phase_velocity_is_c`: v_phase = E/p = 1 for all cycles.
* `group_velocity_is_c`: v_group = ∂E/∂p = 1; non-dispersive propagation.
* `no_rest_frame`: p > 0 always; topology cannot be at rest.
* `topology_is_motion`: Nonzero winding implies nonzero momentum.
* `the_dispersion_correspondence`: Unifies lightlike condition, velocity, and momentum.

Interpretation: With E = m = 1/n and p = 1/λ = 1/n, all cycles satisfy E = p, the dispersion relation of massless particles. Yet cycles have nonzero mass 1/n. The resolution: the invariant mass √(E² - p²) = 0, so cycles are lightlike (null) in the relativistic sense. Diaspora's "mass" is energy content, not rest mass. Since p = 1/n > 0 for all valid cycles, topological defects cannot be stopped. The phase gradient around a cycle is intrinsic momentum; you cannot have topology without motion. This explains why all defects propagate at c regardless of their energy: E = p implies v = 1 universally.

### Invariant Mass (`InvariantMass.lean`)

Single cycles are lightlike, yet they form bound states. The invariant mass m² = E² - p² determines the causal character of composite systems.

| Configuration | E | p | m² | Character |
| :--- | :--- | :--- | :--- | :--- |
| Single cycle | 1/n | 1/n | 0 | lightlike |
| Same-direction pair | 1/n₁ + 1/n₂ | 1/n₁ + 1/n₂ | 0 | lightlike |
| Opposite-direction pair | 1/n₁ + 1/n₂ | 1/n₁ - 1/n₂ | 4/(n₁·n₂) | timelike |
| Equal opposite (unbound) | 2/n | 0 | 4/n² | timelike |
| Equal opposite (bound, k edges) | 2/n - 2k/n² | 0 | (2/n - 2k/n²)² | timelike |
| Complete annihilation | 0 | 0 | 0 | null/vacuum |

* `single_cycle_invariant_mass_sq`: m² = 0 for single cycles.
* `same_direction_no_binding_lightlike`: Same-direction pairs remain lightlike.
* `opposite_direction_timelike`: Opposite-direction pairs have m² > 0.
* `opposite_direction_equal_invariant_mass`: Equal opposite-direction cycles: m = 2/n.
* `more_binding_less_mass`: More binding reduces invariant mass monotonically.
* `annihilation_invariant_mass`: Complete annihilation gives m = 0.
* `charge_determines_causality`: Same charge (direction) implies lightlike; opposite implies timelike.

Interpretation: Orientation determines whether momenta add or cancel. Same-direction cycles are co-propagating: their momenta add, keeping the system lightlike. Opposite-direction cycles are counter-propagating: their momenta partially cancel, creating a timelike composite that can be at rest. For equal cycles with opposite orientation, momenta cancel completely (p = 0), and the invariant mass equals the total energy. Binding reduces this energy continuously from 2/n (unbound) to 0 (annihilated). The Schwarzschild condition (complete overlap) returns the system to the null state. This connects charge/orientation to relativistic causality: matter-antimatter pairs are timelike and can annihilate; matter-matter pairs are lightlike and cannot.

### Bound State Velocity (`Velocity.lean`)

Single cycles travel at c. Bound pairs of counter-propagating cycles are subluminal.

| Configuration | v | γ |
| :--- | :--- | :--- |
| Single cycle | 1 | ∞ |
| Equal opposite (n₁ = n₂) | 0 | 1 |
| Unequal opposite | \|n₂ - n₁\|/(n₂ + n₁) | (n₁ + n₂)/(2√(n₁n₂)) |

* `opposite_direction_subluminal`: Counter-propagating pairs have v < 1.
* `equal_masses_at_rest`: When n₁ = n₂, velocity v = 0.
* `lorentz_factor_ge_one`: γ ≥ 1 always (AM-GM inequality).
* `relativistic_identity`: γ² = 1/(1 - v²).
* `velocity_from_energy_momentum`: v = |p|/E connects to the standard formula.

Interpretation: For opposite-direction pairs, momenta subtract while energies add. The velocity v = |n₂ - n₁|/(n₂ + n₁) is always less than 1. Equal masses give v = 0: the pair is at rest. Unequal masses give 0 < v < 1: subluminal but moving. The Lorentz factor γ = (n₁ + n₂)/(2√(n₁n₂)) satisfies the standard relativistic identity. This is how lightlike particles combine into massive objects that can stop.

### Action Quantization (`Action.lean`)

* `action_of_cycle`: S = E × T = 1; the action of any cycle is exactly 1.
* `action_is_universal`: S(n₁) = S(n₂); all cycles have the same action regardless of size.
* `planck_constant_eq_one`: ℏ = 1; Planck's constant is the action of one cycle.
* `action_equals_planck`: S = ℏ for all elementary defects.
* `additive_action`: k independent cycles have total action k.
* `the_action_correspondence`: Unifies action, energy, period, and Planck's constant.

Interpretation: Every topological defect carries exactly one quantum of action: S = E × T = (1/n) × n = 1. The n's cancel—a triangle and a 1000-cycle both have S = 1. This is Diaspora's **Bohr-Sommerfeld condition**: action is quantized in integer multiples of ℏ = 1. The quantum of action is universal because it's the "cost" of creating a topological obstruction, independent of the obstruction's size. Since the Betti number b₁ counts independent cycles, the total topological action of a universe equals b₁. This explains why ℏ appears in all quantum relations: it's built into discrete spacetime as the irreducible unit of topological complexity.

### Angular Momentum (`AngularMomentum.lean`)

* `angular_momentum_quantized`: L ∈ ℤ; winding numbers are integers.
* `rotator_energy`: E = L²/n; energy scales quadratically with angular momentum.
* `minimum_nonzero_angular_momentum`: |L| ≥ 1 for L ≠ 0; no fractional winding.
* `angular_momentum_additive`: L_total = L₁ + L₂; angular momentum is conserved.
* `energy_level_spacing`: ΔE = (2L+1)/n; spacing grows linearly with L.
* `classical_limit_angular_momentum`: ΔE/E → 0 as L → ∞; large quantum numbers approach continuity.

Interpretation: The winding number around a cycle is an integer by construction. This is angular momentum quantization, the discrete Bohr condition. For a harmonic form with winding L on an n-cycle, each edge carries value L/n, giving total energy L²/n. The cycle length n acts as a moment of inertia: larger cycles hold more angular momentum with less energy. The Dehn twist (L=1) is the ground state; higher windings L=2,3,... are excited rotational states. Angular momentum adds when forms combine, and opposite windings cancel. The connection to action: one winding contributes one quantum of action (ℏ = 1).

### Planck Scale (`Planck.lean`)

The three fundamental constants combine to define Planck units:

| Constant | Value | Origin |
| :--- | :--- | :--- |
| Speed of light | c = 1 | λ/T = n/n |
| Planck's constant | ℏ = 1 | S = E × T |
| Gravitational constant | G = 2 | F = 2m₁m₂ |

| Planck Unit | Formula | Value |
| :--- | :--- | :--- |
| Planck mass | m_P = √(ℏc/G) | 1/√2 ≈ 0.707 |
| Planck length | l_P = √(ℏG/c³) | √2 ≈ 1.414 |
| Planck time | t_P = √(ℏG/c⁵) | √2 ≈ 1.414 |

* `sub_planckian_bound`: m_max < m_P; the maximum mass (1/3) is less than the Planck mass (1/√2).
* `wavelength_exceeds_planck`: λ_min > l_P; the minimum wavelength (3) exceeds the Planck length (√2).
* `density_bound`: Maximum achievable density is far below Planck density.
* `fine_structure_of_diaspora`: (m_max/m_P)² = 2/9; a calculable dimensionless ratio.
* `triangle_sets_all_bounds`: The triangle (n=3) determines all fundamental cutoffs.

Interpretation: The discrete topology imposes bounds stricter than Planck physics. The triangle is the densest cycle, with mass 1/3, which falls below the Planck mass by a factor of √2/3 ≈ 0.47. The ratio (m_max/m_P)² = 2/9 plays a role analogous to the fine structure constant, but follows directly from the minimum cycle length (3) and the gravitational constant (2). All cutoffs trace back to the triangle: maximum mass, minimum wavelength, minimum period, maximum frequency.

### Schwarzschild Radius (`SchwarzschildRadius.lean`)

Two scales characterize a particle: the Compton wavelength λ_C = ℏ/(mc) where quantum effects dominate, and the Schwarzschild radius r_s = 2Gm/c² where gravitational collapse occurs.

| Scale | Formula | Value for n-cycle |
| :--- | :--- | :--- |
| Compton wavelength | λ_C = 1/m | n |
| Schwarzschild radius | r_s = 4m | 4/n |
| Ratio | r_s/λ_C = 4m² | 4/n² |

* `quantum_dominance`: r_s < λ_C for all n ≥ 3.
* `ratio_less_than_one`: r_s/λ_C = 4/n² < 1; all particles are quantum-dominated.
* `no_black_holes`: ¬(r_s ≥ λ_C); classical black holes cannot form.
* `triangle_ratio`: The triangle has r_s/λ_C = 4/9, the maximum.
* `larger_more_quantum`: Larger cycles have smaller ratios (more quantum-dominated).
* `critical_would_be_two`: r_s = λ_C would require n = 2, which is forbidden.

Interpretation: The critical cycle length where gravitational and quantum scales meet is n = 2. But cycles require n ≥ 3. The discrete structure prevents gravitational collapse: you cannot pack enough topology into a small enough region to form a black hole. Even the triangle, the densest defect, has r_s/λ_C = 4/9 < 1/2.

### Gravitational Time Dilation (`TimeDilation.lean`)

Binding creates time dilation: bound systems "tick slower" than free systems.

| Quantity | Formula | Meaning |
| :--- | :--- | :--- |
| Effective period | T_eff = 1/m_eff | Period of bound system |
| Time dilation factor | γ = m_ref/m_eff | Ratio of bound to free period |
| Redshift factor | z = m_eff/m_ref | Frequency ratio (reciprocal of γ) |

* `binding_slows_clocks`: More binding → longer effective period (slower time).
* `time_dilation_is_mass_ratio`: γ = (m₁ + m₂)/m_eff; dilation from mass deficit.
* `redshift_times_dilation`: z × γ = 1; redshift and dilation are reciprocals.
* `no_dilation_at_zero`: γ = 1 when k = 0; unbound particles experience no dilation.
* `schwarzschild_time_freeze`: At complete overlap, m_eff = 0; time "freezes".
* `schwarzschild_infinite_redshift`: At complete overlap, z = 0; infinite redshift.
* `weak_field_dilation`: For small binding, γ ≈ 1 + binding/m_ref.

Interpretation: Gravitational binding creates a "potential well" that slows proper time. For a free particle, period T = n = 1/m. For a bound system with effective mass m_eff = m₁ + m₂ - binding, the effective period T_eff = 1/m_eff > 1/(m₁ + m₂). The deeper the binding (more shared edges), the slower clocks run. At the Schwarzschild condition (complete overlap), effective mass vanishes and time stops entirely. This mirrors general relativity: time dilation near massive objects, gravitational redshift of escaping light, and time freeze at the event horizon. The duality z × γ = 1 connects time dilation (slower clocks) to redshift (lower frequency): they are two views of the same phenomenon.

### Simulation (`Sim.lean`)

* `simulation_entropy_nondecreasing`: Time is irreversible.

---

## Models and Stories

### Genesis (`Models/Genesis.lean`)

Two graphs on 3 nodes: open line vs closed cycle.

* `open_state_is_exact`: On the line, constraint is exact.
* `closed_state_is_not_exact`: On the cycle, no potential satisfies all edges.
* `harmonic_genesis`: Hodge decomposition produces γ with holonomy 3.

Interpretation: Closing the loop creates "irremovable frustration." Generic noise creates topology.

### Naming (`Models/Naming.lean`, `Models/NamingStability.lean`)

Models naming as topological symmetry breaking.

* Pre-naming: Star graph (b₁=0), stimuli interchangeable.
* Post-naming: Memory node creates cycle (b₁=1), stimuli distinguishable.
* `exists_harmonic_discriminator`: Harmonic form "sees" named stimulus but not others.

The stability layer connects naming to dynamics:

* `mass_of_name`: The naming cycle has energy exactly 1/3.
* `naming_stable_iff`: Names persist iff C_max ≥ 1/9.
* `cost_stability_tradeoff`: Shorter referential loops cost more energy AND require higher tolerance.
* `meaning_requires_tolerance`: The threshold determines the minimum cycle length that can exist.

Interpretation: Naming creates mass (the harmonic content is frozen residue of the referential act). That mass requires tolerance to persist. A universe with low tolerance cannot sustain short references; as tolerance drops, only longer, "cheaper" names survive. At zero tolerance: no names, pure classical vacuum.

### Interaction (`Models/Interaction.lean`)

Two disjoint triangles:

* `isolation_betti_number`: Total b₁ = 2.
* `contact_is_sterile`: One bridge keeps b₁ the same.
* `fusion_creates_shared_reality`: Two bridges create a new cross-world cycle.

Interpretation: One bridge is contact; two bridges create shared topology. **The handshake theorem.**

### Glass (`Models/Triangle.lean`, `Dynamics/Glass.lean`)

* `IsGlassySystem`: Multiple non-isomorphic stable equilibria.
* Tailed triangle: breaking different edges produces star vs line (non-isomorphic).

Interpretation: Glassy = history-dependent. Different break orders end in genuinely different topologies.

### Void (`Models/Void.lean`)

* `Microstate`: Full state (weighted graph + fields).
* `Macrostate`: Observable state (thresholded topology + spectrum).
* `observable_present_undetermines_future`: Same observation now, different observations later.

Interpretation: Observation doesn't commute with dynamics.

### Observer Effect (`Models/ObserverEffect.lean`)

* `attention_is_structural_reinforcement`: Repeated observation builds weight on observed structure.

Interpretation: Topological Zeno effect - attention freezes the topology it touches.

---

## Quantum (`Quantum/`)

### Evolution & Berry Phase

* `SchrodingerEvolution`: Discrete Schrödinger with H = -Δ + V.
* `DiscreteBerryConnection`, `BerryPhase`: Berry phase on finite parameter graphs.
* `introspection_operator`: Transport phase around a cycle.
* `zombie_cannot_see_self`: Exact σ ⟹ no observable holonomy.
* `self_aware_detection`: Harmonic component ⟹ measurable phase shift.

### The Local Witness Theorem (`Quantum/Witness.lean`)

* `local_holonomy_predicts_global_energy`: A local observer walking around a cycle can determine the global energy of a topological defect. The proof uses Stokes' theorem for walks: exact fluctuations (dϕ) vanish on closed loops, leaving only the harmonic content visible.

### Aharonov-Bohm (`AharonovBohm.lean`)

* `cycle_graph_all_flat`: Pure cycles have no triangular faces, so every connection is flat.
* `aharonov_bohm`: Flat connection + non-trivial topology ⟹ walk phase equals holonomy.
* `interference_phase_difference`: Phase ratio of two paths = phase around their enclosing loop.
* `holonomy_gauge_invariant`: Local phase choices (gauge) don't affect holonomy.
* `strainToConnection`: Maps a real 1-cochain σ to a U(1) connection via exp(i·σ).
* `holonomy_eq_exp_winding`: Holonomy of exp(i·σ) equals exp(i · winding).
* `exact_implies_trivial_holonomy`: Zero winding ⟹ trivial holonomy.
* `hodge_gauge_correspondence`: Holonomy of σ = holonomy of its harmonic projection γ. The exact part d₀φ contributes no phase.
* `harmonic_holonomy_quantized`: Integer winding m ⟹ holonomy = exp(i·m).

Interpretation: A particle acquires phase from encircling a region, even when the field is zero on its path. The Hodge decomposition σ = d₀φ + γ is the gauge decomposition: exact forms are pure gauge (locally observable, globally trivial), harmonic forms carry the gauge-invariant content. Satisfiable theories produce trivial holonomy; paradox produces phase.

---

## Project Structure

```text
Diaspora/
├── Core/           # Foundations: calculus, phase fields, weighted graphs
├── Hodge/          # Static theory: decomposition, harmonic analysis, spectral gap
├── Logic/          # Foundational semantics: constraints, paradox, Universe
├── Dynamics/       # Time evolution: diffusion, plasticity, topology change
├── Quantum/        # Complex extensions: Schrödinger, Berry phase, measurement
└── Models/         # Concrete examples and named stories
```

---

## How to build / run

This project targets **Lean 4 + mathlib**.

```bash
lake build
```
