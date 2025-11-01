#!/usr/bin/env -S uv run --with numpy --with networkx --with matplotlib
# /// script
# requires-python = ">=3.10"
# dependencies = [
#     "numpy>=1.24.0",
#     "networkx>=3.0",
#     "matplotlib>=3.7.0",
# ]
# ///
"""
Gauge Negotiation Experiment: Reality is Negotiated

This experiment models the interaction between two stable, but fundamentally
different, "singularities" (world-models):

- Singularity A (Rigid): Evolved under high cost (λ=10.0)
- Singularity B (Adaptive): Evolved under low cost (λ=0.1)
- The Negotiation GA is initialized by "mating" them
- The outcome is the *new* emergent reality (G_negotiated)

**Relationship to Lean formalization:**
This script generates the empirical data that is formally verified in:
- Diaspora/GaugeNegotiationVerified.lean (constraint matrix, optimal phases)
- Diaspora/GaugeNegotiationExplicit.lean (zero-sorry proof of emergent optimization)

The random seed (42) ensures deterministic reproduction of the verified data.
Running this script with seed=42 produces the exact constraint matrix C_initial
and optimal phases that are hard-coded in the Lean proofs.
"""

import numpy as np
import networkx as nx
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import copy
import random

# === Core Primitives ===

def compute_violation(G, frames, constraints):
    violation = 0
    for (i, j), desired in constraints.items():
        if not G.has_edge(i, j): continue
        actual = frames[j] - frames[i]
        diff = (actual - desired + np.pi) % (2*np.pi) - np.pi
        violation += diff**2
    return violation

def compute_all_external_violations(frames, jobs):
    violations_dict = {}
    total_weighted_violation = 0.0
    for job_name, job_params in jobs.items():
        in_node, out_node = job_params['in_node'], job_params['out_node']
        demand_phase, weight = job_params['demand_phase'], job_params['weight']
        actual_diff = frames.get(out_node, 0.0) - frames.get(in_node, 0.0)
        diff = (actual_diff - demand_phase + np.pi) % (2*np.pi) - np.pi
        v_ext = diff**2
        violations_dict[job_name] = v_ext
        total_weighted_violation += (weight * v_ext)
    return violations_dict, total_weighted_violation

def optimize_frames(G, constraints, num_nodes, anchor_node,
                    iterations=50, tolerance=1e-6):
    """The "Dumb Physics" Resolution Kernel (Unchanged)."""
    frames = {i: 0.0 for i in range(num_nodes)}
    in_neighbors = {i: [] for i in range(num_nodes)}
    out_neighbors = {i: [] for i in range(num_nodes)}
    for (i, j) in G.edges():
        if (i, j) in constraints:
            out_neighbors[i].append((j, constraints[(i, j)]))
            in_neighbors[j].append((i, constraints[(i, j)]))
    for _ in range(iterations):
        last_frames = frames.copy()
        max_change = 0.0
        for i in range(num_nodes):
            if i == anchor_node:
                frames[i] = 0.0
                continue
            votes = []
            for j, demand_ji in in_neighbors[i]: votes.append(frames[j] + demand_ji)
            for j, demand_ij in out_neighbors[i]: votes.append(frames[j] - demand_ij)
            if votes:
                avg_vote = np.angle(np.sum([np.exp(1j * v) for v in votes]))
                frames[i] = avg_vote
                max_change = max(max_change, np.abs(avg_vote - last_frames[i]))
        if max_change < tolerance: break
    final_v_internal = compute_violation(G, frames, constraints)
    return frames, final_v_internal

def compute_lagrangian(v_internal, weighted_v_external_total, num_edges, lambda_cost):
    return v_internal + weighted_v_external_total + (lambda_cost * num_edges)

# === GA Functions ===

def create_individual(nodes, C_initial, p_edge=0.5):
    G = nx.DiGraph()
    G.add_nodes_from(nodes)
    C = C_initial.copy()
    for i in nodes:
        for j in nodes:
            if i != j and random.random() < p_edge:
                G.add_edge(i, j)
    return G, C

def evaluate_population(population, C_initial, num_nodes, anchor_node, jobs, lambda_cost):
    pop_with_fitness = []
    for G, C in population:
        frames, v_int = optimize_frames(G, C, num_nodes, anchor_node)
        violations_dict, v_ext_total = compute_all_external_violations(frames, jobs)
        fitness = compute_lagrangian(v_int, v_ext_total, G.number_of_edges(), lambda_cost)
        pop_with_fitness.append((G, C, fitness, frames, v_int, v_ext_total, violations_dict))
    pop_with_fitness.sort(key=lambda x: x[2])
    return pop_with_fitness

def reproduce(parent1, parent2, C_initial, nodes, mutation_rate=0.1):
    G1, C1 = parent1
    G2, C2 = parent2
    G_child = nx.DiGraph()
    G_child.add_nodes_from(G1.nodes())
    G_child.add_edges_from(G1.edges())
    G_child.add_edges_from(G2.edges())
    C_child = C1.copy()
    if random.random() < mutation_rate:
        i, j = np.random.choice(nodes, 2, replace=False)
        if not G_child.has_edge(i, j): G_child.add_edge(i, j)
    if random.random() < mutation_rate:
        if G_child.number_of_edges() > 0:
            edge = random.choice(list(G_child.edges()))
            G_child.remove_edge(*edge)
    return G_child, C_child

def run_ga_evolution(initial_population, C_initial, num_nodes, lambda_cost, 
                     anchor_node, jobs, num_generations, pop_size, elite_size, verbose=True):
    """The core GA loop for finding a stable gauge lock."""
    if verbose:
        print(f"--- Running GA Evolution for λ = {lambda_cost:.4f} ---")
    
    population = copy.deepcopy(initial_population)
    
    for gen in range(num_generations):
        pop_with_fitness = evaluate_population(
            population, C_initial, num_nodes, anchor_node, jobs, lambda_cost
        )
        elite = pop_with_fitness[:elite_size]
        elite_graphs = [(G, C) for G, C, _, _, _, _, _ in elite]
        
        new_population = elite_graphs
        while len(new_population) < pop_size:
            parent1, parent2 = random.sample(elite_graphs, 2)
            child = reproduce(parent1, parent2, C_initial, list(range(num_nodes)))
            new_population.append(child)
        population = new_population
        
        if verbose and gen % 10 == 0:
            best_L, best_E = pop_with_fitness[0][2], pop_with_fitness[0][0].number_of_edges()
            print(f"  -> Gen {gen}: Best L={best_L:.4f}, Best E={best_E}")

    final_pop = evaluate_population(
        population, C_initial, num_nodes, anchor_node, jobs, lambda_cost
    )
    _G, _C, L, _F, V_int, V_ext, V_ext_dict = final_pop[0]
    
    if verbose:
        print(f"--- Evolution Complete. Final Best L={L:.4f} ---")
    
    # Returns: (Best Graph, Best Constraints)
    return final_pop[0][0], final_pop[0][1]

# === Plotting Function for Negotiation ===

def plot_negotiation_report(G_A, G_B, G_Negotiated, G_Initial, final_stats, lambda_cost):
    """
    Plots the three combatant graphs and the final negotiated result.
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 14))
    
    # Shared settings
    nodes = list(G_A.nodes())
    pos = nx.spring_layout(G_A, seed=42)
    job_nodes = {0: 'red', 1: 'yellow', 7: 'blue'}
    
    def draw_graph(ax, G, title, color_lambda=None):
        E = G.number_of_edges()
        color_map = [job_nodes.get(node, 'lightgray') for node in G.nodes()]
        
        nx.draw(G, pos, ax=ax, with_labels=True, node_color=color_map,
                node_size=800, font_size=12, arrows=True, arrowsize=15)
        
        title_full = f"{title} (E={E})"
        if color_lambda is not None:
            title_full += f" [λ={color_lambda:.1f}]"
            
        ax.set_title(title_full, fontweight='bold')
        ax.set_axis_off()

    # Top Left: Initial State
    draw_graph(axes[0, 0], G_Initial, "Initial Random Population")

    # Top Right: Singularity A (Rigid Conservator)
    draw_graph(axes[0, 1], G_A, "Singularity A (Rigid Conservator)", color_lambda=10.0)

    # Bottom Left: Singularity B (Adaptive Pragmatist)
    draw_graph(axes[1, 0], G_B, "Singularity B (Adaptive Pragmatist)", color_lambda=0.1)

    # Bottom Right: Final Negotiated Reality
    G_N = G_Negotiated
    stats = final_stats
    V_ext_total = stats['V_ext']
    
    draw_graph(axes[1, 1], G_N, f"Final Negotiated Reality (L={stats['L']:.2f})")
    
    # Add final stats overlay
    text_stats = (
        f"Final Edges: {G_N.number_of_edges()}\n"
        f"V_int (Holonomy): {stats['V_int']:.4f}\n"
        f"Job 1 (0->7) Error: {stats['V_ext_dict']['Job_1 (0->7)']:.4f}\n"
        f"Job 2 (1->7) Error: {stats['V_ext_dict']['Job_2 (1->7)']:.4f}"
    )
    axes[1, 1].text(0.5, -0.1, text_stats, transform=axes[1, 1].transAxes, 
                   ha='center', fontsize=10, bbox=dict(facecolor='white', alpha=0.8, edgecolor='black'))

    fig.suptitle(f"Gauge Lock Negotiation: Emergence of a New Reality (λ_Negotiation={lambda_cost:.1f})", fontsize=18, fontweight='bold')
    plt.tight_layout(rect=[0, 0.03, 1, 0.95])
    plt.savefig('gauge_negotiation_report.png', dpi=150)
    plt.close(fig)
    print(f"\n📊 Generated negotiation report: gauge_negotiation_report.png")

# === Main Experiment Runner ===

if __name__ == "__main__":
    
    # --- Define Job Realities ---
    # Job A (Simple): 0 -> 7 demand
    JOBS_A = {
        'Job_1 (0->7)': {'in_node': 0, 'out_node': 7, 'demand_phase': np.pi/2, 'weight': 50.0}
    }
    # Job B (Complex): 0 -> 7 AND 1 -> 7 demands
    JOBS_B = {
        'Job_1 (0->7)': {'in_node': 0, 'out_node': 7, 'demand_phase': np.pi/2, 'weight': 50.0},
        'Job_2 (1->7)': {'in_node': 1, 'out_node': 7, 'demand_phase': np.pi/4, 'weight': 50.0}
    }
    # Job Negotiation (Medium): 1 -> 7 demand
    JOBS_NEGOTIATION = {
        'Job_1 (0->7)': {'in_node': 0, 'out_node': 7, 'demand_phase': np.pi/2, 'weight': 50.0},
        'Job_2 (1->7)': {'in_node': 1, 'out_node': 7, 'demand_phase': np.pi/4, 'weight': 50.0}
    }
    
    # --- Define GA Parameters ---
    NUM_NODES = 8
    ANCHOR_NODE = 0
    POPULATION_SIZE = 50
    ELITE_SIZE = 10
    NUM_GENERATIONS_PRE_EVOLVE = 30
    NUM_GENERATIONS_NEGOTIATE = 40
    
    LAMBDA_A = 10.0 # Rigid Conservator
    LAMBDA_B = 0.1  # Adaptive Pragmatist
    LAMBDA_NEGOTIATION = 1.0 # Pragmatist Cost for negotiation

    # --- Setup Initial Constraints ---
    np.random.seed(42)
    random.seed(42)  # Also seed the random module for GA
    C_initial = {
        (i, j): np.random.uniform(-np.pi, np.pi)
        for i in range(NUM_NODES) for j in range(NUM_NODES) if i != j
    }

    # Output C_initial for Lean formalization
    print("\n" + "="*60)
    print("C_INITIAL CONSTRAINTS FOR LEAN (copy into GaugeNegotiationVerified.lean)")
    print("="*60)
    print("def C_initial (i j : Fin 8) : ℝ :=")
    print("  match (i.val, j.val) with")
    for (i, j), val in sorted(C_initial.items()):
        print(f"  | ({i}, {j}) => {val}")
    print("  | _ => 0.0  -- diagonal and self-loops")
    
    print("="*60)
    print("PHASE 1: PRE-EVOLUTION (Creating the Combatants)")
    print("==================================================")
    
    # --- Step 1: Evolve Singularity A (Rigid Conservator) ---
    G_A, C_A = run_ga_evolution(
        [create_individual(list(range(NUM_NODES)), C_initial, p_edge=0.5) for _ in range(POPULATION_SIZE)],
        C_initial, NUM_NODES, LAMBDA_A, ANCHOR_NODE, JOBS_A, NUM_GENERATIONS_PRE_EVOLVE, POPULATION_SIZE, ELITE_SIZE, verbose=True
    )
    print(f"-> G_A (Rigid) created: E={G_A.number_of_edges()}")

    # --- Step 2: Evolve Singularity B (Adaptive Pragmatist) ---
    G_B, C_B = run_ga_evolution(
        [create_individual(list(range(NUM_NODES)), C_initial, p_edge=0.5) for _ in range(POPULATION_SIZE)],
        C_initial, NUM_NODES, LAMBDA_B, ANCHOR_NODE, JOBS_B, NUM_GENERATIONS_PRE_EVOLVE, POPULATION_SIZE, ELITE_SIZE, verbose=True
    )
    print(f"-> G_B (Adaptive) created: E={G_B.number_of_edges()}")

    # --- PHASE 3: NEGOTIATION (Creating a New Reality) ---
    print("\n==================================================")
    print("PHASE 3: NEGOTIATION (Creating a New Reality)")
    print("==================================================")

    # --- Step 3: Initialize Negotiation Population ---
    # The population is created by "mating" G_A and G_B repeatedly.
    negotiation_population = []
    
    # Add a few copies of the originals
    negotiation_population.extend([(G_A, C_A) for _ in range(5)])
    negotiation_population.extend([(G_B, C_B) for _ in range(5)])
    
    # Fill the rest with children (Crossover)
    for _ in range(POPULATION_SIZE - 10):
        # Using a modified reproduce function (not the actual one above) to mate the combatants
        # For simplicity, we manually call the reproduce logic once.
        parent_A = (G_A, C_A)
        parent_B = (G_B, C_B)
        G_child = nx.DiGraph()
        G_child.add_nodes_from(G_A.nodes())
        G_child.add_edges_from(G_A.edges())
        G_child.add_edges_from(G_B.edges()) # Union of edges
        negotiation_population.append((G_child, C_A))
    
    print(f"-> Negotiation Population Initialized (Union of G_A + G_B).")
    
    # --- Step 4: Run the Final Negotiation GA ---
    G_Negotiated, C_Negotiated = run_ga_evolution(
        negotiation_population, C_initial, NUM_NODES, LAMBDA_NEGOTIATION, 
        ANCHOR_NODE, JOBS_NEGOTIATION, NUM_GENERATIONS_NEGOTIATE, POPULATION_SIZE, ELITE_SIZE, verbose=True
    )

    # --- Step 5: Get Final Stats for Plotting ---
    frames_final, v_int_final = optimize_frames(G_Negotiated, C_Negotiated, NUM_NODES, ANCHOR_NODE)
    v_ext_dict_final, v_ext_total_final = compute_all_external_violations(frames_final, JOBS_NEGOTIATION)
    L_final = compute_lagrangian(v_int_final, v_ext_total_final, G_Negotiated.number_of_edges(), LAMBDA_NEGOTIATION)
    
    final_stats = {
        'L': L_final,
        'V_int': v_int_final,
        'V_ext': v_ext_total_final,
        'V_ext_dict': v_ext_dict_final
    }

    # Create a simple initial graph for the plot (just the union)
    G_Initial_Plot = nx.DiGraph()
    G_Initial_Plot.add_nodes_from(G_A.nodes())
    G_Initial_Plot.add_edges_from(G_A.edges())
    G_Initial_Plot.add_edges_from(G_B.edges())

    # --- Step 6: Generate Report ---
    plot_negotiation_report(G_A, G_B, G_Negotiated, G_Initial_Plot, final_stats, LAMBDA_NEGOTIATION)
    
    print("\n" + "="*60)
    print("GAUGE LOCK NEGOTIATION COMPLETE.")
    print("Check 'gauge_negotiation_report.png' to see the final emergent reality.")
    print("="*60)

    # --- Output for Lean formalization ---
    print("\n" + "="*60)
    print("GRAPH EDGES FOR LEAN FORMALIZATION")
    print("="*60)
    print(f"\nG_A edges ({G_A.number_of_edges()} edges):")
    print(sorted(G_A.edges()))
    print(f"\nG_B edges ({G_B.number_of_edges()} edges):")
    print(sorted(G_B.edges()))
    print(f"\nG_Negotiated edges ({G_Negotiated.number_of_edges()} edges):")
    print(sorted(G_Negotiated.edges()))

    # Union graph
    G_Union = nx.DiGraph()
    G_Union.add_nodes_from(G_A.nodes())
    G_Union.add_edges_from(G_A.edges())
    G_Union.add_edges_from(G_B.edges())
    print(f"\nG_Union edges ({G_Union.number_of_edges()} edges):")
    print(sorted(G_Union.edges()))

    # Compute costs for all graphs under negotiation conditions
    print("\n" + "="*60)
    print("COSTS UNDER NEGOTIATION CONDITIONS (λ=1.0)")
    print("="*60)

    for name, G in [("G_A", G_A), ("G_B", G_B), ("G_N", G_Negotiated), ("G_Union", G_Union)]:
        frames, v_int = optimize_frames(G, C_initial, NUM_NODES, ANCHOR_NODE)
        v_ext_dict, v_ext = compute_all_external_violations(frames, JOBS_NEGOTIATION)
        L = compute_lagrangian(v_int, v_ext, G.number_of_edges(), LAMBDA_NEGOTIATION)
        print(f"\n{name}:")
        print(f"  E = {G.number_of_edges()}")
        print(f"  V_int = {v_int:.6f}")
        print(f"  V_ext = {v_ext:.6f}")
        print(f"  L = {L:.6f}")
        print(f"  Optimal frames: {[frames[i] for i in range(NUM_NODES)]}")
