#!/usr/bin/env python3
"""
Diaspora Evolution Animator

Animates the genesis → vacuum transition with smooth interpolation.
"""

import json
import matplotlib.pyplot as plt
import matplotlib.animation as animation
import networkx as nx
import numpy as np

def load_simulation(filename="diaspora_evolution.json"):
    with open(filename) as f:
        return json.load(f)

def interpolate(v0, v1, t):
    """Smooth interpolation with easing"""
    # Ease-in-out cubic
    t = t * 2
    if t < 1:
        return v0 + (v1 - v0) * 0.5 * t * t * t
    t -= 2
    return v0 + (v1 - v0) * 0.5 * (t * t * t + 2)

def create_animation(data):
    states = data["states"]
    s0, s1 = states[0], states[1]

    # Animation parameters
    n_frames = 120
    fps = 30

    # Colors
    color_active = '#00ff88'
    color_breaking = '#ff3366'
    color_bg = '#0a0a0a'
    color_text = '#ffffff'

    # Create figure
    fig = plt.figure(figsize=(16, 10))
    fig.patch.set_facecolor(color_bg)
    gs = fig.add_gridspec(3, 2, hspace=0.45, wspace=0.3, top=0.82,
                          height_ratios=[2, 1.5, 1.5])

    # Graph axes (spanning both columns)
    ax_graph = fig.add_subplot(gs[0, :])
    ax_graph.set_facecolor(color_bg)

    # Physical quantities
    ax_phys = fig.add_subplot(gs[1, :])
    ax_phys.set_facecolor(color_bg)

    # Topological invariants
    ax_topo = fig.add_subplot(gs[2, :])
    ax_topo.set_facecolor(color_bg)

    # Graph positions (circular layout) - scaled up for visibility
    scale = 1.8
    pos = {0: (0, 1*scale), 1: (-0.866*scale, -0.5*scale), 2: (0.866*scale, -0.5*scale)}

    # Breaking edge
    breaking_edge = (1, 2)

    def init():
        for ax in [ax_graph, ax_phys, ax_topo]:
            ax.clear()
            ax.set_facecolor(color_bg)
        return []

    def animate(frame):
        # Calculate interpolation parameter (0 to 1)
        t = frame / (n_frames - 1)

        # Smooth step function for discrete transitions
        step = 1 if t > 0.5 else 0

        # Interpolate continuous values
        mass = interpolate(s0["mass"], s1["mass"], t)
        strain = interpolate(s0["strain_energy"], s1["strain_energy"], t)
        latent = interpolate(s0["latent_capacity"], s1["latent_capacity"], t)

        # Edge opacity (breaking animation)
        edge_alpha = max(0, 1 - 2*t)  # Fade out in first half

        # === GRAPH ===
        ax_graph.clear()
        ax_graph.set_facecolor(color_bg)

        # Draw all nodes (circular vertices)
        for i in range(3):
            circle = plt.Circle(pos[i], 0.22, color=color_active, zorder=3)
            ax_graph.add_patch(circle)
            ax_graph.text(pos[i][0], pos[i][1], str(i),
                         ha='center', va='center', fontsize=15,
                         fontweight='bold', color='black', zorder=4)

        # Draw active edges (match bottom graph linewidth)
        for edge in [(0, 1), (2, 0)]:
            i, j = edge
            ax_graph.plot([pos[i][0], pos[j][0]], [pos[i][1], pos[j][1]],
                         '-', color=color_active, linewidth=3, zorder=1,
                         solid_capstyle='round')

        # Draw breaking edge with fade
        if edge_alpha > 0:
            i, j = breaking_edge
            ax_graph.plot([pos[i][0], pos[j][0]], [pos[i][1], pos[j][1]],
                         '-', color=color_active, linewidth=3,
                         alpha=edge_alpha, zorder=1, solid_capstyle='round')
        else:
            # Show ghost edge
            i, j = breaking_edge
            ax_graph.plot([pos[i][0], pos[j][0]], [pos[i][1], pos[j][1]],
                         '--', color=color_breaking, linewidth=3,
                         alpha=0.3, zorder=0)

        # Phase indicator (moved to suptitle below, not as subplot title)

        # Info box
        info = f"Betti: {1 if t < 0.5 else 0}  |  "
        info += f"Satisfiable: {s0['satisfiable'] if t < 0.5 else s1['satisfiable']}\n"
        info += f"Winding: {s0['winding_number'] if t < 0.5 else 0}"
        ax_graph.text(0, -2.4, info, ha='center', fontsize=11,
                     color=color_text,
                     bbox=dict(boxstyle='round', facecolor=color_bg,
                              edgecolor=color_active, linewidth=2, pad=0.5))

        # Set equal aspect ratio for circular nodes
        ax_graph.set_xlim(-2.5, 2.5)
        ax_graph.set_ylim(-3.0, 2.5)
        ax_graph.set_aspect('equal', adjustable='box')
        ax_graph.axis('off')

        # === PHYSICAL QUANTITIES ===
        ax_phys.clear()
        ax_phys.set_facecolor(color_bg)

        # Plot as continuous lines with distinct styles
        t_history = np.linspace(0, t, 100)
        mass_history = [interpolate(s0["mass"], s1["mass"], ti)
                       for ti in t_history]
        strain_history = [interpolate(s0["strain_energy"], s1["strain_energy"], ti)
                         for ti in t_history]
        latent_history = [interpolate(s0["latent_capacity"], s1["latent_capacity"], ti)
                         for ti in t_history]

        # Add larger vertical offsets to make all three lines clearly visible
        mass_offset = 0.15
        strain_offset = -0.15

        # Draw all three lines with clear separation
        # Strain (dashed cyan) - slightly below actual value
        ax_phys.plot(t_history, [s + strain_offset for s in strain_history],
                    '--', color='#00ffff', linewidth=3, label='Strain Energy',
                    zorder=1, alpha=1.0, dashes=(10, 5))
        # Latent (dash-dot yellow) - at actual value
        ax_phys.plot(t_history, latent_history, '-.', color='#ffff00',
                    linewidth=3, label='Latent Capacity', zorder=2, alpha=1.0,
                    dashes=(15, 5, 3, 5))
        # Mass (solid pink/magenta) - slightly above actual value
        ax_phys.plot(t_history, [m + mass_offset for m in mass_history],
                    '-', color='#ff00ff', linewidth=3, label='Mass (‖γ‖²)',
                    zorder=3, alpha=1.0)

        # Current point markers
        ax_phys.plot(t, mass + mass_offset, 'o', color='#ff00ff', markersize=10,
                    markeredgecolor='white', markeredgewidth=2, zorder=10)
        ax_phys.plot(t, strain + strain_offset, 's', color='#00ffff', markersize=10,
                    markeredgecolor='white', markeredgewidth=2, zorder=10)
        ax_phys.plot(t, latent, '^', color='#ffff00', markersize=10,
                    markeredgecolor='white', markeredgewidth=2, zorder=10)

        ax_phys.set_xlabel('Time (normalized)', color=color_text,
                          fontsize=12, fontweight='bold')
        ax_phys.set_ylabel('Energy / Capacity', color=color_text,
                          fontsize=12, fontweight='bold')
        ax_phys.set_title('Physical Quantities Evolution',
                         color=color_text, fontsize=14, fontweight='bold')
        ax_phys.legend(facecolor=color_bg, edgecolor=color_active,
                      labelcolor=color_text, framealpha=0.9, loc='upper right')
        ax_phys.tick_params(colors=color_text)
        ax_phys.spines['bottom'].set_color(color_text)
        ax_phys.spines['left'].set_color(color_text)
        ax_phys.spines['top'].set_visible(False)
        ax_phys.spines['right'].set_visible(False)
        ax_phys.grid(True, alpha=0.2, color=color_text)
        ax_phys.set_xlim(-0.05, 1.05)
        ax_phys.set_ylim(-0.2, 3.5)

        # === TOPOLOGICAL INVARIANTS ===
        ax_topo.clear()
        ax_topo.set_facecolor(color_bg)

        # Step functions for discrete quantities
        winding_history = [s0["winding_number"] if ti < 0.5 else 0
                          for ti in t_history]
        betti_history = [1 if ti < 0.5 else 0 for ti in t_history]

        ax_topo.plot(t_history, winding_history, '-', color='#ff6b6b',
                    linewidth=3, label='Winding Number')
        ax_topo.plot(t_history, betti_history, '-', color='#4ecdc4',
                    linewidth=3, label='Betti Number (β₁)')

        # Current markers
        current_winding = s0["winding_number"] if t < 0.5 else 0
        current_betti = 1 if t < 0.5 else 0
        ax_topo.plot(t, current_winding, 'o', color='#ff6b6b',
                    markersize=10, markeredgecolor='white',
                    markeredgewidth=2, zorder=5)
        ax_topo.plot(t, current_betti, 's', color='#4ecdc4',
                    markersize=10, markeredgecolor='white',
                    markeredgewidth=2, zorder=5)

        ax_topo.set_xlabel('Time (normalized)', color=color_text,
                          fontsize=12, fontweight='bold', labelpad=12)
        ax_topo.set_ylabel('Topological Invariant', color=color_text,
                          fontsize=12, fontweight='bold')
        ax_topo.set_title('Topological Invariants (Quantized Defects)',
                         color=color_text, fontsize=14, fontweight='bold')
        ax_topo.legend(facecolor=color_bg, edgecolor=color_active,
                      labelcolor=color_text, framealpha=0.9, loc='upper right')
        ax_topo.tick_params(colors=color_text)
        ax_topo.spines['bottom'].set_color(color_text)
        ax_topo.spines['left'].set_color(color_text)
        ax_topo.spines['top'].set_visible(False)
        ax_topo.spines['right'].set_visible(False)
        ax_topo.grid(True, alpha=0.2, color=color_text)
        ax_topo.set_xlim(-0.05, 1.05)
        ax_topo.set_ylim(-0.5, 3.5)

        # Overall title with all four header lines
        phase = "GENESIS (Paradox)" if t < 0.5 else "VACUUM (Relaxed)"
        transition = ">>> EDGE BREAKING <<<" if 0.3 < t < 0.7 else ""

        title = 'DIASPORA: Genesis → Vacuum Transition\n'
        title += '"Matter is fossilized contradiction"\n\n'
        title += phase
        if transition:
            title += f'\n{transition}'

        fig.suptitle(title, fontsize=16, fontweight='bold', color=color_text, y=0.94)

        return []

    # Create animation
    anim = animation.FuncAnimation(fig, animate, init_func=init,
                                  frames=n_frames, interval=1000/fps,
                                  blit=True, repeat=True)

    # Save as gif and mp4
    print("Rendering animation (this may take a minute)...")
    anim.save('diaspora_evolution.gif', writer='pillow', fps=fps, dpi=100)
    print("✓ Saved animation to diaspora_evolution.gif")

    try:
        anim.save('diaspora_evolution.mp4', writer='ffmpeg', fps=fps, dpi=150,
                 extra_args=['-vcodec', 'libx264', '-pix_fmt', 'yuv420p'])
        print("✓ Saved animation to diaspora_evolution.mp4")
    except:
        print("⚠ ffmpeg not found, skipping mp4 (install with: sudo pacman -S ffmpeg)")

    plt.show()

if __name__ == "__main__":
    data = load_simulation()
    create_animation(data)
