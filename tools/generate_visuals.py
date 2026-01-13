#!/usr/bin/env python3
"""
generate_visuals.py - Generate UMAP visualizations for Lean Kernel → SKY

Generates:
1. 2D UMAP embedding (HTML + SVG preview with connection lines)
2. 3D UMAP embedding (HTML + SVG preview)
3. Pipeline overview diagram (SVG)
4. Phase dependency graph (SVG)

Requirements:
    pip install umap-learn plotly numpy scikit-learn

Usage:
    cd lean-kernel-sky
    python3 tools/generate_visuals.py
"""

import json
import os
import sys
import random
from pathlib import Path

try:
    import numpy as np
    from sklearn.feature_extraction.text import TfidfVectorizer
    HAS_SKLEARN = True
except ImportError:
    HAS_SKLEARN = False
    print("Warning: scikit-learn not installed. Install with: pip install scikit-learn")

try:
    import umap
    HAS_UMAP = True
except ImportError:
    HAS_UMAP = False
    print("Warning: umap-learn not installed. Install with: pip install umap-learn")

try:
    import plotly.graph_objects as go
    HAS_PLOTLY = True
except ImportError:
    HAS_PLOTLY = False
    print("Warning: plotly not installed. Install with: pip install plotly")


# LeanKernel phase families for coloring
MODULE_FAMILIES = {
    "DataPlane": ["UniverseLevel", "Expression", "Lean4LeanSKY", "Lean4LeanSKYMain"],
    "NativeKernel": ["WHNF", "DefEq", "Inductive", "Infer", "Environment"],
    "ComputationPlane": ["WHNFSKY", "DefEqSKY", "InferSKY", "KernelSKY", "KernelSKYMain"],
    "FullKernel": ["EnvironmentSKY", "WHNFDeltaSKY", "WHNFIotaSKY", "FullKernelSKY", "FullKernelSKYMain"],
    "Combinators": ["SKY", "BracketAbstraction", "SKYExec", "SKYMachineBounded", "Denotational", "GraphReduction"],
    "Foundation": ["Blocks", "Soundness"],
    "Tests": ["LeanKernelSanity"],
}

# Color scheme matching heyting-viz style (dark theme)
FAMILY_COLORS = {
    "DataPlane": "#6c5ce7",      # Purple
    "NativeKernel": "#00b894",   # Teal
    "ComputationPlane": "#e17055", # Orange
    "FullKernel": "#e94560",     # Red/Pink
    "Combinators": "#0984e3",    # Blue
    "Foundation": "#fd79a8",     # Pink
    "Tests": "#636e72",          # Gray
    "Other": "#a0a0a0",
}


def get_family(module_name: str) -> str:
    """Determine the family for a module name."""
    for family, modules in MODULE_FAMILIES.items():
        for mod in modules:
            if mod in module_name:
                return family
    return "Other"


def collect_lean_files(root_dir: Path) -> list:
    """Collect all .lean files."""
    lean_files = []
    for lean_file in root_dir.rglob("*.lean"):
        if ".lake" not in str(lean_file):
            lean_files.append(lean_file)
    return lean_files


def extract_features(lean_files: list) -> tuple:
    """Extract text features from Lean files."""
    texts = []
    names = []
    families = []

    for f in lean_files:
        try:
            content = f.read_text(encoding='utf-8')
            texts.append(content)
            name = f.stem
            names.append(name)
            families.append(get_family(name))
        except Exception as e:
            print(f"Warning: Could not read {f}: {e}")

    return texts, names, families


def generate_umap_2d(texts, names, families, output_dir: Path):
    """Generate 2D UMAP visualization."""
    if not (HAS_SKLEARN and HAS_UMAP and HAS_PLOTLY):
        print("Skipping 2D UMAP: missing dependencies")
        return None

    vectorizer = TfidfVectorizer(max_features=1000, stop_words='english')
    X = vectorizer.fit_transform(texts)

    reducer = umap.UMAP(n_components=2, random_state=42, n_neighbors=10, min_dist=0.1)
    embedding = reducer.fit_transform(X.toarray())

    fig = go.Figure()

    for family in set(families):
        mask = [f == family for f in families]
        fig.add_trace(go.Scatter(
            x=[embedding[i, 0] for i, m in enumerate(mask) if m],
            y=[embedding[i, 1] for i, m in enumerate(mask) if m],
            mode='markers+text',
            marker=dict(size=12, color=FAMILY_COLORS.get(family, "#a0a0a0")),
            text=[names[i] for i, m in enumerate(mask) if m],
            textposition='top center',
            textfont=dict(size=9, color='white'),
            name=family,
            hoverinfo='text',
        ))

    fig.update_layout(
        title="Lean Kernel → SKY: 2D Module Map",
        template="plotly_dark",
        paper_bgcolor="#0b0f14",
        plot_bgcolor="#0b0f14",
        showlegend=True,
        legend=dict(
            bgcolor="rgba(0,0,0,0.5)",
            font=dict(color="white")
        ),
    )

    fig.write_html(str(output_dir / "kernel_2d.html"))
    print(f"Saved: {output_dir / 'kernel_2d.html'}")

    return embedding


def generate_umap_3d(texts, names, families, output_dir: Path):
    """Generate 3D UMAP visualization."""
    if not (HAS_SKLEARN and HAS_UMAP and HAS_PLOTLY):
        print("Skipping 3D UMAP: missing dependencies")
        return None

    vectorizer = TfidfVectorizer(max_features=1000, stop_words='english')
    X = vectorizer.fit_transform(texts)

    reducer = umap.UMAP(n_components=3, random_state=42, n_neighbors=10, min_dist=0.1)
    embedding = reducer.fit_transform(X.toarray())

    fig = go.Figure()

    for family in set(families):
        mask = [f == family for f in families]
        fig.add_trace(go.Scatter3d(
            x=[embedding[i, 0] for i, m in enumerate(mask) if m],
            y=[embedding[i, 1] for i, m in enumerate(mask) if m],
            z=[embedding[i, 2] for i, m in enumerate(mask) if m],
            mode='markers+text',
            marker=dict(size=8, color=FAMILY_COLORS.get(family, "#a0a0a0")),
            text=[names[i] for i, m in enumerate(mask) if m],
            name=family,
            hoverinfo='text',
        ))

    fig.update_layout(
        title="Lean Kernel → SKY: 3D Module Map",
        template="plotly_dark",
        paper_bgcolor="#0b0f14",
        scene=dict(bgcolor="#0b0f14"),
        showlegend=True,
    )

    fig.write_html(str(output_dir / "kernel_3d.html"))
    print(f"Saved: {output_dir / 'kernel_3d.html'}")

    return embedding


def generate_data_driven_preview(embedding, names, families, output_dir: Path, is_3d=False):
    """Generate data-driven SVG preview with connection lines like GenerativeStack."""

    if embedding is None:
        return

    # Normalize coordinates to fit in viewbox
    min_x, max_x = embedding[:, 0].min(), embedding[:, 0].max()
    min_y, max_y = embedding[:, 1].min(), embedding[:, 1].max()

    # Scale to 800x600 with padding
    padding = 40
    width, height = 800, 600

    def scale_x(x):
        return padding + (x - min_x) / (max_x - min_x) * (width - 2*padding)

    def scale_y(y):
        return padding + (y - min_y) / (max_y - min_y) * (height - 2*padding)

    coords = [(scale_x(embedding[i, 0]), scale_y(embedding[i, 1])) for i in range(len(names))]

    # Generate connection lines (random subset of edges)
    random.seed(42)
    lines_svg = []
    for i in range(len(names)):
        # Connect to 2-3 nearby points
        for j in range(i+1, min(i+4, len(names))):
            if random.random() < 0.3:  # 30% chance of edge
                lines_svg.append(
                    f'    <line x1="{coords[i][0]:.1f}" y1="{coords[i][1]:.1f}" '
                    f'x2="{coords[j][0]:.1f}" y2="{coords[j][1]:.1f}"/>'
                )

    # Generate circles
    circles_svg = []
    for i, (x, y) in enumerate(coords):
        family = families[i]
        color = FAMILY_COLORS.get(family, "#a0a0a0")
        opacity = 0.7 + random.random() * 0.3
        radius = 8 + random.random() * 4
        circles_svg.append(
            f'  <circle cx="{x:.1f}" cy="{y:.1f}" r="{radius:.1f}" fill="{color}" opacity="{opacity:.2f}"/>'
        )

    suffix = "3d" if is_3d else "2d"
    title = "3D Module Map" if is_3d else "2D Module Map"

    svg = f'''<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}">
  <rect width="{width}" height="{height}" fill="#0b0f14"/>
  <text x="{width//2}" y="25" text-anchor="middle" fill="#e94560" font-family="Arial" font-size="16" font-weight="bold">{title}</text>

  <!-- Connection lines -->
  <g stroke="rgba(207,216,220,0.25)" stroke-width="0.5">
{chr(10).join(lines_svg)}
  </g>

  <!-- Module points -->
{chr(10).join(circles_svg)}

  <!-- Legend -->
  <g transform="translate(20, {height - 100})">
    <rect x="0" y="0" width="12" height="12" fill="#6c5ce7"/><text x="18" y="10" fill="#a0a0a0" font-size="9">DataPlane</text>
    <rect x="0" y="18" width="12" height="12" fill="#00b894"/><text x="18" y="28" fill="#a0a0a0" font-size="9">NativeKernel</text>
    <rect x="100" y="0" width="12" height="12" fill="#e17055"/><text x="118" y="10" fill="#a0a0a0" font-size="9">ComputationPlane</text>
    <rect x="100" y="18" width="12" height="12" fill="#e94560"/><text x="118" y="28" fill="#a0a0a0" font-size="9">FullKernel</text>
    <rect x="230" y="0" width="12" height="12" fill="#0984e3"/><text x="248" y="10" fill="#a0a0a0" font-size="9">Combinators</text>
    <rect x="230" y="18" width="12" height="12" fill="#fd79a8"/><text x="248" y="28" fill="#a0a0a0" font-size="9">Foundation</text>
  </g>

  <text x="{width//2}" y="{height - 15}" text-anchor="middle" fill="#60a5fa" font-family="Arial" font-size="10">Click to open interactive view</text>
</svg>'''

    filename = f"kernel_{suffix}_preview.svg"
    (output_dir / filename).write_text(svg)
    print(f"Saved: {output_dir / filename}")


def generate_pipeline_overview(output_dir: Path):
    """Generate pipeline overview SVG."""

    svg = '''<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 900 400" width="900" height="400">
  <defs>
    <marker id="arrowhead" markerWidth="10" markerHeight="7" refX="9" refY="3.5" orient="auto">
      <polygon points="0 0, 10 3.5, 0 7" fill="#60a5fa"/>
    </marker>
  </defs>

  <rect width="900" height="400" fill="#0b0f14"/>
  <text x="450" y="30" text-anchor="middle" fill="#e94560" font-family="Arial" font-size="18" font-weight="bold">Lean Kernel → SKY Pipeline</text>

  <!-- Phase boxes -->
  <!-- Data Plane -->
  <rect x="30" y="60" width="180" height="120" rx="8" fill="#16213e" stroke="#6c5ce7" stroke-width="2"/>
  <text x="120" y="85" text-anchor="middle" fill="#6c5ce7" font-family="Arial" font-size="12" font-weight="bold">DATA PLANE</text>
  <text x="120" y="105" text-anchor="middle" fill="#a0a0a0" font-size="10">Phases 7-15</text>
  <text x="40" y="125" fill="#fff" font-size="9">• Expr 9-ary Scott</text>
  <text x="40" y="140" fill="#fff" font-size="9">• ULevel 6-ary Scott</text>
  <text x="40" y="155" fill="#fff" font-size="9">• Bracket abstraction</text>
  <text x="40" y="170" fill="#fff" font-size="9">• Data → Comb</text>

  <!-- Arrow -->
  <line x1="215" y1="120" x2="255" y2="120" stroke="#60a5fa" stroke-width="2" marker-end="url(#arrowhead)"/>

  <!-- Computation Plane -->
  <rect x="260" y="60" width="180" height="120" rx="8" fill="#16213e" stroke="#e17055" stroke-width="2"/>
  <text x="350" y="85" text-anchor="middle" fill="#e17055" font-family="Arial" font-size="12" font-weight="bold">COMPUTATION PLANE</text>
  <text x="350" y="105" text-anchor="middle" fill="#a0a0a0" font-size="10">Phases 16-20</text>
  <text x="270" y="125" fill="#fff" font-size="9">• WHNF as λ-term</text>
  <text x="270" y="140" fill="#fff" font-size="9">• DefEq as λ-term</text>
  <text x="270" y="155" fill="#fff" font-size="9">• Infer as λ-term</text>
  <text x="270" y="170" fill="#fff" font-size="9">• Y combinator recursion</text>

  <!-- Arrow -->
  <line x1="445" y1="120" x2="485" y2="120" stroke="#60a5fa" stroke-width="2" marker-end="url(#arrowhead)"/>

  <!-- Full Kernel -->
  <rect x="490" y="60" width="180" height="120" rx="8" fill="#16213e" stroke="#e94560" stroke-width="2"/>
  <text x="580" y="85" text-anchor="middle" fill="#e94560" font-family="Arial" font-size="12" font-weight="bold">FULL KERNEL</text>
  <text x="580" y="105" text-anchor="middle" fill="#a0a0a0" font-size="10">Phases 21-25</text>
  <text x="500" y="125" fill="#fff" font-size="9">• Environment encoding</text>
  <text x="500" y="140" fill="#fff" font-size="9">• δ-reduction</text>
  <text x="500" y="155" fill="#fff" font-size="9">• ι-reduction</text>
  <text x="500" y="170" fill="#fff" font-size="9">• β/ζ/δ/ι combined</text>

  <!-- Arrow -->
  <line x1="675" y1="120" x2="715" y2="120" stroke="#60a5fa" stroke-width="2" marker-end="url(#arrowhead)"/>

  <!-- SKY Execution -->
  <rect x="720" y="60" width="150" height="120" rx="8" fill="#16213e" stroke="#0984e3" stroke-width="2"/>
  <text x="795" y="85" text-anchor="middle" fill="#0984e3" font-family="Arial" font-size="12" font-weight="bold">SKY EXECUTION</text>
  <text x="795" y="105" text-anchor="middle" fill="#a0a0a0" font-size="10">Runtime</text>
  <text x="730" y="125" fill="#fff" font-size="9">• S K Y only</text>
  <text x="730" y="140" fill="#fff" font-size="9">• Fuel-bounded</text>
  <text x="730" y="155" fill="#fff" font-size="9">• Cross-validated</text>
  <text x="730" y="170" fill="#fff" font-size="9">• FPGA-ready</text>

  <!-- Bottom: reduction forms -->
  <rect x="30" y="220" width="840" height="80" rx="8" fill="#16213e" stroke="#00b894" stroke-width="2"/>
  <text x="450" y="245" text-anchor="middle" fill="#00b894" font-family="Arial" font-size="14" font-weight="bold">REDUCTION FORMS</text>

  <text x="120" y="275" text-anchor="middle" fill="#6c5ce7" font-size="11" font-weight="bold">β</text>
  <text x="120" y="290" text-anchor="middle" fill="#a0a0a0" font-size="9">(λx.M) N → M[N/x]</text>

  <text x="300" y="275" text-anchor="middle" fill="#e17055" font-size="11" font-weight="bold">ζ</text>
  <text x="300" y="290" text-anchor="middle" fill="#a0a0a0" font-size="9">let x := N in M → M[N/x]</text>

  <text x="500" y="275" text-anchor="middle" fill="#e94560" font-size="11" font-weight="bold">δ</text>
  <text x="500" y="290" text-anchor="middle" fill="#a0a0a0" font-size="9">const c → body</text>

  <text x="700" y="275" text-anchor="middle" fill="#0984e3" font-size="11" font-weight="bold">ι</text>
  <text x="700" y="290" text-anchor="middle" fill="#a0a0a0" font-size="9">casesOn (Cᵢ args) → branchᵢ</text>

  <!-- Bottom stats -->
  <text x="120" y="360" text-anchor="middle" fill="#636e72" font-size="10">25 Phases</text>
  <text x="300" y="360" text-anchor="middle" fill="#636e72" font-size="10">~2,200 Lines</text>
  <text x="500" y="360" text-anchor="middle" fill="#636e72" font-size="10">0 Sorry</text>
  <text x="700" y="360" text-anchor="middle" fill="#636e72" font-size="10">Cross-Validated ✓</text>
</svg>'''

    (output_dir / "pipeline_overview.svg").write_text(svg)
    print(f"Saved: {output_dir / 'pipeline_overview.svg'}")


def generate_phase_dependencies(output_dir: Path):
    """Generate phase dependency graph SVG."""

    svg = '''<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 700 500" width="700" height="500">
  <defs>
    <marker id="arrow" markerWidth="8" markerHeight="6" refX="7" refY="3" orient="auto">
      <polygon points="0 0, 8 3, 0 6" fill="#60a5fa"/>
    </marker>
  </defs>

  <rect width="700" height="500" fill="#0b0f14"/>
  <text x="350" y="25" text-anchor="middle" fill="#e94560" font-family="Arial" font-size="16" font-weight="bold">Phase Dependencies</text>

  <!-- Row 1: Data Plane -->
  <g transform="translate(50, 50)">
    <rect width="50" height="30" rx="4" fill="#6c5ce7"/>
    <text x="25" y="20" text-anchor="middle" fill="white" font-size="10">P7</text>
  </g>
  <g transform="translate(120, 50)">
    <rect width="50" height="30" rx="4" fill="#6c5ce7"/>
    <text x="25" y="20" text-anchor="middle" fill="white" font-size="10">P8</text>
  </g>
  <g transform="translate(190, 50)">
    <rect width="50" height="30" rx="4" fill="#00b894"/>
    <text x="25" y="20" text-anchor="middle" fill="white" font-size="10">P9</text>
  </g>
  <g transform="translate(260, 50)">
    <rect width="50" height="30" rx="4" fill="#00b894"/>
    <text x="25" y="20" text-anchor="middle" fill="white" font-size="10">P10</text>
  </g>
  <g transform="translate(330, 50)">
    <rect width="50" height="30" rx="4" fill="#00b894"/>
    <text x="25" y="20" text-anchor="middle" fill="white" font-size="10">P11</text>
  </g>
  <g transform="translate(400, 50)">
    <rect width="50" height="30" rx="4" fill="#00b894"/>
    <text x="25" y="20" text-anchor="middle" fill="white" font-size="10">P12</text>
  </g>
  <g transform="translate(470, 50)">
    <rect width="50" height="30" rx="4" fill="#00b894"/>
    <text x="25" y="20" text-anchor="middle" fill="white" font-size="10">P13</text>
  </g>
  <g transform="translate(540, 50)">
    <rect width="50" height="30" rx="4" fill="#6c5ce7"/>
    <text x="25" y="20" text-anchor="middle" fill="white" font-size="10">P14</text>
  </g>
  <g transform="translate(610, 50)">
    <rect width="50" height="30" rx="4" fill="#6c5ce7"/>
    <text x="25" y="20" text-anchor="middle" fill="white" font-size="10">P15</text>
  </g>

  <!-- Arrows Row 1 -->
  <line x1="100" y1="65" x2="118" y2="65" stroke="#60a5fa" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="170" y1="65" x2="188" y2="65" stroke="#60a5fa" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="240" y1="65" x2="258" y2="65" stroke="#60a5fa" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="310" y1="65" x2="328" y2="65" stroke="#60a5fa" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="380" y1="65" x2="398" y2="65" stroke="#60a5fa" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="450" y1="65" x2="468" y2="65" stroke="#60a5fa" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="520" y1="65" x2="538" y2="65" stroke="#60a5fa" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="590" y1="65" x2="608" y2="65" stroke="#60a5fa" stroke-width="1.5" marker-end="url(#arrow)"/>

  <!-- Row 2: Computation Plane -->
  <g transform="translate(120, 150)">
    <rect width="50" height="30" rx="4" fill="#e17055"/>
    <text x="25" y="20" text-anchor="middle" fill="white" font-size="10">P16</text>
  </g>
  <g transform="translate(220, 150)">
    <rect width="50" height="30" rx="4" fill="#e17055"/>
    <text x="25" y="20" text-anchor="middle" fill="white" font-size="10">P17</text>
  </g>
  <g transform="translate(320, 150)">
    <rect width="50" height="30" rx="4" fill="#e17055"/>
    <text x="25" y="20" text-anchor="middle" fill="white" font-size="10">P18</text>
  </g>
  <g transform="translate(420, 150)">
    <rect width="50" height="30" rx="4" fill="#e17055"/>
    <text x="25" y="20" text-anchor="middle" fill="white" font-size="10">P19</text>
  </g>
  <g transform="translate(520, 150)">
    <rect width="50" height="30" rx="4" fill="#e17055"/>
    <text x="25" y="20" text-anchor="middle" fill="white" font-size="10">P20</text>
  </g>

  <!-- Arrows Row 1→2 -->
  <line x1="145" y1="80" x2="145" y2="148" stroke="#60a5fa" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="215" y1="80" x2="235" y2="148" stroke="#60a5fa" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="285" y1="80" x2="325" y2="148" stroke="#60a5fa" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="425" y1="80" x2="365" y2="148" stroke="#60a5fa" stroke-width="1.5" marker-end="url(#arrow)"/>

  <!-- Arrows Row 2 horizontal -->
  <line x1="170" y1="165" x2="218" y2="165" stroke="#60a5fa" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="270" y1="165" x2="318" y2="165" stroke="#60a5fa" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="370" y1="165" x2="418" y2="165" stroke="#60a5fa" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="470" y1="165" x2="518" y2="165" stroke="#60a5fa" stroke-width="1.5" marker-end="url(#arrow)"/>

  <!-- Row 3: Full Kernel -->
  <g transform="translate(120, 250)">
    <rect width="50" height="30" rx="4" fill="#e94560"/>
    <text x="25" y="20" text-anchor="middle" fill="white" font-size="10">P21</text>
  </g>
  <g transform="translate(220, 250)">
    <rect width="50" height="30" rx="4" fill="#e94560"/>
    <text x="25" y="20" text-anchor="middle" fill="white" font-size="10">P22</text>
  </g>
  <g transform="translate(320, 250)">
    <rect width="50" height="30" rx="4" fill="#e94560"/>
    <text x="25" y="20" text-anchor="middle" fill="white" font-size="10">P23</text>
  </g>
  <g transform="translate(420, 250)">
    <rect width="50" height="30" rx="4" fill="#e94560"/>
    <text x="25" y="20" text-anchor="middle" fill="white" font-size="10">P24</text>
  </g>
  <g transform="translate(520, 250)">
    <rect width="50" height="30" rx="4" fill="#e94560"/>
    <text x="25" y="20" text-anchor="middle" fill="white" font-size="10">P25</text>
  </g>

  <!-- Arrows Row 2→3 -->
  <line x1="445" y1="180" x2="145" y2="248" stroke="#60a5fa" stroke-width="1.5" marker-end="url(#arrow)"/>

  <!-- Arrows Row 3 horizontal -->
  <line x1="170" y1="265" x2="218" y2="265" stroke="#60a5fa" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="270" y1="265" x2="318" y2="265" stroke="#60a5fa" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="370" y1="265" x2="418" y2="265" stroke="#60a5fa" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="470" y1="265" x2="518" y2="265" stroke="#60a5fa" stroke-width="1.5" marker-end="url(#arrow)"/>

  <!-- Legend -->
  <g transform="translate(50, 350)">
    <rect width="15" height="15" fill="#6c5ce7"/>
    <text x="25" y="12" fill="white" font-size="10">Data Plane (7-8, 14-15)</text>
  </g>
  <g transform="translate(200, 350)">
    <rect width="15" height="15" fill="#00b894"/>
    <text x="25" y="12" fill="white" font-size="10">Native Kernel (9-13)</text>
  </g>
  <g transform="translate(370, 350)">
    <rect width="15" height="15" fill="#e17055"/>
    <text x="25" y="12" fill="white" font-size="10">Computation Plane (16-20)</text>
  </g>
  <g transform="translate(550, 350)">
    <rect width="15" height="15" fill="#e94560"/>
    <text x="25" y="12" fill="white" font-size="10">Full Kernel (21-25)</text>
  </g>

  <!-- Phase descriptions -->
  <text x="50" y="420" fill="#636e72" font-size="9">P7: ULevel  P8: Expr  P9: WHNF  P10: DefEq  P11: Inductive  P12: Infer  P13: Environment  P14: Lean4LeanSKY  P15: Demo</text>
  <text x="50" y="440" fill="#636e72" font-size="9">P16: WHNFSKY  P17: DefEqSKY  P18: InferSKY  P19: KernelSKY  P20: Demo</text>
  <text x="50" y="460" fill="#636e72" font-size="9">P21: EnvironmentSKY  P22: WHNFDeltaSKY  P23: WHNFIotaSKY  P24: FullKernelSKY  P25: Demo</text>
</svg>'''

    (output_dir / "phase_dependencies.svg").write_text(svg)
    print(f"Saved: {output_dir / 'phase_dependencies.svg'}")


def main():
    script_dir = Path(__file__).parent
    bundle_dir = script_dir.parent / "RESEARCHER_BUNDLE"
    output_dir = bundle_dir / "artifacts" / "visuals"
    output_dir.mkdir(parents=True, exist_ok=True)

    print("=" * 60)
    print("Lean Kernel → SKY Visualization Generator")
    print("=" * 60)
    print()

    # Collect Lean files
    lean_files = collect_lean_files(bundle_dir / "HeytingLean")

    embedding_2d = None
    embedding_3d = None

    if lean_files:
        print(f"Found {len(lean_files)} Lean files")
        texts, names, families = extract_features(lean_files)

        if texts:
            embedding_2d = generate_umap_2d(texts, names, families, output_dir)
            embedding_3d = generate_umap_3d(texts, names, families, output_dir)

            # Generate data-driven previews
            if embedding_2d is not None:
                generate_data_driven_preview(embedding_2d, names, families, output_dir, is_3d=False)
            if embedding_3d is not None:
                generate_data_driven_preview(embedding_3d[:, :2], names, families, output_dir, is_3d=True)
    else:
        print("No Lean files found - generating static visuals only")

    # Always generate static SVGs
    generate_pipeline_overview(output_dir)
    generate_phase_dependencies(output_dir)

    print()
    print("Done!")
    print(f"Output directory: {output_dir}")


if __name__ == "__main__":
    main()
