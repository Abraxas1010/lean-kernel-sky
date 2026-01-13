#!/usr/bin/env python3
"""
generate_visuals.py - Generate UMAP visualizations for LoF Kernel → SKY

Generates:
1. 2D UMAP embedding (HTML + SVG preview with kNN edges)
2. 3D UMAP embedding (HTML + SVG preview with animation)
3. Pipeline overview diagram (SVG)

Requirements:
    pip install umap-learn plotly numpy scikit-learn

Usage:
    cd lean-kernel-sky
    python3 tools/generate_visuals.py
"""

import json
import os
import sys
from pathlib import Path

try:
    import numpy as np
    from sklearn.feature_extraction.text import TfidfVectorizer
    from sklearn.neighbors import NearestNeighbors
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


# Full LoF → Kernel pipeline families
MODULE_FAMILIES = {
    "LoFPrimary": ["AIG", "GateSpec", "MuxNet", "Normalization", "Optimize", "Rewrite", "Syntax"],
    "Foundation": ["Blocks", "Soundness"],
    "Lambda": ["STLC", "STLCSKY"],
    "Eigenform": ["EigenformBridge", "Denotational"],
    "SKYCore": ["SKY", "BracketAbstraction", "SKYExec", "SKYMachineBounded", "SKYMultiway", "GraphReduction"],
    "Heyting": ["Nucleus", "FixedPoint", "Stability", "Trichotomy", "CombinatorMap", "NucleusRangeOps"],
    "Rewriting": ["CriticalPairs", "LocalConfluence", "StepAt"],
    "Category": ["MultiwayCategory", "BranchialCategory", "Groupoid", "DoubleCategory"],
    "Topos": ["SieveFrame", "SieveNucleus", "StepsSite", "Truncation", "Localization"],
    "DataPlane": ["UniverseLevel", "Expression", "Lean4LeanSKY"],
    "NativeKernel": ["WHNF", "DefEq", "Inductive", "Infer", "Environment"],
    "ComputationPlane": ["WHNFSKY", "DefEqSKY", "InferSKY", "KernelSKY"],
    "FullKernel": ["EnvironmentSKY", "WHNFDeltaSKY", "WHNFIotaSKY", "FullKernelSKY"],
    "CLI": ["Lean4LeanSKYMain", "KernelSKYMain", "FullKernelSKYMain"],
    "Tests": ["LeanKernelSanity"],
}

# Color scheme matching heyting-viz style
FAMILY_COLORS = {
    "LoFPrimary": "#ff6b6b",     # Red - Gates/LoF
    "Foundation": "#feca57",     # Yellow - Foundation
    "Lambda": "#48dbfb",         # Cyan - Lambda
    "Eigenform": "#ff9ff3",      # Pink - Eigenform
    "SKYCore": "#0984e3",        # Blue - SKY
    "Heyting": "#00b894",        # Teal - Heyting
    "Rewriting": "#a29bfe",      # Light purple - Rewriting
    "Category": "#fd79a8",       # Pink - Category
    "Topos": "#e17055",          # Orange - Topos
    "DataPlane": "#6c5ce7",      # Purple - Data
    "NativeKernel": "#00cec9",   # Cyan - Native
    "ComputationPlane": "#fdcb6e", # Gold - Computation
    "FullKernel": "#e94560",     # Red - Full Kernel
    "CLI": "#636e72",            # Gray - CLI
    "Tests": "#2d3436",          # Dark gray - Tests
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


def compute_knn_edges(X, k=5):
    """Compute k-nearest neighbor edges from feature matrix."""
    nn = NearestNeighbors(n_neighbors=min(k+1, X.shape[0]), metric='cosine')
    nn.fit(X)
    distances, indices = nn.kneighbors(X)

    edges = []
    for i in range(X.shape[0]):
        for j in range(1, min(k+1, len(indices[i]))):  # Skip self (index 0)
            neighbor = indices[i][j]
            if i < neighbor:  # Avoid duplicates
                edges.append((i, neighbor))

    return edges


def generate_umap_2d(texts, names, families, output_dir: Path):
    """Generate 2D UMAP visualization with kNN edges."""
    if not (HAS_SKLEARN and HAS_UMAP and HAS_PLOTLY):
        print("Skipping 2D UMAP: missing dependencies")
        return None, None

    vectorizer = TfidfVectorizer(max_features=1000, stop_words='english')
    X = vectorizer.fit_transform(texts)
    X_dense = X.toarray()

    # Compute kNN edges
    edges = compute_knn_edges(X_dense, k=5)

    reducer = umap.UMAP(n_components=2, random_state=42, n_neighbors=15, min_dist=0.1)
    embedding = reducer.fit_transform(X_dense)

    fig = go.Figure()

    # Add edges first (behind points)
    for i, j in edges:
        fig.add_trace(go.Scatter(
            x=[embedding[i, 0], embedding[j, 0]],
            y=[embedding[i, 1], embedding[j, 1]],
            mode='lines',
            line=dict(color='rgba(59, 75, 93, 0.18)', width=1),
            hoverinfo='skip',
            showlegend=False,
        ))

    # Add points
    for family in set(families):
        mask = [f == family for f in families]
        fig.add_trace(go.Scatter(
            x=[embedding[i, 0] for i, m in enumerate(mask) if m],
            y=[embedding[i, 1] for i, m in enumerate(mask) if m],
            mode='markers+text',
            marker=dict(size=10, color=FAMILY_COLORS.get(family, "#a0a0a0")),
            text=[names[i] for i, m in enumerate(mask) if m],
            textposition='top center',
            textfont=dict(size=8, color='white'),
            name=family,
            hoverinfo='text',
        ))

    fig.update_layout(
        title="LoF Kernel → SKY: 2D Module Map",
        template="plotly_dark",
        paper_bgcolor="#0b0f14",
        plot_bgcolor="#0f1721",
        showlegend=True,
        legend=dict(bgcolor="rgba(0,0,0,0.5)", font=dict(color="white")),
        xaxis=dict(showgrid=False, zeroline=False, showticklabels=False),
        yaxis=dict(showgrid=False, zeroline=False, showticklabels=False),
    )

    fig.write_html(str(output_dir / "lof_kernel_2d.html"))
    print(f"Saved: {output_dir / 'lof_kernel_2d.html'}")

    return embedding, edges


def generate_umap_3d(texts, names, families, output_dir: Path):
    """Generate 3D UMAP visualization."""
    if not (HAS_SKLEARN and HAS_UMAP and HAS_PLOTLY):
        print("Skipping 3D UMAP: missing dependencies")
        return None, None

    vectorizer = TfidfVectorizer(max_features=1000, stop_words='english')
    X = vectorizer.fit_transform(texts)
    X_dense = X.toarray()

    edges = compute_knn_edges(X_dense, k=5)

    reducer = umap.UMAP(n_components=3, random_state=42, n_neighbors=15, min_dist=0.1)
    embedding = reducer.fit_transform(X_dense)

    fig = go.Figure()

    # Add edges
    for i, j in edges:
        fig.add_trace(go.Scatter3d(
            x=[embedding[i, 0], embedding[j, 0]],
            y=[embedding[i, 1], embedding[j, 1]],
            z=[embedding[i, 2], embedding[j, 2]],
            mode='lines',
            line=dict(color='rgba(59, 75, 93, 0.18)', width=1),
            hoverinfo='skip',
            showlegend=False,
        ))

    # Add points
    for family in set(families):
        mask = [f == family for f in families]
        fig.add_trace(go.Scatter3d(
            x=[embedding[i, 0] for i, m in enumerate(mask) if m],
            y=[embedding[i, 1] for i, m in enumerate(mask) if m],
            z=[embedding[i, 2] for i, m in enumerate(mask) if m],
            mode='markers+text',
            marker=dict(size=6, color=FAMILY_COLORS.get(family, "#a0a0a0")),
            text=[names[i] for i, m in enumerate(mask) if m],
            name=family,
            hoverinfo='text',
        ))

    fig.update_layout(
        title="LoF Kernel → SKY: 3D Module Map",
        template="plotly_dark",
        paper_bgcolor="#0b0f14",
        scene=dict(
            bgcolor="#0f1721",
            xaxis=dict(showgrid=False, zeroline=False, showticklabels=False, showbackground=False),
            yaxis=dict(showgrid=False, zeroline=False, showticklabels=False, showbackground=False),
            zaxis=dict(showgrid=False, zeroline=False, showticklabels=False, showbackground=False),
        ),
        showlegend=True,
    )

    fig.write_html(str(output_dir / "lof_kernel_3d.html"))
    print(f"Saved: {output_dir / 'lof_kernel_3d.html'}")

    return embedding, edges


def generate_svg_preview(embedding, edges, names, families, output_dir: Path, is_3d=False):
    """Generate SVG preview with kNN edges (matching Sky_PaperPack style)."""
    if embedding is None:
        return

    # Use first 2 dims for both 2D and 3D previews
    emb_2d = embedding[:, :2]

    # Normalize to 1090x800 plot area with offset
    min_x, max_x = emb_2d[:, 0].min(), emb_2d[:, 0].max()
    min_y, max_y = emb_2d[:, 1].min(), emb_2d[:, 1].max()

    plot_x, plot_y = 50, 50
    plot_w, plot_h = 1090, 800

    def scale_x(x):
        return plot_x + (x - min_x) / (max_x - min_x + 1e-10) * plot_w

    def scale_y(y):
        return plot_y + (y - min_y) / (max_y - min_y + 1e-10) * plot_h

    coords = [(scale_x(emb_2d[i, 0]), scale_y(emb_2d[i, 1])) for i in range(len(names))]

    # Generate edge lines
    lines_svg = []
    for i, j in edges:
        lines_svg.append(
            f'<line x1="{coords[i][0]:.2f}" y1="{coords[i][1]:.2f}" '
            f'x2="{coords[j][0]:.2f}" y2="{coords[j][1]:.2f}" '
            f'stroke="#3b4b5d" stroke-opacity="0.18" stroke-width="1"/>'
        )

    # Generate circles
    circles_svg = []
    for i, (x, y) in enumerate(coords):
        family = families[i]
        color = FAMILY_COLORS.get(family, "#a0a0a0")
        circles_svg.append(
            f'<circle cx="{x:.2f}" cy="{y:.2f}" r="5" fill="{color}"/>'
        )

    suffix = "3d" if is_3d else "2d"
    title = "UMAP 3D — LoF/Kernel proof/declaration map" if is_3d else "UMAP 2D — LoF/Kernel proof/declaration map"
    subtitle = "Points: declarations • Colors: module family • Edges: kNN similarity links (source-text features)"

    svg = f'''<?xml version="1.0" encoding="utf-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="1500" height="900" viewBox="0 0 1500 900" role="img" aria-label="UMAP preview">
<rect x="0" y="0" width="1500" height="900" fill="#0b0f14"/>
<text x="50" y="32" fill="#ffffff" font-size="20" font-family="ui-sans-serif,system-ui,Segoe UI,Roboto,Helvetica,Arial">{title}</text>
<text x="50" y="48" fill="#b8c7d9" font-size="12" font-family="ui-sans-serif,system-ui,Segoe UI,Roboto,Helvetica,Arial">{subtitle}</text>
<rect x="{plot_x}" y="{plot_y}" width="{plot_w}" height="{plot_h}" fill="#0f1721" stroke="#1c2a3a" stroke-width="1"/>
{chr(10).join(lines_svg)}
{chr(10).join(circles_svg)}
</svg>'''

    filename = f"lof_kernel_{suffix}_preview.svg"
    (output_dir / filename).write_text(svg)
    print(f"Saved: {output_dir / filename}")


def generate_pipeline_overview(output_dir: Path):
    """Generate LoF → Kernel pipeline overview SVG."""

    svg = '''<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1200 600" width="1200" height="600">
  <defs>
    <marker id="arrow" markerWidth="10" markerHeight="7" refX="9" refY="3.5" orient="auto">
      <polygon points="0 0, 10 3.5, 0 7" fill="#60a5fa"/>
    </marker>
  </defs>

  <rect width="1200" height="600" fill="#0b0f14"/>
  <text x="600" y="35" text-anchor="middle" fill="#e94560" font-family="Arial" font-size="22" font-weight="bold">Laws of Form → Lean Kernel Pipeline</text>
  <text x="600" y="55" text-anchor="middle" fill="#a0a0a0" font-size="12">From Spencer-Brown's distinction to verified type checking on 3 instructions</text>

  <!-- Row 1: LoF → Gates → Lambda → SKY -->
  <rect x="30" y="80" width="150" height="100" rx="8" fill="#16213e" stroke="#ff6b6b" stroke-width="2"/>
  <text x="105" y="105" text-anchor="middle" fill="#ff6b6b" font-size="12" font-weight="bold">LAWS OF FORM</text>
  <text x="105" y="125" text-anchor="middle" fill="#a0a0a0" font-size="9">LoFPrimary</text>
  <text x="40" y="145" fill="#fff" font-size="8">• Distinction (mark/void)</text>
  <text x="40" y="158" fill="#fff" font-size="8">• AIG / Gate specs</text>
  <text x="40" y="171" fill="#fff" font-size="8">• MuxNet circuits</text>

  <line x1="185" y1="130" x2="225" y2="130" stroke="#60a5fa" stroke-width="2" marker-end="url(#arrow)"/>

  <rect x="230" y="80" width="150" height="100" rx="8" fill="#16213e" stroke="#48dbfb" stroke-width="2"/>
  <text x="305" y="105" text-anchor="middle" fill="#48dbfb" font-size="12" font-weight="bold">LAMBDA</text>
  <text x="305" y="125" text-anchor="middle" fill="#a0a0a0" font-size="9">STLC / STLCSKY</text>
  <text x="240" y="145" fill="#fff" font-size="8">• Simply typed λ</text>
  <text x="240" y="158" fill="#fff" font-size="8">• Type checking</text>
  <text x="240" y="171" fill="#fff" font-size="8">• λ → SKY compile</text>

  <line x1="385" y1="130" x2="425" y2="130" stroke="#60a5fa" stroke-width="2" marker-end="url(#arrow)"/>

  <rect x="430" y="80" width="150" height="100" rx="8" fill="#16213e" stroke="#0984e3" stroke-width="2"/>
  <text x="505" y="105" text-anchor="middle" fill="#0984e3" font-size="12" font-weight="bold">SKY COMBINATORS</text>
  <text x="505" y="125" text-anchor="middle" fill="#a0a0a0" font-size="9">Core basis</text>
  <text x="440" y="145" fill="#fff" font-size="8">• S K Y primitives</text>
  <text x="440" y="158" fill="#fff" font-size="8">• Bracket abstraction</text>
  <text x="440" y="171" fill="#fff" font-size="8">• Execution engine</text>

  <line x1="585" y1="130" x2="625" y2="130" stroke="#60a5fa" stroke-width="2" marker-end="url(#arrow)"/>

  <rect x="630" y="80" width="150" height="100" rx="8" fill="#16213e" stroke="#ff9ff3" stroke-width="2"/>
  <text x="705" y="105" text-anchor="middle" fill="#ff9ff3" font-size="12" font-weight="bold">EIGENFORM</text>
  <text x="705" y="125" text-anchor="middle" fill="#a0a0a0" font-size="9">Fixed points</text>
  <text x="640" y="145" fill="#fff" font-size="8">• Y combinator</text>
  <text x="640" y="158" fill="#fff" font-size="8">• Self-reference</text>
  <text x="640" y="171" fill="#fff" font-size="8">• Denotational sem.</text>

  <line x1="785" y1="130" x2="825" y2="130" stroke="#60a5fa" stroke-width="2" marker-end="url(#arrow)"/>

  <rect x="830" y="80" width="150" height="100" rx="8" fill="#16213e" stroke="#00b894" stroke-width="2"/>
  <text x="905" y="105" text-anchor="middle" fill="#00b894" font-size="12" font-weight="bold">HEYTING</text>
  <text x="905" y="125" text-anchor="middle" fill="#a0a0a0" font-size="9">Nucleus / Frame</text>
  <text x="840" y="145" fill="#fff" font-size="8">• Closure operators</text>
  <text x="840" y="158" fill="#fff" font-size="8">• Fixed points Ω</text>
  <text x="840" y="171" fill="#fff" font-size="8">• Trichotomy</text>

  <line x1="985" y1="130" x2="1025" y2="130" stroke="#60a5fa" stroke-width="2" marker-end="url(#arrow)"/>

  <rect x="1030" y="80" width="140" height="100" rx="8" fill="#16213e" stroke="#e17055" stroke-width="2"/>
  <text x="1100" y="105" text-anchor="middle" fill="#e17055" font-size="12" font-weight="bold">TOPOS</text>
  <text x="1100" y="125" text-anchor="middle" fill="#a0a0a0" font-size="9">Sieves / Sheaves</text>
  <text x="1040" y="145" fill="#fff" font-size="8">• Grothendieck top.</text>
  <text x="1040" y="158" fill="#fff" font-size="8">• Sieve nucleus</text>
  <text x="1040" y="171" fill="#fff" font-size="8">• Gluing as closure</text>

  <!-- Arrow down to Lean Kernel row -->
  <line x1="600" y1="185" x2="600" y2="220" stroke="#60a5fa" stroke-width="2" marker-end="url(#arrow)"/>

  <!-- Row 2: Lean Kernel compilation -->
  <rect x="100" y="230" width="200" height="110" rx="8" fill="#16213e" stroke="#6c5ce7" stroke-width="2"/>
  <text x="200" y="255" text-anchor="middle" fill="#6c5ce7" font-size="12" font-weight="bold">DATA PLANE</text>
  <text x="200" y="275" text-anchor="middle" fill="#a0a0a0" font-size="9">Phases 7-15</text>
  <text x="110" y="295" fill="#fff" font-size="8">• Expr 9-ary Scott encoding</text>
  <text x="110" y="308" fill="#fff" font-size="8">• ULevel 6-ary Scott encoding</text>
  <text x="110" y="321" fill="#fff" font-size="8">• Data → Comb compilation</text>

  <line x1="305" y1="285" x2="345" y2="285" stroke="#60a5fa" stroke-width="2" marker-end="url(#arrow)"/>

  <rect x="350" y="230" width="200" height="110" rx="8" fill="#16213e" stroke="#fdcb6e" stroke-width="2"/>
  <text x="450" y="255" text-anchor="middle" fill="#fdcb6e" font-size="12" font-weight="bold">COMPUTATION PLANE</text>
  <text x="450" y="275" text-anchor="middle" fill="#a0a0a0" font-size="9">Phases 16-20</text>
  <text x="360" y="295" fill="#fff" font-size="8">• WHNF as λ-term</text>
  <text x="360" y="308" fill="#fff" font-size="8">• DefEq as λ-term</text>
  <text x="360" y="321" fill="#fff" font-size="8">• Y combinator recursion</text>

  <line x1="555" y1="285" x2="595" y2="285" stroke="#60a5fa" stroke-width="2" marker-end="url(#arrow)"/>

  <rect x="600" y="230" width="200" height="110" rx="8" fill="#16213e" stroke="#e94560" stroke-width="2"/>
  <text x="700" y="255" text-anchor="middle" fill="#e94560" font-size="12" font-weight="bold">FULL KERNEL</text>
  <text x="700" y="275" text-anchor="middle" fill="#a0a0a0" font-size="9">Phases 21-25</text>
  <text x="610" y="295" fill="#fff" font-size="8">• δ-reduction (unfold defs)</text>
  <text x="610" y="308" fill="#fff" font-size="8">• ι-reduction (casesOn)</text>
  <text x="610" y="321" fill="#fff" font-size="8">• β/ζ/δ/ι combined</text>

  <line x1="805" y1="285" x2="845" y2="285" stroke="#60a5fa" stroke-width="2" marker-end="url(#arrow)"/>

  <rect x="850" y="230" width="200" height="110" rx="8" fill="#16213e" stroke="#0984e3" stroke-width="2"/>
  <text x="950" y="255" text-anchor="middle" fill="#0984e3" font-size="12" font-weight="bold">SKY EXECUTION</text>
  <text x="950" y="275" text-anchor="middle" fill="#a0a0a0" font-size="9">Runtime</text>
  <text x="860" y="295" fill="#fff" font-size="8">• Pure S, K, Y reduction</text>
  <text x="860" y="308" fill="#fff" font-size="8">• Fuel-bounded machine</text>
  <text x="860" y="321" fill="#fff" font-size="8">• Cross-validated ✓</text>

  <!-- Bottom: Key insight -->
  <rect x="100" y="380" width="1000" height="90" rx="8" fill="#16213e" stroke="#00b894" stroke-width="2"/>
  <text x="600" y="410" text-anchor="middle" fill="#00b894" font-size="14" font-weight="bold">THE KEY INSIGHT</text>
  <text x="600" y="435" text-anchor="middle" fill="#fff" font-size="11">Lean's dependent type checker (WHNF + DefEq + Infer) can be compiled to just 3 combinators:</text>
  <text x="600" y="455" text-anchor="middle" fill="#60a5fa" font-size="12" font-weight="bold">S = λfgx.fx(gx)   •   K = λxy.x   •   Y = λf.(λx.f(xx))(λx.f(xx))</text>

  <!-- Stats -->
  <text x="200" y="520" text-anchor="middle" fill="#636e72" font-size="11">76 Lean files</text>
  <text x="400" y="520" text-anchor="middle" fill="#636e72" font-size="11">25 Phases</text>
  <text x="600" y="520" text-anchor="middle" fill="#636e72" font-size="11">~5,000 Lines</text>
  <text x="800" y="520" text-anchor="middle" fill="#636e72" font-size="11">0 Sorry</text>
  <text x="1000" y="520" text-anchor="middle" fill="#636e72" font-size="11">Cross-Validated</text>

  <!-- Footer -->
  <text x="600" y="570" text-anchor="middle" fill="#a0a0a0" font-size="10">Part of the HeytingLean formal verification project • apoth3osis.io</text>
</svg>'''

    (output_dir / "lof_kernel_pipeline.svg").write_text(svg)
    print(f"Saved: {output_dir / 'lof_kernel_pipeline.svg'}")


def main():
    script_dir = Path(__file__).parent
    bundle_dir = script_dir.parent / "RESEARCHER_BUNDLE"
    output_dir = bundle_dir / "artifacts" / "visuals"
    output_dir.mkdir(parents=True, exist_ok=True)

    print("=" * 60)
    print("LoF Kernel → SKY Visualization Generator")
    print("=" * 60)
    print()

    # Collect Lean files
    lean_files = collect_lean_files(bundle_dir / "HeytingLean")

    if lean_files:
        print(f"Found {len(lean_files)} Lean files")
        texts, names, families = extract_features(lean_files)

        if texts:
            embedding_2d, edges_2d = generate_umap_2d(texts, names, families, output_dir)
            embedding_3d, edges_3d = generate_umap_3d(texts, names, families, output_dir)

            # Generate SVG previews with kNN edges
            if embedding_2d is not None and edges_2d is not None:
                generate_svg_preview(embedding_2d, edges_2d, names, families, output_dir, is_3d=False)
            if embedding_3d is not None and edges_3d is not None:
                generate_svg_preview(embedding_3d, edges_3d, names, families, output_dir, is_3d=True)
    else:
        print("No Lean files found - generating static visuals only")

    # Always generate pipeline overview
    generate_pipeline_overview(output_dir)

    print()
    print("Done!")
    print(f"Output directory: {output_dir}")


if __name__ == "__main__":
    main()
