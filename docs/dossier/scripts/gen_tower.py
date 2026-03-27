"""Generate the Fibonacci p-adic tower visualization."""
import graphviz

g = graphviz.Digraph('tower', format='svg')
g.attr(rankdir='BT', bgcolor='transparent', fontname='Helvetica')
g.attr('node', shape='ellipse', style='filled', fillcolor='#f8f9fa',
       fontname='Helvetica', fontsize='11', color='#dee2e6')
g.attr('edge', color='#6c757d', arrowsize='0.7', style='bold')

# Levels
levels = [
    ('x0', 'X₀\n|X₀| = F₂ = 1', '#e3f2fd'),
    ('x1', 'X₁\n|X₁| = F₃ = 2', '#e3f2fd'),
    ('x2', 'X₂\n|X₂| = F₄ = 3', '#e3f2fd'),
    ('x3', 'X₃\n|X₃| = F₅ = 5', '#e3f2fd'),
    ('x4', 'X₄\n|X₄| = F₆ = 8', '#e3f2fd'),
    ('dots', '⋮', '#ffffff'),
    ('xinf', 'X_∞ = lim X_m\nCompact, totally disconnected\nMetrizable, infinite',
     '#fff3cd'),
]

for nid, label, color in levels:
    if nid == 'dots':
        g.node(nid, label, shape='none', fillcolor='transparent', fontsize='16')
    elif nid == 'xinf':
        g.node(nid, label, fillcolor=color, color='#f0ad4e', penwidth='2',
               shape='box', style='rounded,filled')
    else:
        g.node(nid, label, fillcolor=color, color='#4a90d9')

# Edges (restriction maps)
edges = [('x1', 'x0'), ('x2', 'x1'), ('x3', 'x2'), ('x4', 'x3'),
         ('dots', 'x4'), ('xinf', 'dots')]
for src, dst in edges:
    g.edge(src, dst, label='  Φ  ' if dst != 'dots' and src != 'dots' and src != 'xinf' else '')

# Annotations
g.node('ann1', 'Ring homomorphisms\n(surjective, zero-preserving)',
       shape='note', fillcolor='#f8f9fa', fontsize='9', color='#dee2e6')
g.edge('ann1', 'x2', style='dashed', color='#adb5bd', arrowhead='none')

g.node('ann2', 'Analogous to\nZ_p = lim Z/p^nZ\n(p-adic integers)',
       shape='note', fillcolor='#f8f9fa', fontsize='9', color='#dee2e6')
g.edge('ann2', 'xinf', style='dashed', color='#adb5bd', arrowhead='none')

g.render('/Users/auric/automath/docs/dossier/figures/tower', cleanup=True)
print("Generated: figures/tower.svg")
