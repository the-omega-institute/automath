"""Generate the derivation tree SVG showing what emerges from x^2 = x + 1."""
import graphviz

g = graphviz.Digraph('derivation', format='svg')
g.attr(rankdir='TB', bgcolor='transparent', fontname='Helvetica')
g.attr('node', shape='box', style='rounded,filled', fillcolor='#f8f9fa',
       fontname='Helvetica', fontsize='11', color='#dee2e6')
g.attr('edge', color='#6c757d', arrowsize='0.7')

# Seed
g.node('seed', 'x² = x + 1', fillcolor='#e3f2fd', color='#4a90d9',
       fontsize='14', penwidth='2')

# Level 1
g.node('shift', 'Golden-mean shift X_m\n(no consecutive 1s)')
g.node('fib', 'Fibonacci sequence\nF_n')
g.node('zeck', 'Zeckendorf bijection\nX_m ↔ {0,...,F_{m+2}-1}')

g.edge('seed', 'shift')
g.edge('seed', 'fib')
g.edge('shift', 'zeck')

# Level 2 - Algebra
g.node('ring', 'Ring isomorphism\nX_m ≅ Z/F_{m+2}Z', fillcolor='#fff3cd', color='#f0ad4e')
g.node('field', 'Fibonacci prime fields')
g.node('crt', 'CRT decomposition')

g.edge('zeck', 'ring')
g.edge('ring', 'field')
g.edge('ring', 'crt')

# Level 2 - Fibers
g.node('fold', 'Fold operator\nΦ: X_{m+1} → X_m')
g.node('moments', 'Moment sums S_q(m)', fillcolor='#fff3cd', color='#f0ad4e')
g.node('s2', 'S₂ recurrence\n(unconditional)', fillcolor='#d4edda', color='#28a745')
g.node('hankel', 'Hankel spectrum\nminimal order = 3')

g.edge('zeck', 'fold')
g.edge('fold', 'moments')
g.edge('moments', 's2')
g.edge('s2', 'hankel')

# Level 2 - Dynamics
g.node('entropy', 'Topological entropy\nh = log φ', fillcolor='#d4edda', color='#28a745')
g.node('transfer', 'Transfer matrix\nPerron-Frobenius')
g.node('orbits', 'Periodic orbits')

g.edge('shift', 'entropy')
g.edge('shift', 'transfer')
g.edge('transfer', 'orbits')

# Level 2 - Tower
g.node('tower', 'Modular tower\nX_{m+1} → X_m → ...')
g.node('invlim', 'Inverse limit X_∞\n(Fibonacci p-adics)', fillcolor='#fff3cd', color='#f0ad4e')
g.node('defect', 'Defect algebra\n(discrete curvature)')

g.edge('fold', 'tower')
g.edge('ring', 'tower')
g.edge('tower', 'invlim')
g.edge('tower', 'defect')

# Level 2 - Combinatorics
g.node('pathind', 'Path independent sets\n= F_{n+2}')
g.node('fibcube', 'Fibonacci cubes\n~510 theorems')

g.edge('shift', 'pathind')
g.edge('zeck', 'fibcube')

# Legend
with g.subgraph(name='cluster_legend') as c:
    c.attr(label='', style='invis')
    c.node('l1', 'Verified claim', fillcolor='#d4edda', color='#28a745',
           fontsize='9')
    c.node('l2', 'Key structure', fillcolor='#fff3cd', color='#f0ad4e',
           fontsize='9')
    c.node('l3', 'Derived result', fillcolor='#f8f9fa', color='#dee2e6',
           fontsize='9')

g.render('/Users/auric/automath/docs/dossier/figures/derivation-tree', cleanup=True)
print("Generated: figures/derivation-tree.svg")
