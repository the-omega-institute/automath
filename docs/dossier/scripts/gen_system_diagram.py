"""Generate the three-layer system architecture diagram."""
import graphviz

g = graphviz.Digraph('system', format='svg')
g.attr(rankdir='TB', bgcolor='transparent', fontname='Helvetica',
       nodesep='0.6', ranksep='0.8')
g.attr('node', shape='box', style='rounded,filled', fillcolor='#f8f9fa',
       fontname='Helvetica', fontsize='11', color='#dee2e6', margin='0.3,0.15')
g.attr('edge', color='#6c757d', arrowsize='0.8', style='bold', penwidth='1.5')

# Seed
g.node('seed', 'x² = x + 1', shape='ellipse', fillcolor='white',
       color='#343a40', penwidth='2.5', fontsize='14', fontname='Helvetica-Bold')

# Layer 1
g.node('layer1', 'DERIVATION ENGINE\nLean 4 formal proofs\n10,588+ theorems · zero axioms',
       fillcolor='#e3f2fd', color='#4a90d9', penwidth='2', fontsize='11')

# Layer 2
g.node('layer2', 'KNOWLEDGE GRAPH\nSisyphus · ~20,998 nodes\nProof DAG · derivation depth',
       fillcolor='#fff3cd', color='#f0ad4e', penwidth='2', fontsize='11')

# Layer 3
g.node('layer3', 'PUBLICATION PIPELINE\n16 AI agents\nLaTeX → journal papers',
       fillcolor='#d4edda', color='#28a745', penwidth='2', fontsize='11')

# Edges
g.edge('seed', 'layer1', label='  derive  ', fontsize='9', fontcolor='#6c757d')
g.edge('layer1', 'layer2', label='  visualize  ', fontsize='9', fontcolor='#6c757d')
g.edge('layer2', 'layer3', label='  publish  ', fontsize='9', fontcolor='#6c757d')

g.render('/Users/auric/automath/docs/dossier/figures/system', cleanup=True)
print("Generated: figures/system.svg")
