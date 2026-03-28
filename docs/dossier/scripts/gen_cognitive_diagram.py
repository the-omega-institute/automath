"""Generate the cognitive division of labor diagram."""
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches

fig, ax = plt.subplots(1, 1, figsize=(10, 4))
ax.set_xlim(0, 10)
ax.set_ylim(0, 4)
ax.axis('off')

# Three boxes
boxes = [
    (0.5, 1.5, 2.5, 1.5, '#4a90d9', 'white', 'HUMAN\nDirection & Taste',
     '"Check if this has\nring structure"'),
    (3.75, 1.5, 2.5, 1.5, '#6c757d', 'white', 'AI\nSystematic Derivation',
     'Verify all axioms.\nBuild proof chains.\n25,000 lines of Lean 4.'),
    (7, 1.5, 2.5, 1.5, '#f0ad4e', 'black', 'HUMAN\nRecognition & Naming',
     '"This IS a cyclic ring.\nConnects to p-adics."'),
]

for x, y, w, h, color, tcolor, title, desc in boxes:
    rect = mpatches.FancyBboxPatch((x, y), w, h, boxstyle='round,pad=0.1',
                                    facecolor=color, edgecolor='none', alpha=0.9)
    ax.add_patch(rect)
    ax.text(x + w/2, y + h - 0.35, title, ha='center', va='top',
            fontsize=11, fontweight='bold', color=tcolor, fontfamily='sans-serif')
    ax.text(x + w/2, y + 0.3, desc, ha='center', va='bottom',
            fontsize=8, color=tcolor, fontfamily='sans-serif', alpha=0.85,
            style='italic')

# Arrows
arrow_props = dict(arrowstyle='->', color='#495057', lw=2,
                   connectionstyle='arc3,rad=0')
ax.annotate('', xy=(3.65, 2.25), xytext=(3.1, 2.25), arrowprops=arrow_props)
ax.annotate('', xy=(6.9, 2.25), xytext=(6.35, 2.25), arrowprops=arrow_props)

# Labels on arrows
ax.text(3.35, 2.65, 'DERIVE', ha='center', fontsize=9, color='#495057',
        fontweight='bold', fontfamily='sans-serif')
ax.text(6.6, 2.65, 'DISCOVER', ha='center', fontsize=9, color='#495057',
        fontweight='bold', fontfamily='sans-serif')

# "NAME" label at the end
ax.text(8.25, 3.35, 'NAME', ha='center', fontsize=9, color='#f0ad4e',
        fontweight='bold', fontfamily='sans-serif')

fig.savefig('/Users/auric/automath/docs/dossier/figures/cognitive-division.svg',
            format='svg', bbox_inches='tight', transparent=True, dpi=150)
plt.close()
print("Generated: figures/cognitive-division.svg")
