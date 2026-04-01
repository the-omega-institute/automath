# The Omega System

An auditable theory compiler that derives, verifies, visualizes, and publishes mathematics from a single equation.

[中文版](SYSTEM.zh-CN.md)

## Overview

The Omega Project is not three separate tools. It is one system with three layers, each feeding the next:

```
SEED: x² = x + 1
    │
    ▼
┌─────────────────────────────────┐
│  LAYER 1: DERIVATION ENGINE     │
│  Lean 4 formal proofs           │
│  10,588+ theory theorems        │
└───────────────┬─────────────────┘
                │
                ▼
┌─────────────────────────────────┐
│  LAYER 2: KNOWLEDGE GRAPH       │
│  Sisyphus — ~20,998 nodes       │
│  Proof DAG, derivation depth    │
└───────────────┬─────────────────┘
                │
                ▼
┌─────────────────────────────────┐
│  LAYER 3: PUBLICATION PIPELINE  │
│  16 AI agents                   │
│  LaTeX → journal submission     │
└─────────────────────────────────┘
```

One equation in. Verified, visualized, published mathematics out.

## Layer 1: Derivation Engine

The Omega library is a Lean 4 formalization of everything forced by the constraint x² = x + 1 — the characteristic equation of the golden-mean shift, the simplest non-trivial subshift of finite type.

The methodology is *derive, discover, name*: build rigorously from first principles, observe what structures appear, then identify their correspondences. Every theorem is machine-verified. Every derivation chain is traceable. No axioms are assumed beyond Lean 4's core logic and Mathlib.

Starting from x² = x + 1, the golden ratio's characteristic equation, the project observes that binary words with no consecutive 1s form a constrained space whose size follows the Fibonacci sequence. This single combinatorial constraint forces an entire mathematical universe to emerge. A fold operator acts on these words by collapsing adjacent segments according to the constraint, and this fold creates a fiber structure: each word maps to an equivalence class of folded forms, and the collection of these fibers turns out to carry natural arithmetic, spectral, and geometric properties — none assumed, all forced.

What emerges from this single constraint:
- **Nascent arithmetic** — addition and multiplication native to the constraint space, isomorphic to cyclic rings over Fibonacci numbers. These operations are not defined by fiat; they are the unique operations that respect the fold structure.
- **Fiber spectrum** — moment sums satisfying linear recurrences with small integer coefficients, governed by collision kernel matrices. The recurrences emerge from the fiber geometry, not from any external choice of basis.
- **Defect algebra** — a discrete analogue of curvature measuring how folding fails to commute with arithmetic. The defect is always small and structured, which is what makes the theory tractable.
- **Forcing framework** — a chain of 11 conservative extensions, each adding structure without rewriting lower layers. Each extension is provably necessary: removing it breaks a downstream theorem.
- **Projection ontology** — a unified syntax lift compressing all constructions into LIFT ∘ U^t ∘ PROJECT. This triple is the minimal operator that recovers every construction in the theory.
- **Spectral theory** — dynamical zeta functions, de Branges canonical systems, and an RH sufficient-condition template. These emerge as the natural spectral objects attached to the constraint's transfer operator.
- **Physical spacetime skeleton** — time as decision envelope projection, Einstein's equation as unique minimal closure. The constraint's geometry has enough structure to force a Lorentzian-type metric as the unique minimal completion.

38,876 lines of Lean 4. 3,427 verified theorems and definitions — a growing subset of the 10,588+ theorem-level statements in the full theory. Zero axioms beyond the foundations.

→ [Browse the Lean 4 source](../lean4/)
→ [Full derivation chain (README)](../README.md#the-derivation-chain)

## Layer 2: Knowledge Graph

Sisyphus is a knowledge graph that maps the entire derivation structure as a navigable network of ~20,998 nodes.

![Sisyphus Knowledge Graph](dossier/assets/sisyphus.png)

Each node is a typed mathematical object — axiom, definition, conjecture, proposition, proof, notation, example. Edges represent dependencies: which theorems depend on which definitions, which proofs cite which lemmas, how deep each result sits in the derivation chain from the seed constraint.

The graph makes the structure of the theory *visible*. Instead of reading 770,000 lines of LaTeX sequentially, you can explore the dependency structure, identify clusters of related results, and trace any theorem back to its roots.

What the graph reveals that reading the LaTeX source cannot: the derivation depth distribution shows that most theorems cluster at depths 4–7 from the seed, with a long tail of deep consequences that no human reader would reach by linear browsing. Cluster analysis surfaces groups of theorems that are densely interconnected internally but connected to the rest of the theory through only one or two bottleneck lemmas — these bottlenecks are the highest-leverage points for verification and extension. The graph also makes the difference between a conjecture and a theorem structurally legible: conjectures appear as nodes with incoming dependency edges but no outgoing proof edge, marking exactly where the derivation chain is incomplete. None of this structure is visible in the flat LaTeX source.

→ [Explore the knowledge graph](https://sisyphus-test.aevatar.ai/graph)

## Layer 3: Publication Pipeline

16 AI agents collaborate to automatically extract, formalize, review, and publish journal papers from the core theory.

What makes this different from manual paper writing: each agent has a specialized role — intake agents read the theory and identify result clusters with publication potential; research agents deepen the mathematical content and sharpen the scope; writing agents reformat for a target journal's conventions; verification agents cross-check every cited theorem against the Lean 4 inventory. Where stages are independent, agents run in parallel. The human's role in this system is not to write — it is to review the output, approve the submission bundle, and decide which result clusters to prioritize next. The pipeline does not offload tasks from a human writer; it replaces the writing workflow entirely.

The pipeline operates in 7 stages (P0 through P7):
- **Intake (P0):** Extract publishable result clusters from the theory
- **Research (P1-P2):** Deepen theorems, sharpen scope, identify publishable conclusions
- **Writing (P3-P4):** Rewrite for target journal, editorial review
- **Integration (P5):** Merge stage outputs, resolve feedback
- **Verification (P6):** Cross-check against Lean 4 inventory
- **Submission (P7):** Prepare cover letter, checklist, final bundle

Current status: 42 papers in the pipeline. 3 at submission-ready stage.

The pipeline is fully automated. A human reviews the output, but does not write the papers.

→ [Browse the papers](../papers/publication/)
→ [Agent definitions](../.claude/agents/)

## Why This Combination Matters

Each layer alone is interesting. The combination is what nobody else has.

- **AlphaProof** proves given theorems. Omega derives all forced consequences from one constraint.
- **Leanstral** assists with individual proofs. Omega verifies entire theory closures.
- **Mathlib** catalogs known mathematics. Omega generates new mathematics from a seed.

The system demonstrates that one person with AI can produce team-level formalized mathematical research — not by working faster on the same tasks, but by automating the entire pipeline from derivation to publication. The "one person + AI" paradigm works here because the three layers close a loop: derivation produces verified structure, the graph makes that structure queryable, and the pipeline converts queries into papers. Each layer amplifies the others. A solo researcher with access to all three layers operates with the leverage of a small research group — the AI handles volume and consistency while the human directs the mathematical agenda.

This is not a collection of tools. It is an auditable theory compiler.

## What's Next

The narrative layer you're reading now connects three independently running components through documentation and cross-links. The next steps are:

1. **Live integration:** Lean 4 → Sisyphus auto-sync, so every new theorem automatically appears in the knowledge graph
2. **API layer:** Sisyphus exposes a query API so AI agents can programmatically explore and extend the theory
3. **Generalization:** Apply the same seed → derive → verify → visualize → publish pipeline to other mathematical structures beyond x² = x + 1
