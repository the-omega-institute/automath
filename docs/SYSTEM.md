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
│  10,588+ theorems, zero axioms  │
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

What emerges from this single constraint:
- **Nascent arithmetic** — addition and multiplication native to the constraint space, isomorphic to cyclic rings over Fibonacci numbers
- **Fiber spectrum** — moment sums satisfying linear recurrences with small integer coefficients, governed by collision kernel matrices
- **Defect algebra** — a discrete analogue of curvature measuring how folding fails to commute with arithmetic
- **Forcing framework** — a chain of 11 conservative extensions, each adding structure without rewriting lower layers
- **Projection ontology** — a unified syntax lift compressing all constructions into LIFT ∘ U^t ∘ PROJECT
- **Spectral theory** — dynamical zeta functions, de Branges canonical systems, and an RH sufficient-condition template
- **Physical spacetime skeleton** — time as decision envelope projection, Einstein's equation as unique minimal closure

38,876 lines of Lean 4. 3,427 verified theorems and definitions. Zero axioms beyond the foundations.

→ [Browse the Lean 4 source](../lean4/)
→ [Full derivation chain (README)](../README.md#the-derivation-chain)

## Layer 2: Knowledge Graph

Sisyphus is a knowledge graph that maps the entire derivation structure as a navigable network of ~20,998 nodes.

![Sisyphus Knowledge Graph](dossier/assets/sisyphus.png)

Each node is a typed mathematical object — axiom, definition, conjecture, proposition, proof, notation, example. Edges represent dependencies: which theorems depend on which definitions, which proofs cite which lemmas, how deep each result sits in the derivation chain from the seed constraint.

The graph makes the structure of the theory *visible*. Instead of reading 770,000 lines of LaTeX sequentially, you can explore the dependency structure, identify clusters of related results, and trace any theorem back to its roots.

→ [Explore the knowledge graph](https://sisyphus-test.aevatar.ai/graph)

## Layer 3: Publication Pipeline

16 AI agents collaborate to automatically extract, formalize, review, and publish journal papers from the core theory.

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

The system demonstrates that one person with AI can produce team-level formalized mathematical research — not by working faster on the same tasks, but by automating the entire pipeline from derivation to publication.

This is not a collection of tools. It is an auditable theory compiler.

## What's Next

The narrative layer you're reading now connects three independently running components through documentation and cross-links. The next steps are:

1. **Live integration:** Lean 4 → Sisyphus auto-sync, so every new theorem automatically appears in the knowledge graph
2. **API layer:** Sisyphus exposes a query API so AI agents can programmatically explore and extend the theory
3. **Generalization:** Apply the same seed → derive → verify → visualize → publish pipeline to other mathematical structures beyond x² = x + 1
