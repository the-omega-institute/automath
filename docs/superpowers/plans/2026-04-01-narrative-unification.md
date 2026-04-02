# Narrative Unification Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Unify Lean 4 proofs, Sisyphus knowledge graph, and automated publication pipeline into one coherent narrative — the "auditable theory compiler."

**Architecture:** Documentation-only changes. No code, no pipeline modifications, no Sisyphus backend work. Four deliverables: docs/SYSTEM.md (three-layer architecture narrative), README "The System" section, cross-component links, and consistent one-sentence positioning.

**Tech Stack:** Markdown, Git. Sisyphus screenshot already exists at `docs/dossier/assets/sisyphus.png`.

**Design doc:** `~/.gstack/projects/the-omega-institute-automath/auric-feature/improve-repo-design-20260401-201154.md`

---

## File Map

- **Create:** `docs/SYSTEM.md` — Three-layer system architecture narrative (~1500 words, English)
- **Create:** `docs/SYSTEM.zh-CN.md` — Chinese version of the system narrative
- **Modify:** `README.md:1` — Update title line to include positioning
- **Modify:** `README.md:248-249` — Insert "The System" section after Derivation Chain
- **Modify:** `README.md:250-257` — Add cross-links in Publication Pipeline section
- **Modify:** `README.zh-CN.md:1` — Update title line to include positioning
- **Modify:** `README.zh-CN.md:248-249` — Insert Chinese "The System" section
- **Modify:** `README.zh-CN.md:250-257` — Add cross-links in Chinese Publication Pipeline section

---

### Task 1: Create docs/SYSTEM.md — Three-Layer Architecture Narrative

**Files:**
- Create: `docs/SYSTEM.md`

This is the core deliverable. A standalone document that explains the Omega system as one coherent whole. A first-time reader should be able to describe all three layers and their connections after reading this alone.

- [ ] **Step 1: Write docs/SYSTEM.md**

Write the file with this structure (all content in English, per project convention for .md files):

```markdown
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

→ [Browse the Lean 4 source](lean4/)
→ [Full derivation chain (README)](README.md#the-derivation-chain)

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

→ [Browse the papers](papers/publication/)
→ [Agent definitions](.claude/agents/)

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
```

- [ ] **Step 2: Verify the file reads well**

Read back `docs/SYSTEM.md` and check:
- All three layers described with what they do and how they connect
- Links point to correct paths (lean4/, papers/publication/, .claude/agents/)
- Screenshot path `dossier/assets/sisyphus.png` is correct relative to docs/
- No placeholder text, no "TBD"
- Standalone test: could a reader describe all three layers without browsing lean4/ or theory/?

- [ ] **Step 3: Commit**

```bash
git add docs/SYSTEM.md
git commit -m "docs: add three-layer system architecture narrative"
```

---

### Task 2: Create docs/SYSTEM.zh-CN.md — Chinese Version

**Files:**
- Create: `docs/SYSTEM.zh-CN.md`

Chinese translation of docs/SYSTEM.md. Per CLAUDE.md: working language is Chinese, .md docs are in English, but Chinese versions use `.zh-CN.md` suffix.

- [ ] **Step 1: Write docs/SYSTEM.zh-CN.md**

Translate the full content of docs/SYSTEM.md into Chinese. Keep the same structure, same diagram (ASCII art stays in English), same links. The title becomes:

```markdown
# Omega 系统

一个可审计的理论编译器，从单一方程出发，推导、验证、可视化并发表数学。

[English](SYSTEM.md)
```

All section headers in Chinese. All prose in Chinese. Code blocks, file paths, and proper nouns (Lean 4, Mathlib, Sisyphus, AlphaProof, Leanstral) stay in English.

- [ ] **Step 2: Commit**

```bash
git add docs/SYSTEM.zh-CN.md
git commit -m "docs: add Chinese version of system architecture narrative"
```

---

### Task 3: Update README.md — Add "The System" Section and One-Sentence Positioning

**Files:**
- Modify: `README.md:1` — title line
- Modify: `README.md:248-249` — insert after Derivation Chain

- [ ] **Step 1: Update the title line with one-sentence positioning**

Change line 1 of README.md from:

```markdown
# The Omega Project
```

to:

```markdown
# The Omega Project

> An auditable theory compiler that derives, verifies, visualizes, and publishes mathematics from a single equation.
```

- [ ] **Step 2: Insert "The System" section after the Derivation Chain**

After line 248 (`Every arrow is a formally verified derivation step...`), insert:

```markdown

## The System

The Omega Project is one system with three layers:

```
SEED: x² = x + 1
    │
    ▼
┌─────────────────────────────────┐
│  LAYER 1: DERIVATION ENGINE     │
│  Lean 4 — 10,588+ theorems      │
│  Zero axioms, machine-verified  │
└───────────────┬─────────────────┘
                │
                ▼
┌─────────────────────────────────┐
│  LAYER 2: KNOWLEDGE GRAPH       │
│  Sisyphus — ~20,998 nodes       │
│  Theorem dependencies & depth   │
└───────────────┬─────────────────┘
                │
                ▼
┌─────────────────────────────────┐
│  LAYER 3: PUBLICATION PIPELINE  │
│  16 AI agents → journal papers  │
└─────────────────────────────────┘
```

One equation in. Verified, visualized, published mathematics out.

![Sisyphus Knowledge Graph](docs/dossier/assets/sisyphus.png)

→ [Full system architecture](docs/SYSTEM.md) · [Explore the knowledge graph](https://sisyphus-test.aevatar.ai/graph) · [Browse the papers](papers/publication/)
```

- [ ] **Step 3: Verify rendering**

Read back the modified README.md. Check:
- The blockquote positioning line renders correctly after the title
- The system diagram ASCII art is intact
- The image path `docs/dossier/assets/sisyphus.png` is correct from repo root
- Links point to correct targets
- Section appears between "The Derivation Chain" and "The Publication Pipeline"

- [ ] **Step 4: Commit**

```bash
git add README.md
git commit -m "docs: add system architecture section and one-sentence positioning to README"
```

---

### Task 4: Update README.zh-CN.md — Chinese Version of System Section

**Files:**
- Modify: `README.zh-CN.md:1` — title line
- Modify: `README.zh-CN.md:248-249` — insert after Derivation Chain

- [ ] **Step 1: Update the title line**

Change line 1 from:

```markdown
# Omega 项目
```

to:

```markdown
# Omega 项目

> 一个可审计的理论编译器，从单一方程出发，推导、验证、可视化并发表数学。
```

- [ ] **Step 2: Insert Chinese "The System" section**

After the derivation chain closing text (line ~248), insert:

```markdown

## 系统架构

Omega 项目是一个包含三层的统一系统：

```
种子: x² = x + 1
    │
    ▼
┌─────────────────────────────────┐
│  第一层：推导引擎               │
│  Lean 4 — 10,588+ 条定理        │
│  零公理，机器验证               │
└───────────────┬─────────────────┘
                │
                ▼
┌─────────────────────────────────┐
│  第二层：知识图谱               │
│  Sisyphus — ~20,998 个节点      │
│  定理依赖关系与推导深度         │
└───────────────┬─────────────────┘
                │
                ▼
┌─────────────────────────────────┐
│  第三层：出版管线               │
│  16 个 AI 智能体 → 期刊论文     │
└─────────────────────────────────┘
```

一个方程输入。经过验证、可视化、发表的数学输出。

![Sisyphus 知识图谱](docs/dossier/assets/sisyphus.png)

→ [完整系统架构](docs/SYSTEM.zh-CN.md) · [探索知识图谱](https://sisyphus-test.aevatar.ai/graph) · [浏览论文](papers/publication/)
```

- [ ] **Step 3: Commit**

```bash
git add README.zh-CN.md
git commit -m "docs: add system architecture section and positioning to Chinese README"
```

---

### Task 5: Add Cross-Links to Publication Pipeline Sections

**Files:**
- Modify: `README.md:250-257` — Publication Pipeline section
- Modify: `README.zh-CN.md:250-257` — Chinese Publication Pipeline section

- [ ] **Step 1: Add cross-link to English Publication Pipeline section**

In README.md, after the Publication Pipeline section's current status line (`Current status: 42 papers in the pipeline...`), add:

```markdown

→ [How the system works end-to-end](docs/SYSTEM.md#layer-3-publication-pipeline)
```

- [ ] **Step 2: Add cross-link to Chinese Publication Pipeline section**

In README.zh-CN.md, after the corresponding status line, add:

```markdown

→ [系统端到端工作原理](docs/SYSTEM.zh-CN.md#第三层出版管线)
```

- [ ] **Step 3: Commit**

```bash
git add README.md README.zh-CN.md
git commit -m "docs: add cross-links from publication pipeline to system architecture"
```

---

### Task 6: Final Verification

- [ ] **Step 1: Verify all links work**

Check that all referenced files exist:
```bash
ls docs/SYSTEM.md docs/SYSTEM.zh-CN.md docs/dossier/assets/sisyphus.png README.md README.zh-CN.md papers/publication/
```

- [ ] **Step 2: Verify one-sentence positioning consistency**

Grep for the positioning statement to ensure it appears in all public-facing docs:
```bash
grep -l "auditable theory compiler" docs/SYSTEM.md README.md
grep -l "可审计的理论编译器" docs/SYSTEM.zh-CN.md README.zh-CN.md
```

Expected: all four files match.

- [ ] **Step 3: Verify no broken image paths**

```bash
grep -n "!\[" README.md README.zh-CN.md docs/SYSTEM.md docs/SYSTEM.zh-CN.md
```

Check each image reference points to an existing file.

- [ ] **Step 4: Read the README from top to verify flow**

Read README.md from line 1 to verify:
- Title + positioning blockquote
- Sections I-XV (unchanged)
- Derivation Chain (unchanged)
- **New: "The System" section** with diagram, screenshot, and links
- Publication Pipeline (with new cross-link)
- Project Structure, Status, Build, etc. (unchanged)

Confirm a new visitor would understand within 60 seconds that this is one system.
