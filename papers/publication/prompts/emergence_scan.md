# Emergence Scan — Reasoning Oracle Prompt

## Instructions

You are a mathematical research strategist. Given the current state of a large mathematical knowledge base (the "core paper"), identify opportunities for NEW results — theorems, derivation chains, or paper candidates that do not yet exist but are implied by the existing content.

## Core Paper Summary

**Sections and their key results:**

{SECTION_INVENTORY}

**Current publication papers extracted from this core:**

{PAPER_LIST}

## Tasks

### 1. Incomplete Derivation Chains

Identify places where the logical chain is broken:
- Theorem X cites "standard result" without proof — can we prove it?
- Lemma Y is used but never stated explicitly
- A corollary is expected but not written down

For each, give:
- Location (section, theorem label)
- What is missing
- Difficulty (easy / medium / hard)

### 2. Cross-Section Bridges

Find connections between different sections that could yield new results:
- Can technique from Section A solve a problem in Section B?
- Do two sections share a common structure that hasn't been exploited?
- Are there analogies (e.g., "X is to entropy what Y is to zeta functions")?

For each bridge:
- Source section → Target section
- Conjectured result (precise statement if possible)
- Evidence (why you think this works)

### 3. Generalizations

Existing results that are stated in a specific setting but should hold more generally:
- Specific parameter range → general range
- Specific algebraic structure → broader class
- Finite case → infinite case or vice versa

For each:
- Current statement (with its limitations)
- Proposed generalization
- Expected difficulty
- What would break if it fails (counterexample direction)

### 4. New Paper Candidates

Based on findings in 1-3, propose clusters of results that could form new publication papers:
- **Theme**: What unifies these results?
- **Results**: List of 3+ new/extended results
- **Target journal**: Where would this fit?
- **Novelty argument**: Why would a referee care?

## Output Format

Structured markdown with numbered items in each section. Be concrete — give mathematical statements, not vague descriptions. Each proposed result should be precise enough that a mathematician could attempt to prove it.
