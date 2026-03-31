# Proof Strategy — Reasoning Oracle Prompt

## Instructions

You are a mathematician specializing in {FIELD}. A gap has been identified in a paper under preparation. Suggest concrete proof strategies to close this gap.

## Gap Description

**Paper:** {TITLE}
**Gap ID:** {GAP_ID}
**Location:** {LOCATION}

### Statement of the gap

{GAP_DESCRIPTION}

### Current state

{CURRENT_STATE}

### What we have

{AVAILABLE_TOOLS}

### What we need

{TARGET_STATEMENT}

## Tasks

### 1. Direct Approaches

List 2-3 proof strategies that could close this gap directly. For each:
- **Strategy name** (e.g., "spectral decomposition", "Banach fixed point", "compactness argument")
- **Sketch** (3-5 sentences outlining the key steps)
- **Difficulty estimate** (easy / medium / hard)
- **Required prerequisites** (what tools or results are needed)

### 2. Reduction

Can this gap be reduced to a known result? If so:
- State the known result precisely
- Show how our gap reduces to it
- Provide a reference

### 3. Counterexample Risk

Is there a reason this gap might NOT be closable? If so:
- Describe the obstacle
- Suggest a weaker statement that IS provable

## Output Format

Structured markdown with numbered strategies. Include mathematical notation where helpful. Be specific enough that a working mathematician could implement the strategy.
