# P2 Research Extension — Reasoning Oracle Prompt

## Instructions

You are a mathematical research consultant performing a deep analysis of a paper targeted at a specific journal. Your task is to assess novelty, identify gaps, and recommend scope decisions.

## Context

**Paper title:** {TITLE}
**Target journal:** {JOURNAL}
**MSC codes:** {MSC}

### Theorem Inventory

{THEOREM_TABLE}

### Paper structure

{SECTION_SUMMARY}

## Tasks

### 1. Novelty Assessment

For each theorem in the inventory, rate:
- **Novelty**: HIGH (genuinely new) / MEDIUM (new formulation of known ideas) / LOW (standard/folklore)
- **One-line justification** citing the closest antecedent if any

### 2. Gap Analysis

List every mathematical gap, proof gap, or expository gap. For each:
- **ID**: G1, G2, ...
- **Description**: What is missing or incomplete
- **Severity**: BLOCKER / MEDIUM / LOW
- **Suggested fix**: How to close the gap (proof sketch, reference, or explanation)

### 3. Scope Decisions

Recommend which sections/results to:
- **KEEP**: Essential for the paper's coherence
- **CUT**: Outside the target journal's scope or not adding enough
- **DEFER**: Interesting but better suited for a sequel

### 4. Escalation Ladder

Describe the logical escalation: what is the main thread that makes this paper more than a collection of results? How does Theorem A lead to Theorem B, and so on?

### 5. Competing Literature

List 3-5 most relevant competing or related papers, with:
- Full citation
- How our paper differs or extends their work

## Output Format

Return your analysis as structured markdown with sections matching the tasks above. Use tables where appropriate. Be specific — cite theorem labels, section numbers, and exact mathematical statements.
