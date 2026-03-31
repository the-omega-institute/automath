# Literature Search — Reasoning Oracle Prompt

## Instructions

You are a mathematical literature expert. Given the theorem statements and mathematical context below, identify the most relevant competing and related work. Focus on papers from the last 10 years, but include foundational references where essential.

## Context

**Paper topic:** {TOPIC}
**Target journal:** {JOURNAL}
**Key mathematical objects:** {KEY_OBJECTS}

### Main Results

{THEOREM_STATEMENTS}

## Tasks

### 1. Direct Antecedents

Papers that prove results closest to ours. For each:
- Full citation (authors, title, journal, year, DOI if available)
- Which of our results it is closest to
- How our result differs (stronger, more general, different proof technique, etc.)

### 2. Methodological Relatives

Papers using similar techniques but for different objects:
- Full citation
- Which technique they share with us
- How the application differs

### 3. Survey/Reference Papers

Key surveys or textbooks that a referee would expect to see cited:
- Full citation
- Why it should be cited (establishes notation, proves prerequisite, standard reference)

### 4. Recent Competition

Papers from the last 3 years in {JOURNAL} or closely related venues on similar topics:
- Full citation
- Relevance to our work

## Output Format

Return as structured markdown. For each paper, include enough bibliographic detail to create a BibTeX entry. Flag any paper that we MUST cite (referee would notice its absence).
