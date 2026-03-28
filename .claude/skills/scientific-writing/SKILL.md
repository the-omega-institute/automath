---
name: scientific-writing
description: Write scientific manuscripts with proper structure (IMRAD), citations (APA/AMA/Vancouver), figures/tables, and reporting guidelines (CONSORT/STROBE/PRISMA). Use when drafting any manuscript section, improving writing clarity, or preparing for journal submission.
---

# Scientific Writing

> Write clear, precise, and publication-ready scientific manuscripts.

## When to Use

- Drafting manuscript sections (abstract, intro, methods, results, discussion)
- Structuring a research paper using IMRAD format
- Formatting citations and references
- Creating or improving figures and tables
- Applying reporting guidelines (CONSORT, STROBE, PRISMA)
- Preparing manuscripts for journal submission
- During the WRITING or REVIEW phases

## Manuscript Structure (IMRAD)

```
┌─────────────────────────────────────────────────────────────┐
│ TITLE                                                       │
│ Concise, specific, informative (12-15 words)               │
├─────────────────────────────────────────────────────────────┤
│ ABSTRACT (150-250 words)                                    │
│ Background → Objective → Methods → Results → Conclusion     │
├─────────────────────────────────────────────────────────────┤
│ INTRODUCTION                                                │
│ Context → Gap → Objective → Approach                        │
│ Funnel: Broad → Narrow → Your question                     │
├─────────────────────────────────────────────────────────────┤
│ METHODS                                                     │
│ Study design → Participants → Procedures → Analysis         │
│ Enough detail for replication                              │
├─────────────────────────────────────────────────────────────┤
│ RESULTS                                                     │
│ Objective findings, no interpretation                       │
│ Text + Figures + Tables                                     │
├─────────────────────────────────────────────────────────────┤
│ DISCUSSION                                                  │
│ Key findings → Context → Limitations → Implications         │
│ Reverse funnel: Specific → Broad                           │
├─────────────────────────────────────────────────────────────┤
│ REFERENCES                                                  │
│ Consistent style, verified DOIs                            │
└─────────────────────────────────────────────────────────────┘
```

---

## Section-by-Section Guidance

### Abstract

**Purpose**: Standalone summary of the entire paper

**Structure** (for structured abstracts):
- **Background**: Why this matters (1-2 sentences)
- **Objective**: What you did (1 sentence)
- **Methods**: How you did it (2-3 sentences)
- **Results**: Key findings with numbers (3-4 sentences)
- **Conclusion**: Main takeaway (1-2 sentences)

**Tips**:
- Write LAST after all other sections
- Include specific numbers/results
- Avoid abbreviations (or define them)
- Stay within word limit (usually 150-250)

### Introduction

**Purpose**: Establish context, gap, and rationale

**Structure (Funnel)**:
1. **Broad context** (1-2 paragraphs): Why does this field matter?
2. **Current knowledge** (2-3 paragraphs): What's known? What approaches exist?
3. **Gap/Problem** (1 paragraph): What's missing? What's the controversy?
4. **Your study** (1 paragraph): What did you do? Why this approach?

**Tips**:
- End with clear objectives or hypotheses
- Cite 20-40 references typically
- Use present tense for established facts
- Be specific about what you're studying

### Methods

**Purpose**: Enable replication

**Key Sections**:
1. **Study Design**: Type of study, setting, dates
2. **Participants/Samples**: Selection, criteria, sample size, ethics
3. **Procedures**: What was done, in order
4. **Measurements**: What and how measured
5. **Statistical Analysis**: Tests, software, significance criteria

**Common Mistakes**:
| Mistake | Problem | Fix |
|---------|---------|-----|
| Vague methods | "Standard methods" | Specify exact protocol |
| Missing stats | "Data were analyzed" | Name specific tests |
| No software versions | Not reproducible | Include version numbers |
| Missing sample size justification | Why this n? | Add power analysis |

**Tips**:
- Use past tense
- Be specific: model numbers, concentrations, durations
- Reference published protocols if applicable
- Include ethical approvals

### Results

**Purpose**: Present findings objectively

**Organization**:
1. Order by importance or by methods flow
2. Each paragraph: finding + evidence (figure/table reference)
3. Stats: test, statistic, df, p-value, effect size

**Structure Pattern**:
```
[What was found] (Figure X).
[Statistical support] (t(df) = X.XX, p = .XXX, d = X.XX).
[Additional detail or subgroup analysis].
```

**Tips**:
- NO interpretation (save for Discussion)
- Include negative/null results
- Reference every figure and table
- Use past tense
- Include exact p-values (not just p < 0.05)

### Discussion

**Purpose**: Interpret findings in context

**Structure (Reverse Funnel)**:
1. **Key findings** (1-2 paragraphs): Main results, directly address objectives
2. **Comparison to literature** (2-3 paragraphs): How do findings fit with prior work?
3. **Mechanisms** (1-2 paragraphs): Why might this happen?
4. **Limitations** (1 paragraph): Be honest and specific
5. **Implications** (1-2 paragraphs): Clinical, practical, theoretical significance
6. **Future directions** (optional): What next?
7. **Conclusion** (1 paragraph): Main takeaway

**Tips**:
- Start with your results, not literature
- Acknowledge limitations honestly
- Don't overstate conclusions
- Distinguish correlation from causation

---

## Citation Styles

### APA (7th Edition)

**In-text**: (Author, Year) or Author (Year)
```
Previous research found significant effects (Smith, 2023).
Smith (2023) reported significant effects.
```

**Reference list**:
```
Smith, J. D., Johnson, M. L., & Williams, K. R. (2023). Title of 
    article. Journal Name, 22(4), 301-318. https://doi.org/10.xxx/yyy
```

### Vancouver/ICMJE

**In-text**: Superscript or bracketed numbers¹ or [1]
```
Previous research found significant effects.¹
Multiple studies support this finding.¹⁻³
```

**Reference list** (numbered):
```
1. Smith JD, Johnson ML, Williams KR. Title of article. J Name. 
   2023;22(4):301-18.
```

### Nature

**In-text**: Superscript numbers¹
```
Previous research found significant effects¹.
```

**Reference list**:
```
1. Smith, J. D., Johnson, M. L. & Williams, K. R. Title of article. 
   Nat. Rev. Drug Discov. 22, 301-318 (2023).
```

---

## Figures and Tables

### When to Use Which

| Use Tables For | Use Figures For |
|----------------|-----------------|
| Exact values needed | Trends and patterns |
| Many variables | Comparisons |
| Summary statistics | Relationships |
| Participant characteristics | Processes |

### Figure Checklist

- [ ] Self-explanatory with caption
- [ ] Axes labeled with units
- [ ] Error bars defined (SEM, SD, CI)
- [ ] Significance markers explained
- [ ] Colorblind-safe
- [ ] Resolution ≥300 DPI

### Table Checklist

- [ ] Clear, descriptive title
- [ ] Column headers with units
- [ ] Appropriate precision (not too many decimals)
- [ ] Notes for abbreviations
- [ ] n values included

### Caption Template

```markdown
**Figure 1. Brief descriptive title.**

(A) Description of panel A. (B) Description of panel B. 
Data shown as mean ± SEM (n = X per group). Statistical 
comparisons by [test name]. *p < 0.05, **p < 0.01, ***p < 0.001.
```

---

## Reporting Guidelines

### Which Guideline to Use

| Study Type | Guideline | URL |
|------------|-----------|-----|
| Randomized trial | CONSORT | consort-statement.org |
| Observational (cohort, case-control) | STROBE | strobe-statement.org |
| Systematic review | PRISMA | prisma-statement.org |
| Diagnostic accuracy | STARD | stard-statement.org |
| Prediction models | TRIPOD | tripod-statement.org |
| Animal research | ARRIVE | arriveguidelines.org |
| Case reports | CARE | care-statement.org |
| Quality improvement | SQUIRE | squire-statement.org |

### Using Checklists

1. Download checklist from guideline website
2. Complete each item during writing
3. Include page/line numbers
4. Submit with manuscript (often required)

---

## Writing Principles

### Clarity

- Use precise, unambiguous language
- One idea per sentence
- Define technical terms at first use
- Use active voice when possible

**Example**:
```
❌ "The samples were subjected to analysis"
✓ "We analyzed the samples using..."

❌ "It has been shown that..."
✓ "Smith et al. (2023) showed that..."
```

### Conciseness

| Wordy | Concise |
|-------|---------|
| "Due to the fact that" | "Because" |
| "In order to" | "To" |
| "A large number of" | "Many" |
| "At the present time" | "Now" / "Currently" |
| "In the event that" | "If" |
| "Has the ability to" | "Can" |

### Accuracy

- Report exact values with appropriate precision
- Use consistent terminology
- Distinguish observation from interpretation
- Acknowledge uncertainty

### Objectivity

- Present results without bias
- Don't overstate findings
- Acknowledge contradictory evidence
- Maintain professional, neutral tone

---

## Field-Specific Terminology

### General Principles

- Match terminology to the target journal
- Use established nomenclature systems
- Define abbreviations at first use
- Be consistent throughout

### Quick Reference

| Field | Convention |
|-------|------------|
| Genes | Italics (*BRCA1*) |
| Proteins | Roman (BRCA1) |
| Species | Italics, full at first (*Escherichia coli*), then abbreviated (*E. coli*) |
| Statistics | Italics (p, n, t, F, r) |
| Drugs | Generic name first, brand in parentheses |

---

## Common Mistakes to Avoid

### Top Rejection Reasons

1. Incomplete or inappropriate statistics
2. Over-interpretation of results
3. Poor methods description
4. Inadequate sample size
5. Poor writing quality
6. Inadequate literature review
7. Unclear figures
8. Failure to follow guidelines

### Writing Issues

| Issue | Example | Fix |
|-------|---------|-----|
| Tense mixing | "We collected... and analyze" | Past for methods/results |
| Excessive jargon | Too many undefined terms | Define or simplify |
| Paragraph breaks | Random breaks | One topic per paragraph |
| Missing transitions | Abrupt section changes | Add linking sentences |

---

## Manuscript Development Workflow

### Recommended Order

1. **Figures/Tables first** (core data story)
2. **Methods** (often easiest to draft)
3. **Results** (describe figures/tables)
4. **Discussion** (interpret findings)
5. **Introduction** (set up the question)
6. **Abstract** (synthesize everything)
7. **Title** (last refinement)

### Revision Checklist

- [ ] Logical flow throughout
- [ ] Consistent terminology
- [ ] All figures/tables referenced
- [ ] All citations verified
- [ ] Word counts met
- [ ] Reporting checklist complete
- [ ] Journal format requirements met

---

## Integration with RA Workflow

### WRITING Phase Files

| File | Purpose |
|------|---------|
| `manuscript/background.md` | Introduction content |
| `manuscript/methods.md` | Methods section |
| `manuscript/results.md` | Results + figure refs |
| `manuscript/discussion.md` | Discussion section |
| `manuscript/figures/figN/caption.md` | Figure captions |

### Connected Skills

- **← `/write_background`**: Drafts introduction
- **← `/write_methods`**: Generates methods from scripts
- **← `/write_results`**: Drafts results from figures
- **→ `/peer_review`**: Self-review before submission
