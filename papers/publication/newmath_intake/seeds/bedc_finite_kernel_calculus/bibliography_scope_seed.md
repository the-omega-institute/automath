# Bibliography Scope Seed: BEDC Finite Kernel Calculus

This is a seed-level related-work scaffold. It is not an active `BIB_SCOPE.md`
and does not authorize promotion.

- seed:
  `papers/publication/newmath_intake/seeds/bedc_finite_kernel_calculus`
- source repo: `D:/omega/newmath`
- pinned source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`
- note date: 2026-05-31

## Purpose

The finite-kernel seed must not read as a BEDC manifesto or a list of Lean
declarations. Before journal-style promotion, the paper needs a comparison
frame that explains the finite kernel as a small formal calculus and naming
certificate interface.

## Comparison Buckets

| Bucket | Why it matters | Required comparison question |
|---|---|---|
| Small formal calculi | The manuscript claims a finite kernel of marks, histories, extension, continuation, bundles, and ask policies | What is structurally finite here, and how is it different from merely presenting a syntax fragment? |
| Proof-system interfaces | The seed discusses controlled naming, certificates, and policy surfaces | Which parts are object-language syntax, which are meta-level certificate disciplines, and which are implementation support? |
| Proof-assistant artifact papers | The source evidence is Lean code, but the paper claim should not be "we wrote Lean declarations" | What theorem-level interface is visible to a referee without reading the whole source tree? |
| Naming and certificate boundaries | NameCert and package surfaces are in scope, but not as replacement foundations | How does the naming/certificate boundary avoid claiming semantic completeness? |
| Formalization methodology | The automation pipeline may use this seed as evidence of source/manuscript separation | How does this paper avoid merging into the automation-pipeline paper? |

## Required Live Work Before Promotion

Before an active paper is created, run a current related-work pass for the
chosen route. The promoted paper should then create an active `BIB_SCOPE.md`
with exact citations and route-specific exclusions.

Do not promote directly to APAL, LMCS, or a similar journal unless the promoted
paper can answer:

- what single theorem or theorem family is the main finite-kernel contribution;
- why the result is not just a list of constructor facts;
- how the work compares with existing formal calculi and proof-system
  interfaces;
- what the paper explicitly does not claim about foundations or universality.

## Seed-Level Exclusions

This seed-level scaffold must not be used to claim:

- a replacement for type theory, set theory, or category theory;
- semantic completeness of BEDC;
- a Rule110 or automation-pipeline result;
- journal readiness without a packaging theorem or an explicitly modest
  short-note route.

