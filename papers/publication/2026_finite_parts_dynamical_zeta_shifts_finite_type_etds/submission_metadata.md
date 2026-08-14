# Ergodic Theory and Dynamical Systems submission metadata

Journal: Ergodic Theory and Dynamical Systems

Article type: Research Article

Title: Finite radial determination of Frobenius profiles for elementary two-group extensions of shifts of finite type

Authors:

1. Haobo Ma
   - Email: auric@aelf.io
   - Affiliation: AELF PTE. LTD., #14-02, Marina Bay Financial Centre Tower 1,
     8 Marina Boulevard, Singapore 018981, Singapore
2. Wenlin Zhang
   - Email: e1327962@u.nus.edu
   - Affiliation: National University of Singapore, 21 Lower Kent Ridge Road,
     Singapore 119077, Singapore
   - Corresponding author: yes

## Abstract

Let E=(C2)^r, and let two one-step E-cocycles lie over primitive edge shifts
whose vertex counts are at most V; the base shifts need not be the same. For
the primitive length-element counts p_(n,g), put E_g(y)=sum_(n>=1)
p_(n,g) log(1-y^n). Without a twisted-gap hypothesis, equality of every
element profile at 2V ceil(log_2(4V)) distinct radii in the common open Perron
interval forces equality of every p_(n,g), provided that one sampled radius
is algebraic. Thus the number of radial locations is independent of r,
although each location supplies the full 2^r-component profile vector. For a
reduced binary character-determinant ratio of total degree D>0, one algebraic
collision identifies the complete real collision set, which has at most
D ceil(log_2(2D))-1 points. The inverse mechanism is arithmetic: determinant
parity, Kumiko Nishioka's special-value theorem, and Keiji Nishioka's
algebraic-solution rationality theorem force a normalized rational Mahler coboundary. A divisor
l1 estimate gives an O(D log D) degree bound and one finite Pade system
reconstructs or rejects the certificate. An exact four-vertex pair shows that
one centered Perron-boundary profile vector does not suffice. For general
finite groups, recovery holds from a radial set with an interior accumulation
point; already for C3, Adams--Mobius inversion exhibits the obstruction to a
finite bound by coupling determinant logarithms at infinitely many powers.

Keywords: one-sided edge shift; finite-group extension; inverse problem;
Mahler function; twisted determinant; Adams operation; primitive orbit;
finite sampling

2020 MSC: 37B10; 11B85; 39A06; 20C15; 05C25

Competing interests: The authors declare none.

## Referee-facing upload set

1. `main.pdf`: primary manuscript.
2. `supplement.pdf`: separately compiled Supplementary Material,
   "Adams-corrected Frobenius-class product constants".
3. `reproducibility.zip`: every verifier, every unit test, archived verifier
   and unit-test output, exact S3 certificate source/output, literature audit,
   checksums, and `REPRODUCE.md`.
4. `source.zip`: all sources needed to compile `main.pdf` and
   `supplement.pdf`, including `references.bib`.
5. `cover_letter.txt`: ETDS-specific cover letter.
6. `submission_metadata.md`: this manifest.

The same files are unpacked under `submission_bundle/` so portal upload does
not hide the scripts or their readable outputs inside an archive.

## Supplement policy

Checked 2026-08-15 against the ETDS "Preparing your materials" instructions:
https://www.cambridge.org/core/journals/ergodic-theory-and-dynamical-systems/information/author-instructions/preparing-your-materials

The instructions expressly permit supplementary materials and state that they
are published online alongside the article. The supplement and reproducibility
archive may therefore remain separate; no content needs to be moved into the
main manuscript.

## Priority boundary

Ostrowski (1968) treats the linear multiplicative equation. Keiji Nishioka (1985)
directly implies that an algebraic solution of
`F(z^2)=H(z)^(-1)F(z)^2` is rational. The submission makes no originality
claim for that implication. Its claimed contribution is limited to
parity-compatible algebraic collision lifting, effective rational-coboundary
bounds and reconstruction, and the cross-base elementary-two-group result.

## Verified expected results

- Both PDFs clean-build with XeLaTeX and have no undefined references,
  undefined citations, or multiply defined labels.
- `verify_a5_results.py` ends with `STATUS: PASS`.
- `verify_twisted_determinant_rigidity.py` ends with `STATUS: PASS`.
- The combined unit suite runs 37 tests and ends with `OK`.
- The exact S3 program ends with `fixed-label windows verified`.
- Every digest in `artifacts/SHA256SUMS` matches.
