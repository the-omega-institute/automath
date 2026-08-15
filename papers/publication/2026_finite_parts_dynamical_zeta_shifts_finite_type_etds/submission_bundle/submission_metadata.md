# Ergodic Theory and Dynamical Systems submission metadata

Journal: Ergodic Theory and Dynamical Systems

Article type: Research Article

Title: Finite radial determination of Frobenius profiles for odd-Adams-invariant abelian two-group extensions of shifts of finite type

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

Let G be a finite abelian 2-group, and assume that the twisted determinants
of two one-step G-cocycles are invariant under every odd Adams operation.
The cocycles lie over primitive edge shifts whose vertex counts are at most
V; the bases need not be the same. For the primitive length-element counts
p_(n,g), put E_g(y)=sum_(n>=1) p_(n,g) log(1-y^n). Without a twisted-gap
hypothesis, equality of every element profile at
2V ceil(log_2(4V)) distinct radii in the common open Perron interval forces
equality of every p_(n,g), provided that one sampled radius is algebraic.
The number of radial locations is independent of the rank and exponent of G.
The hypothesis is automatic for G=(C2)^r and permits genuine holonomy of
orders 4, 8, and beyond. The inverse mechanism is arithmetic: a parity-free
rational critical p-Mahler lifting theorem combines an elementary
linear-exponent denominator estimate with Kumiko Nishioka's special-value
theorem and the cited algebraic-solution rationality result of Keiji
Nishioka. Determinant parity gives a stronger integral refinement but is not
needed for lifting. For the multiplicative certificate itself, an input-only
divisor estimate gives an O(D log D) degree bound in terms of the reduced
input degree alone. Its order is sharp abstractly and on standard realizable
C2-cover zeta ratios. Explicit height and fixed-p bit bounds are supporting
quantitative consequences; the Pade step is rational reconstruction after a
degree cap is known. A second standard-cover family gives m exact rational collisions on
4m+2 vertices and hence an Omega(V) sampling lower bound. For general finite
groups, recovery holds from a radial set with an interior accumulation point;
already for C3, Adams--Mobius inversion exhibits the obstruction to a finite
bound by coupling determinant logarithms at infinitely many powers.

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

## Venue and paper architecture

ETDS remains a defensible ambitious submission because the principal result
is the dynamical inverse theorem: finite radial determination of represented
periodic data for odd-Adams-invariant finite abelian two-group extensions,
with cross-base recovery, rank- and exponent-independent radial depth, exact
collisions, and realizable lower bounds. This is a central dynamical problem
at the interface with number theory and combinatorics. The Mahler theorem is a
strong supporting theorem that improves the paper's completeness and
effectivity; it does not carry the journal-tier case.

A symbolic-computation venue is not a better home for the present whole
paper, whose headline and standard conclusion are dynamical. A focused
functional-equations extraction was considered, but splitting was declined:
the quantitative Mahler result is more meaningful here because its sharpness
is realized by standard C2-cover zeta ratios, while the dynamics paper uses
the result as its effective arithmetic engine.

## Supplement policy

Checked 2026-08-15 against the ETDS "Preparing your materials" instructions:
https://www.cambridge.org/core/journals/ergodic-theory-and-dynamical-systems/information/author-instructions/preparing-your-materials

The instructions expressly permit supplementary materials and state that they
are published online alongside the article. The supplement and reproducibility
archive may therefore remain separate; no content needs to be moved into the
main manuscript.

## Priority boundary

Ostrowski (1968) treats the linear multiplicative equation. The cited
algebraic-solution rationality result of Keiji Nishioka (1985) supplies the
rationality implication for `F(z^2)=H(z)^(-1)F(z)^2`; the submission makes no
originality claim for that implication. The parity-free lifting theorem is
explicitly the combination of Kumiko Nishioka's 1982 special-value theorem,
the cited Keiji Nishioka result, and an elementary denominator estimate. The
claimed contribution is limited to parity-compatible algebraic collision
lifting in the dynamical setting, the input-only multiplicative-certificate
divisor estimate and its sharp lower-bound family, the supporting height and
fixed-p bit estimates, the cross-base odd-Adams-invariant abelian 2-group
theorem, and the realizable certificate-degree and linear sampling lower
bounds. Bare existence and decidability are prior; once a degree bound is
known, the Pade step is largely standard rational reconstruction.

## Verified expected results

- Both PDFs clean-build with XeLaTeX and have no undefined references,
  undefined citations, or multiply defined labels.
- `verify_a5_results.py` ends with `STATUS: PASS`.
- `verify_twisted_determinant_rigidity.py` ends with `STATUS: PASS`.
- The combined unit suite runs 41 tests and ends with `OK`.
- The exact S3 program ends with `fixed-label windows verified`.
- Every digest in `artifacts/SHA256SUMS` matches.
