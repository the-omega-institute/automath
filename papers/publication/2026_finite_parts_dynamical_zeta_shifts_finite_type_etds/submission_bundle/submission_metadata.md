# Ergodic Theory and Dynamical Systems submission metadata

Journal: Ergodic Theory and Dynamical Systems

Article type: Research Article

Title: Linear radial determination for unit-Adams-invariant abelian
prime-power extensions of shifts of finite type

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

Let ell be prime and G a finite abelian ell-group. Consider two one-step
G-cocycles over primitive edge shifts with v and v' vertices, where the bases
need not agree. For the primitive length-element counts p_(n,g), put
E_g(y)=sum_(n>=1) p_(n,g) log(1-y^n). Assume that the ratios of the
corresponding character determinants are invariant under every unit Adams
operation chi -> chi^u, (u,ell)=1. If the two primitive profiles agree through
length L and their full element-profile vectors agree at K distinct radii in
the common open Perron interval, one of which is algebraic, then
K+L >= max{v,v'} forces equality of every p_(n,g). No twisted-gap hypothesis
is required. In particular, V radial locations determine the complete
primitive data for bases of size at most V. For binary extensions, an
explicit common-base family gives the complementary linear lower bound, and
hence the universal radial determination number is Theta(V).

The arithmetic step is unconditional. A rational critical p-Mahler product
with one algebraic value is first shown to be algebraic by an elementary
linear-exponent denominator estimate and Kumiko Nishioka's special-value
theorem. Logarithmic differentiation then places its logarithmic derivative
in the linear Mahler class, where the rational-transcendental dichotomy
applies. A divisor congruence under z -> z^p eliminates residual finite
monodromy and makes the original product rational. For a reduced input of
total degree D, the new squarefree estimate
2(p-1) deg rad(AB) <= D, R=A/B, combined with Rolle's theorem gives the
collision-jet bound used in the linear inverse theorem. A separate divisor
l1 estimate gives the sharp-order input-only bound
deg A+deg B=O_p(D log D), with explicit height control and fixed-p polynomial
bit complexity. Binary and odd-prime constructions give linearly many exact
rational collisions. For general finite groups, recovery holds from a radial
set with an interior accumulation point; already for C3, Adams-Mobius
inversion exhibits the obstruction to a finite bound by coupling determinant
logarithms at infinitely many powers.

Keywords: one-sided edge shift; finite-group extension; inverse problem;
Mahler function; twisted determinant; Adams operation; primitive orbit;
finite sampling

2020 MSC: 37B10; 11B85; 39A06; 20C15; 05C25

Competing interests: The authors declare none.

## Referee-facing upload set

1. main.pdf: primary manuscript.
2. supplement.pdf: separately compiled Supplementary Material,
   "Adams-corrected Frobenius-class product constants".
3. reproducibility.zip: every verifier, every unit test, archived verifier
   and unit-test output, exact S3 certificate source/output, literature audit,
   checksums, and REPRODUCE.md.
4. source.zip: all sources needed to compile main.pdf and supplement.pdf,
   including references.bib.
5. cover_letter.txt: ETDS-specific cover letter.
6. submission_metadata.md: this manifest.

The same files are unpacked under submission_bundle/ so portal upload does
not hide the scripts or their readable outputs inside an archive.

## Venue and paper architecture

ETDS is a defensible ambitious submission because the principal result is an
unconditional dynamical inverse theorem: linear finite radial determination
of represented periodic data for relatively unit-Adams-invariant finite
abelian prime-power extensions, with cross-base recovery, rank- and
exponent-independent radial depth, exact collisions, and realizable lower
bounds. The Mahler theorem is a supporting arithmetic mechanism; it does not
carry the journal-tier case.

A symbolic-computation venue is not a better home for the whole paper, whose
headline and standard conclusion are dynamical. The quantitative Mahler
results remain meaningful here because their sharpness is realized by
standard C2-cover zeta ratios.

## Supplement policy

Checked 2026-08-15 against the ETDS "Preparing your materials" instructions:
https://www.cambridge.org/core/journals/ergodic-theory-and-dynamical-systems/information/author-instructions/preparing-your-materials

The instructions expressly permit supplementary materials and state that they
are published online alongside the article. The supplement and
reproducibility archive may therefore remain separate.

## Priority boundary

Ostrowski treats the linear multiplicative equation. Algebraic-solution
rationality for nonlinear Mahler equations is prior and is not claimed here.
The proof of the normalized critical case uses Kumiko Nishioka's verified
linear rational-transcendental dichotomy, its Bell-Coons-Rowland restatement,
and an elementary divisor argument after logarithmic differentiation.
Kumiko Nishioka's 1982 special-value statement was checked directly.

The claimed contribution is the unconditional cross-base prime-primary
linear radial determination theorem, the sharp squarefree and total-divisor
estimates for its multiplicative certificate, their sharp lower-bound
families and realizable transfer, the supporting height and fixed-p bit
estimates, and the exact collision constructions. Bare existence and
decidability reduce to published additive and linear Mahler algorithms, and
the affine Pade step is standard rational reconstruction after a degree cap
is known.

## Verified expected results

- Both PDFs clean-build with XeLaTeX and have no undefined references,
  undefined citations, or multiply defined labels.
- verify_a5_results.py ends with STATUS: PASS.
- verify_linear_collision_claims.py ends with STATUS: PASS.
- verify_twisted_determinant_rigidity.py ends with STATUS: PASS.
- The combined unit suite runs 44 tests and ends with OK.
- The exact S3 program ends with fixed-label windows verified.
- Every digest in artifacts/SHA256SUMS matches.
