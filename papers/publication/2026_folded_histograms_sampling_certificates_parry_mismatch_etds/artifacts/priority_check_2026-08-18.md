# Priority and state check — folded_histograms, 2026-08-18

## A state bug: this paper is marked submitted and is not

The directory carries a `SUBMITTED` marker file. That marker is functional, not decorative:
`tools/chatgpt-oracle/split_overlap_harness.py` line 393 treats a paper directory as
submitted if it exists (`SUBMITTED_MARKER_FILES = ("SUBMITTED", "submission_receipt.md")`).

Every other directory in `papers/publication` carrying the marker is prefixed `submitted_`.
This one is the sole exception — the only paper in the active namespace that tooling will
classify as already submitted.

The marker is a leftover from the 48-page ETDS submission, which was **rejected** on
significance grounds; `next_FH_r2.txt` records the verdict verbatim ("too slight for ETDS
[...] a significance problem that major revision cannot repair"). What the directory holds
now is the short paper extracted in response: a 6-page note, *A Two-Letter Criterion for
Fibonacci Folding of Rotation Words*, whose cover letter is correctly addressed to The
Fibonacci Quarterly. That note has not been submitted anywhere.

Fix: remove or rename the marker. The directory suffix `_etds` is also stale, but that is
cosmetic and internal — unlike brocot, the cover letter here does **not** salute the
journal that rejected the paper.

## A citation gap: Ostrowski numeration is never mentioned

`references.bib` has three entries: Frougny 1991, Morse-Hedlund 1940, Zeckendorf 1972.
The string "Ostrowski" appears nowhere in the bibliography or in any built section, while
"Sturmian" appears in three of them.

The paper assigns Fibonacci weights to binary words, takes Zeckendorf normal forms, and
classifies injectivity on the block languages of interval codings of irrational rotations.
Ostrowski numeration is the numeration system canonically attached to rotation by alpha,
and for the golden rotation it specializes to exactly the Zeckendorf expansion. That is the
structural fact explaining why Fibonacci weights interact with rotation codings at all. The
introduction says "this familiar coding sits exactly on the collision-free boundary for the
Fibonacci fold" without it.

In fairness the note is otherwise well positioned and unusually honest about its scope
("Nothing stronger is being asserted [...] not a general rigidity theorem for dynamical
systems"), and a three-entry bibliography is defensible for a six-page note. This is one
missing thread, not a pattern.

Candidates, metadata verified against Crossref:

- M. Bunder and K. Tognetti, "The Zeckendorf Representation and the Golden Sequence",
  The Fibonacci Quarterly 29 (1991), no. 3, 217-219, doi 10.1080/00150517.1991.12429415.
  In the target journal itself.
- Lothaire, "Numeration Systems", chapter 8 of *Algebraic Combinatorics on Words*,
  Cambridge, 2002, pp. 230-268, doi 10.1017/cbo9781107326019.008. The standard reference.
- L. Schaeffer, "Ostrowski Numeration and the Local Period of Sturmian Words", LNCS 7810
  (2013), 493-503, doi 10.1007/978-3-642-37064-9_43.
- A. E. Frid, "Sturmian numeration systems and decompositions to palindromes",
  European J. Combin. 71 (2018), 202-212, doi 10.1016/j.ejc.2018.04.003.

One sentence citing the first two would close it. The last two are optional depth.

---

# Addendum: the main theorem, verified by exact computation

Script: `verify_two_letter_criterion.py`, in this directory.

The note's whole content is the equivalence

    Fold_m injective on S_m for every m  <=>  injective at m = 2  <=>  beta in (0,delta] u [1-delta,1)

so that is what was checked, from the definitions in Sections 2 and 3.

## Method, and why the arithmetic is exact

`s_j(x) = 1` exactly when `x` lies in the arc `[-j*alpha, beta - j*alpha)`. The `2m`
endpoints cut the circle into at most `2m` pieces, and each piece of positive length
contributes exactly one word. So `S_m` is computed exactly, with no sampling.

`alpha` is taken to be a continued-fraction convergent of a genuine irrational, with a
denominator far above any `m` used - `F_40/F_41 = 165580141/267914296` for the golden ratio
conjugate, and similar for `sqrt(2)-1` and `pi-3`. Every breakpoint comparison and arc
length is then a rational computation with no tolerance anywhere.

**This is the point of the choice, not a compromise.** The theorem asserts a *sharp*
threshold, and the interesting values are `beta = delta` and `beta = 1-delta` themselves,
which are on the injective side. In floating point those cases cannot be tested at all. In
exact rational arithmetic they can, and were.

**The limitation that comes with it**: `alpha` is rational, so this is a check of the
combinatorics rather than of an irrational rotation. For finite `m`, `S_m` depends only on
the cyclic order of the `2m` breakpoints, and a denominator of order `10^8` against
`m <= 12` cannot be distinguished from the irrational it approximates. That is an argument,
not a proof, and it is the one assumption this check rests on.

## Controls

- `N_m` restricted to the golden-mean language is a bijection onto `{0,...,F_{m+2}-1}` for
  `m = 1..14`, and `Fold_m` fixes every legal word. This is the note's
  Proposition 2.2, and it passes.
- The two-letter table quoted in Remark 2.3 reproduces exactly:
  `00 -> 00`, `10 -> 10`, `01 -> 01`, `11 -> 00`.

A third block prints `|S_m|` for a sample window. It is **descriptive, not a test** - it has
no pass condition and nothing is concluded from it. The counts do settle to `2m` for
`m >= 5` as expected for a non-Sturmian window.

## Result

For each of the three irrationals, 45 window lengths were tested - a grid of fortieths plus
the exact boundary values `delta` and `1-delta` and points `10^-6` either side of each.
**Zero mismatches** between the predicted classification and the computed injectivity, both
for "injective at every `m` up to 12" and for "injective at `m = 2`".

The refinement was checked separately: in the failing range `delta < beta < 1-delta`,
injectivity fails already at length two at every window length tested - 15, 11 and 43 values
for the three irrationals respectively, zero exceptions.

The theorem holds as stated, including at the threshold.
