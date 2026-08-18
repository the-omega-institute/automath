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
