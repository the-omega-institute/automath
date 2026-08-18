# Verification of the referee's duplication charge — ITA-2026-0032, 2026-08-18

Checked independently while the Oracle and codex channels were down. This is the only
manuscript in the repository currently in a journal's hands, so it carries the highest
stakes of anything in the sprint queue.

## The charge

Referee 1 closes with "In my opinion this work cannot be published, as the results are
already well known." The sharpest specific is:

> At the end of their manuscript the authors show in Theorem 7.1 that the normalized
> addition alpha is not a local function. This is Proposition 14 in the cited paper [5].

The referee's own reference list runs [1] to [4]. **There is no [5].** So the most damaging
single charge in the report points at a source the report does not identify, and the
response had to guess which paper was meant. It guessed Frougny 1999.

## The guess is right

A local copy of the paper is in `tmp/pdfs/frougny1999.txt`. Proposition 14 exists and reads:

> Proposition 14. Addition in base [tau] on alphabet {0,1} is not a local function.

(The OCR renders tau as "r" throughout; the surrounding proof discusses r-representations
and the golden-ratio base, and the response's own Table 1 describes Proposition 13 as the
"base-phi online machine", so the base is tau.)

Control: the extraction contains 23 occurrences of "Proposition" and Propositions 1, 3-14
are all present, so a miss would have been a real absence rather than a broken extraction.

So the referee is right that the qualitative result is Frougny's, and the response's
identification of the unlabeled [5] is correct. This charge is answered honestly rather
than deflected: the revision moves the result to an appendix, states it is "not claimed as
a new qualitative nonlocality theorem", and cites Proposition 14 directly.

## One precision point worth fixing

Frougny's Proposition 14 is stated for **base tau**, not for the Fibonacci numeration
system. Frougny reaches Fibonacci numeration separately, by Corollary 4 — as the response's
own Table 1 records. The manuscript's theorem is about Zeckendorf normalization on
{0,1,2}.

The appendix wording is accurate: "a finite-scale light-cone formulation of the known
nonlocality phenomenon; see [Prop. 14]". The Table 1 row is looser — "Nonlocality is
established in [Prop. 14]" reads as though Proposition 14 already covers the manuscript's
setting. The two systems are tightly linked and the phenomenon does transfer, so this is a
precision issue and not a misattribution. One clause naming the base would close it.

## Not verified

The response cites Proposition 14 at "p. 99". The OCR text carries no page markers near
that point, so the page number is **unconfirmed**. Proposition 13 is placed at pp. 98-99 by
the response, which makes p. 99 plausible for the next proposition, but plausible is not
checked.

## A bookkeeping discrepancy, stated as what is absent

The board describes this as a "major revision package". No editor decision letter exists in
this directory or anywhere in the repository, and the response document contains no
occurrence of "major revision", "minor revision", "reject", or "decision". Referee 1
recommended against publication; Referee 2's report is not in the directory either, though
the response answers thirteen numbered points from it.

The decision may well have arrived by email and never been saved. What can be stated is
only that no document in the repository supports the "major revision" characterization, and
that the one referee report present recommends rejection. Worth resolving before the
revision is uploaded, because the covering note should answer the decision that was
actually issued.

---

# Addendum: independent rebuild of the upload artifact, 2026-08-18

`ITA-2026-0032_source.zip` is what actually goes to the journal, so it was rebuilt from
the zip itself rather than from the working directory, and without trusting the
`tmp/source_zip_compile_test_*` run already present.

Extracted to a clean directory, `latexmk -pdf` with no extra arguments and no
command-line macro definitions:

- exit 0
- **29 pages, exactly matching `ITA-2026-0032_manuscript.pdf`**
- zero undefined citations in the log
- zero `[?]` markers in the output
- all fifteen references render, `[1]` through `[15]`

The package is sound.

Two alarms I raised along the way were both mine, not the paper's:

1. The three `.bib` files sit in `submission_source_20260313/` while `main.tex` and
   `main.bbl` are at the archive root, which looked like a packaging error. It is not:
   line 2164 reads
   `\bibliography{submission_source_20260313/references_godel_zeckendorf,submission_source_20260313/references_fibonacci,submission_source_20260313/references}`.
   The layout is deliberate. My first grep for the command used the wrong escaping and
   reported it absent.
2. `main.bbl` carries fifteen `\bibitem` entries while my count of rendered references
   came to fourteen. The reference list is complete; a page break splits the list and one
   entry's `[n]` does not begin a line, so the counting regex missed it. Numbers 1 through
   15 are all present in the output.

Both are the same failure: a check that could not see something, reported as an absence.

## One cross-link worth recording

This bibliography contains Baranwal-Schaeffer-Shallit, *Ostrowski-automatic sequences*
[2], and Hieronymi-Terry, *Ostrowski numeration systems, addition and finite automata*
[10]. So the Ostrowski literature is known to this project and cited here.

That sharpens the folded_histograms finding of 2026-08-18: a manuscript whose whole subject
is Fibonacci-weight folding of rotation codings has no Ostrowski citation at all, while a
sibling manuscript cites two. As with the Berstel adder and `zeck_arith`, the gap is an
internal inconsistency rather than an unknown reference — which makes it cheaper to fix and
harder to excuse.
