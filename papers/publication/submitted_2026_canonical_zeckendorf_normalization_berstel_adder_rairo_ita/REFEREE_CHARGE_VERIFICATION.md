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

---

# Addendum: the two surviving novelty claims, verified by computation

After the revision conceded the qualitative results to Frougny, Sakarovitch, Berstel and
Mousavi-Schaeffer-Shallit, the paper's novelty rests on two bounds. Both were checked
independently by re-implementing the machinery from the manuscript's own definitions:
the ten-state transducer of Section 5, `Val_MSD(w) = sum d_i F_{n-i+2}`,
`Berstel(w) = trimMSD(K(trimMSD(w)))`, and
`tau(w) = min{t : Berstel^t(trimMSD(w)) = Z_MSD(w)}`.

Script: `verify_berstel_iteration_depth.py`, in this directory.

## Controls, run first

The script refuses to report on the theorems until these pass, because a mistranscribed
transition table would make every downstream number meaningless.

- **Value preservation of the transducer**: all 29,523 words over {0,1,2} of length 1 to 9,
  `Val_MSD(K(w)) = Val_MSD(w)`, **zero mismatches**. The table is transcribed correctly.
- **Greedy Zeckendorf**: 20,000 values, each `Z_MSD(v)` admissible and of the right value,
  zero mismatches.
- **Lemma tau(u) <= D(u) <= floor(L/2)** on all binary words to length 16: pass.

## Theorem, binary cleanup depth

`max { tau(u) : u in {0,1}^L trimmed } = floor(L/2)`, checked exhaustively for L = 1..20.
Exact agreement at every length. The extremal witnesses found by brute force are exactly
the family the paper predicts:

    L=20  witness 10101010101010101011      tau = 10 = floor(20/2)
    L=19  witness 1010101010101010110       tau =  9 = floor(19/2)

that is `(10)^k 11` for even L and `(10)^k 110` for odd L, matching the paper's `P_r`.

## Theorem, depth on genuine additions

`max { tau(w) : w in Add_2^MSD(n) } = ceil(n/2)`, checked exhaustively for n = 1..14 over
the words with no factor 12, 21 or 22. Exact agreement at every length.

The revision makes a sharper claim than this: that the maximum is **attained by trimmed
inputs**, so the bound is not an artifact of leading-zero padding. Brute-force enumeration
restricted to trimmed words was run separately, because the unrestricted search returns
padded witnesses first and so does not test the claim. It holds at every n from 1 to 14:

    n=13  witness 2002002002011   tau = 7 = ceil(13/2)
    n=14  witness 10020020020102  tau = 7 = ceil(14/2)

## Verdict

Both surviving novelty claims hold, with the extremal families the paper names, and the
trimmed-attainment refinement holds as well. This is the part of the manuscript that has to
carry the resubmission, and it stands up.

---

# Addendum: the six-state quotient, verified

Referee 1 allowed that "the only original result could be the minimality of the Berstel
adder", then doubted that too. The revision answers by dropping the old ten-state
minimality claim and replacing it with a six-state output-delay quotient plus a
pairwise-separation argument. Both were checked from the manuscript's own tables.

Script: `verify_six_state_quotient.py`, in this directory.

- **Forced prefixes p(q)**: all ten match the displayed values — `0` for the four states
  beginning 0, `1` for the four beginning 1, empty for `002` and `010`. The longest common
  prefix is **stable between search depth 7 and depth 9**, so it is not a finite-depth
  artifact.
- **The six classes**: exactly six distinct normalized residuals, and the partition is
  exactly the claimed one, `{000,100} {001,101} {002} {010} {0B2,1B2} {01B,11B}`.
- **The separating suffixes quoted in the proof** reproduce exactly: `G_A(0)=000` against
  `G_E(0)=001`, `G_B(0)=010` against `G_F(0)=001`, `G_C(0)=0101` against `G_D(0)=0100`.
  Terminal outputs come out `A,E -> 00`, `B,F -> 01`, `C,D -> 010` as printed.
- **The quotient realizes K**: the displayed six-state table, run with initial state A and
  initial output `0`, reproduces the ten-state machine's complete output on all **88,573**
  words of length up to 10, **zero mismatches**. This validates the table entry by entry,
  including the initial-output convention.
- **Lower bound**: all fifteen pairs of reduced residuals are distinct, so no five-state
  realization exists under this convention.

## What this check does not settle

It confirms the mathematics as printed. It says nothing about the referee's other point,
that the Mousavi-Schaeffer-Shallit proof "gives also a proof of the minimality". That is a
priority question about whether the result is new, not about whether it is true, and no
computation here can answer it. It needs a reading of that paper, and it should go to the
Oracle when the channel returns.

Taken with the iteration-depth check, both pillars the resubmission rests on verify.
