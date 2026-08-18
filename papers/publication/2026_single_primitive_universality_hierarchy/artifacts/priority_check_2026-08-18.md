# Priority and citation check — single_primitive, 2026-08-18

Run against Crossref while the Oracle and codex channels were down.

## Clean: the load-bearing external citation is genuine

The abstract states that the only external enumerative input is the Fibonacci
interval-maximum formula of Kocabova-Masakova-Pelantova, used at
`sec05_height_and_nonuniformity.tex:34` as [Thm. 4.7]. That citation was verified.

A lookup by DOI returned empty, which given this project's history with a fabricated
citation warranted checking rather than assuming. It is a quirk of the by-DOI path, not a
fabrication: the same call on Frougny's DOI, same publisher prefix and same old-style
colon format, resolved normally, and a Crossref search by title returned the paper
exactly — Petra Kocabova, Zuzana Masakova, Edita Pelantova, "Integers with a maximal
number of Fibonacci representations", RAIRO ITA 39 (2005), no. 2, 343-359,
doi 10.1051/ita:2005022. Every field in `references.bib` matches. Nothing to fix.

## Finding: Carlitz is gone from the built paper

`references.bib` has no Carlitz entry, and no built section mentions him. The six
sections `\input` by `main.tex` are sec01 through sec06; `_cut_hierarchy_eml_richardson.tex`
is not among them.

That cut file still contains the passage that positioned this work against the classical
literature:

> The classical Fibonacci representation-function analyses of
> \cite{Carlitz1968,Carlitz1970,KocabovaMasakovaPelantova2005} concern individual
> representation counts and their extrema [...] The result below concerns instead the
> positive-support transfer of the intrinsic collision moments.

The surviving replacement in `sec01_introduction.tex` does most of that work well — it
cites BicknellJohnsonFielder1999 and KocabovaMasakovaPelantova2005, explains that they
count representations of specified integers and so do not form the residue fibres of
Fold_m, and compares against Sanna. What it dropped is Carlitz specifically. The sentence
now opens "There is also a substantial literature on the multiplicity of individual
integers as sums of distinct Fibonacci numbers" and then cites only 1999 and 2005.

Carlitz 1968 is the founding paper on that multiplicity function, and this manuscript
computes its moments. Verified metadata for both works:

- L. Carlitz, "Fibonacci Representations", The Fibonacci Quarterly 6 (1968), no. 4,
  193-220, doi 10.1080/00150517.1968.12431213. 44 citations in Crossref.
- L. Carlitz, "Fibonacci Representations - II", The Fibonacci Quarterly 8 (1970), no. 2,
  133-134, doi 10.1080/00150517.1970.12431098.

Action when the codex channel returns: restore both entries and cite them in that opening
sentence. Mechanical; no mathematical content changes. This is a completeness gap rather
than a priority threat — Carlitz studies individual representation counts, not the
collision moments S_q(m).

## Not done: the OEIS check

The second-moment sequence S_2(m) = 6, 14, 36, 88, 220, 544, 1352, 3352, 8320, 20640,
51216, 127072 (from the paper's recurrence S_2(m) = 2S_2(m-1) + 2S_2(m-2) - 2S_2(m-3)
with initial values 6, 14, 36) should be checked against OEIS before submitting to a
Fibonacci-community venue. Both the text and JSON search endpoints returned HTTP 403, so
**this check has not been performed**. It is not recorded as clear. It needs either a
browser session or a hand check by someone with OEIS access.
