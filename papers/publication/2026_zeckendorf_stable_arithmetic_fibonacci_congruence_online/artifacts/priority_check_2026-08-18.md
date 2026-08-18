# Priority and citation check — zeck_arith, 2026-08-18

Run against Crossref and arXiv (the two indices reachable while the Oracle and codex
channels were down). Semantic Scholar rate-limited and contributed nothing.

## Positive control

Before reading anything into a null result, a control query established that the index
covers this literature at all: `Frougny on-line finite automata addition numeration
systems` returned, in the top six, Frougny 1999 (the paper this manuscript cites),
Frougny-Sakarovitch *Number representation and finite automata*, Frougny 1992, and
Hieronymi-Terry. The index sees this field.

## Finding: a missing citation, verified

**Labbe, Sebastien; Lepsova, Jana. "A Fibonacci analogue of the two's complement
numeration system." RAIRO - Theoretical Informatics and Applications 57 (2023), art. 12.
DOI 10.1051/ita/2023007.**

Metadata confirmed directly against Crossref by DOI: title, both authors, volume 57,
article 12, year 2023, 3 citations, publisher EDP Sciences. arXiv preprint 2205.02574.

Relevance: it supplies the **Berstel adder** — the named finite-state transducer that
adds ordinary Fibonacci representations of nonnegative integers — together with a new
constructive proof, and extends the construction to signed integers. Section 7 of this
manuscript is precisely about addition transducers in Fibonacci numeration, and it
currently cites only Frougny 1999 for that object. Both papers are in RAIRO ITA; a
referee drawn from this community is likely to know it.

Neither `Berstel` (as adder) nor `Labbe`/`Lepsova` appears in `references.bib`
(19 entries checked). Note that the sibling manuscript fibonacci_folding does contain a
`Berstel1985` key, but that is *Fibonacci Words - a Survey*, a different work by the same
author; it is not the adder.

Action when the codex channel returns: add the entry and cite it where the online adder
is introduced. This is a completeness citation, not a priority threat — Labbe-Lepsova
claim no delay bound, so Frougny 1999 remains the correct source for delay three.

## Null result, and why it is weak

A query aimed at prior art for the manuscript's own headline — the linear lower bound on
multiplication delay — returned nothing relevant. It also returned nothing *on topic*:
the hits were delay-differential equations, the counterfeit-coin problem, quantum
oblivious transfer, and delay cells for neural-network hardware. A query whose noise is
drawn from four unrelated fields has not searched the intended field, so this is not
evidence that the lower bound is unanticipated. The priority question for
`thm:mul-delay-linear-lower-bound` remains open and should be put to the Oracle, which
can read the statement rather than match keywords against it.

---

# Addendum, same day: the gap is internal, and larger than first reported

The Labbe-Lepsova recommendation above understated the problem. This project already owns
a manuscript whose entire subject is the object in question:

`papers/publication/submitted_2026_canonical_zeckendorf_normalization_berstel_adder_rairo_ita`
— *Canonical Zeckendorf Normalization and Sharp Iteration Depth of the Berstel Adder*,
ITA-2026-0032, submitted to RAIRO ITA and currently with referees (Referee 1 report and a
response document are both in that directory). Its keywords are "Berstel adder, online
delay, Fibonacci addition". It cites Labbe-Lepsova already, so no new entry needs to be
created — the verified record can be copied across verbatim:

    @article{LabbeLepsova2023FibonacciTwosComplement,
      author  = {Labb{\'e}, S{\'e}bastien and Lep{\v{s}}ov{\'a}, Jana},
      title   = {A {Fibonacci} analogue of the two's complement numeration system},
      journal = {RAIRO - Theoretical Informatics and Applications},
      volume  = {57}, year = {2023}, pages = {12},
      doi     = {10.1051/ita/2023007},
    }

Meanwhile `zeck_arith` mentions Berstel **zero** times. Verified across every `.tex` and
`.bib` in the paper — main.tex plus the four `source/07_emergent_arithmetic_*` files —
with a positive control in the same command (Frougny: 13 hits, so the search was looking
in the right place; Berstel: 0; Labbe/Lepsova: 0).

So Section 7 of this manuscript builds an online addition transducer for Fibonacci
numeration without naming the Berstel adder, and without citing the sibling paper this
project has under review at RAIRO ITA on exactly that adder.

That is no longer a completeness citation. Two manuscripts from the same authors on
overlapping material, one of them already before referees at RAIRO ITA, must cite each
other — otherwise the second submission reads as undisclosed overlap. Fibonacci-numeration
automata is a small field and the referee pools overlap.

Action, in priority order, when the codex channel returns:
1. Cite the sibling manuscript in `zeck_arith` and state the relationship explicitly.
2. Copy the Labbe-Lepsova entry across and cite it where the online adder is introduced.
3. Have someone check the reverse direction — whether ITA-2026-0032's response to referees
   should disclose `zeck_arith` as companion work.
