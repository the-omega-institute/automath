# Submission brief — zeck_arith, 2026-08-19

t462 found this is the only sprint manuscript with no cover letter, no checklist and no
submission metadata. This assembles what a cover letter needs, from material already
established. It deliberately does not draft the letter: that is authoring, and the writing
channel is down.

## Recorded target

`scope_contract.md` states the bar as "a submission to Integers: Electronic Journal of
Combinatorial Number Theory". That is the only venue on record for this manuscript.

## What a referee will treat as the paper

The t418 assessment was blunt about this and it should drive the letter: the referee will treat
`thm:mul-delay-linear-lower-bound` -- every exact most-significant-digit-first multiplier at
effective resolution n has delay at least n-1 -- as the paper, and the ring structure as
notation and motivation. The abstract already states the delay theorem, so no rewrite is needed
there; the letter should lead with it rather than with the monoid quotient.

I verified that theorem independently at t427: the witness triple is admissible, the streams
differ only at position 1, the products are exact with no reduction, and the outputs differ at
some k >= n, for n = 3..24.

## Venue tension worth flagging to whoever decides

The delay theorem is an automata and on-line arithmetic result. Integers is combinatorial
number theory. The natural home for the delay half is a theoretical-informatics venue -- and
this project already has a manuscript there: ITA-2026-0032, "Canonical Zeckendorf Normalization
and Sharp Iteration Depth of the Berstel Adder", currently with referees at RAIRO ITA.

That cuts both ways. It argues for Integers, to avoid two overlapping submissions in one
editorial pool; and it makes disclosure obligatory whichever venue is chosen. This is a
decision, not a defect, and it is recorded rather than settled.

## Disclosures the letter must make

1. The sibling manuscript ITA-2026-0032, under review at RAIRO ITA, on the Berstel adder.
   Section 7 here builds an online addition transducer for Fibonacci numeration and currently
   mentions Berstel zero times. Two manuscripts from the same authors on overlapping material,
   one already before referees, must cite each other or the second reads as undisclosed overlap.

## Citations to add before submission, all verified missing

    Labbe and Lepsova, "A Fibonacci analogue of the two's complement numeration system",
        RAIRO ITA 57 (2023), art. 12, doi 10.1051/ita/2023007
    Fenwick, "Zeckendorf Integer Arithmetic", Fibonacci Quart. 41 (2003) 405-413,
        doi 10.1080/00150517.2003.12428552
    Dimitrov and Donevsky, "Faster Multiplication of Medium Large Numbers Via the Zeckendorf
        Representation", Fibonacci Quart. 33 (1995) 74-77, doi 10.1080/00150517.1995.12429176

None threatens priority. The Fenwick omission is the conspicuous one: a paper on Zeckendorf
arithmetic that does not cite the paper titled "Zeckendorf Integer Arithmetic" reads as an
unread field, and Integers draws referees from exactly that pool.

## Priority status, for the letter's novelty paragraph

No prior art for the linear lower bound on multiplication delay was found in an index
demonstrably covering the field. The t434 search returned twelve hits all in Fibonacci
numeration, ten of them in the Fibonacci Quarterly, which is the positive control the earlier
attempt lacked. That is the strongest statement the reachable channels support and the letter
should not claim more.

## Reproducibility

t455 found this manuscript names no scripts and never uses the word reproducibility, and it has
exactly one artifact script, `verify_multiplication_delay_bound.py`, which runs clean. Whatever
reproducibility statement is added must name that script, and any script named must be run
first.
