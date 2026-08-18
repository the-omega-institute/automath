# Toward the correct ambiguous-core bound for the Zeckendorf window fold

Working notes. Nothing here is in a manuscript, and the main bound is not proved.

## Setting

Low-to-high digits; position k carries weight F_{k+1}, with F_2 = 1, F_3 = 2, F_4 = 3.
For a length-m window w, Fold_m(w) is the Zeckendorf normal form of N(w) mod F_{m+2}.
An ambiguity of block length L is a pair u != v in {0,1}^L whose L-m+1 consecutive
window labels agree.

Writing d = u - v in {-1,0,1}^L, the labels agree at window i exactly when

    S_i(d) := sum_{k=0}^{m-1} d_{i+k} F_{k+2}  ==  0   (mod F_{m+2}).

## Lemma (proved). Every window sum is 0 or +/- F_{m+2}.

The weights of one window sum to

    sum_{j=2}^{m+1} F_j = F_{m+3} - 2,

so |S_i(d)| <= F_{m+3} - 2 for any d in {-1,0,1}^L. Since F_{m+3} = F_{m+2} + F_{m+1}
and F_{m+1} < F_{m+2} for m >= 1, we get F_{m+3} - 2 < 2 F_{m+2}. Combined with
S_i == 0 mod F_{m+2}, this forces

    S_i(d)  in  { 0, +F_{m+2}, -F_{m+2} }.

Checked against every ambiguous pair the exhaustive search produced for m = 3..6:
1980 window sums, zero violations, distribution 1638 zeros, 340 at -F_{m+2}, 2 at +F_{m+2}.

## What is observed but not proved

The longest minimal ambiguous core has length exactly 2m-2, verified exhaustively for
m = 3,4,5,6,7,8. The extremal witnesses are always the Fibonacci recurrence itself:

    u has a single 1 at position m+1,      N(u) = F_{m+2}
    v has 1s at positions m-1 and m,       N(v) = F_{m+1} + F_m = F_{m+2}

padded with zeros to length 2m-2. Deleting any coordinate destroys the ambiguity, which
is what makes the pair minimal; the padding is not decoration.

That family gives the lower bound 2m-2 for every m. The upper bound is open. The lemma
above is the natural first step: an ambiguity is a +/-1 vector all of whose window sums
are 0 or +/- F_{m+2}, and the question is how long such a vector can be while remaining
deletion-minimal.

## Status of the published claim

The manuscript's Theorem 5.2 asserted a bound of r+1 = 4 independent of m. That is false;
it holds at m = 3 only by coincidence, since 2m-2 = 4 there. Withdrawn in the manuscript.

An external oracle asked for the correct bound answered m+1, which is also wrong: at m = 5
the pair 00000100 against 00011000 is a minimal core of length 8 > 6.

## The sharper statement (tick 320): ambiguity dies entirely beyond 2m-2

The search was measuring the wrong thing. Counting *minimal* cores hid the real fact:
for L > 2m-2 there are no ambiguous pairs at all, minimal or otherwise. The counts go to
zero, they do not merely become non-minimal.

    largest L admitting any ambiguity
      m=3 : 4     m=4 : 6     m=5 : 8     m=6 : 10    m=7 : 12
    each equal to 2m-2.

So the sharp statement is not about cores. It is:

    Any two distinct blocks of length >= 2m-1 have different label sequences.

That gives injectivity of Phi_m immediately: if two bi-infinite configurations agreed on
all labels but differed somewhere, a length-(2m-1) window around the difference would be
an ambiguity of length 2m-1 > 2m-2.

This is the question the referee left open - "the conjugacy assertion for m >= 3 may still
be true; I do not have a counterexample" - and the answer looks affirmative, with the
threshold 2m-1 rather than the withdrawn r+1 = 4.

Verified exhaustively for m = 3..7 over all block lengths up to the search cutoff.
NOT PROVED. What is proved so far is only the window-sum lemma above. Anything entering
the manuscript needs the general argument, not five values of m.

## Second lemma (proved, tick 321): a nonzero window forces its right end

**Lemma.** If c in {-1,0,1}^m satisfies sum_{k=1}^m c_k F_{k+1} = F_{m+2}, then c_m = +1.

*Proof.* The lower weights satisfy F_2 + ... + F_m = F_{m+2} - 2. If c_m = 0 then
|sum| <= F_{m+2} - 2 < F_{m+2}. If c_m = -1 then sum <= -F_{m+1} + (F_{m+2} - 2) = F_m - 2,
again below F_{m+2}, using F_{m+2} - F_{m+1} = F_m. Hence c_m = +1. []

Negating gives the mirror statement for -F_{m+2}. So, combined with the first lemma:

    S_i(d) = sigma * F_{m+2} with sigma in {+1,-1}   ==>   d_{i+m-1} = sigma.

Checked exhaustively for m = 3..12: 623 solutions in total, no exception. The numerical
maxima match the proof exactly - the largest attainable value with c_m = 0 is F_{m+2}-2 and
with c_m = -1 is F_m - 2.

**The constraint is one-sided.** The leading coefficient c_1 takes all three values -1, 0, +1
among the solutions, so there is no mirror statement pinning the left end of a window. That
asymmetry is precisely the causal cone the referee pointed at: information propagates from
low positions upward through carries, not symmetrically.

## Where the vanishing theorem still needs work

Proved so far:
  (L1) every window sum is 0 or +/- F_{m+2};
  (L2) a nonzero window sum determines the sign of the window's rightmost coordinate.

Wanted: L <= 2m-2 for any nonzero d all of whose window sums satisfy (L1).

(L2) says the positions where nonzero windows end carry nonzero d-entries with matching
signs. What is missing is the counting step that turns that into a length bound. Note the
witness family has exactly one nonzero window, so the extremal configuration is as sparse as
possible in nonzero windows - the length is not being forced by many nonzero windows.
