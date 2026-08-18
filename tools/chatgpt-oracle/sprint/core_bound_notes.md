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
