# Feasibility note: n-state killed-reset D-MAP identifiability

## Decision

A strong new identifiability theorem for general n-state killed-reset D-MAPs
is not warranted. Killed reset makes the visible record a renewal process, so
the record determines the scalar discrete phase-type gap law. It does not
determine a labelled hidden realization. Minimal scalar realizations are
unique only up to similarity, and the intersection of a similarity orbit with
the nonnegative substochastic matrices can contain multiple Markovian
representatives. This is the established phase-type/MAP nonuniqueness problem,
not a new hidden-Markov identifiability theorem.

The relevant literature boundary is represented in the manuscript by Ryden
(1996) on identifiability and order, O'Cinneide (1989) on non-unique phase-type
representations, Ramirez-Cobo and Lillo (2012) on weakly equivalent MAP2/MAP3
processes, and Bladt and Nielsen (2017) on matrix-exponential/phase-type
realizations. Generic HMM identifiability results do not identify a preferred
rate tuple in this transition-labelled deterministic-reset class.

## Tractable restricted chart

If one adds the substantive hypothesis that the hidden process is a serial
n-phase sampled absorption chain, then the Palm gap tail is an exponential
sum with sampled poles `exp(-theta_i Delta)`. Standard Hankel/Prony realization
recovers those poles, and therefore the unordered rates, under minimality. The
manuscript now proves the explicit n=3, pairwise-distinct case: `S_0,...,S_5`
form two 3 by 3 Hankel matrices whose generalized eigenvalues are the three
sampled survival factors. The exact labelled fibre in this restricted chart
is the permutation orbit.

This is a useful modest increment because it gives an explicit visible
inverse in the first dimension beyond the paper's two-state model. It is not
presented as a new general realization theorem. Repeated-rate strata are not
covered by the proposition; they require confluent coordinates and are
numerically ill-conditioned, although they belong to standard realization
theory rather than constituting evidence for a new hidden-kernel inverse.

## Machine evidence

`verify_nstate_identifiability.py` constructs explicit serial killed-reset
D-MAPs for n=2 and n=3, computes Palm tail and stationary click-inclusion
coordinates, recovers sampled poles by a Hankel pencil, checks all rate
permutations, runs deterministic multistart and random nearest-pair searches,
and constructs non-serial stochastic-similarity equivalents. For the tested
serial examples, no fibre beyond permutations was found. For both n=2 and
n=3, the script exhibits a distinct nonnegative killed-reset kernel with the
same visible tails to numerical precision, confirming that killed reset alone
does not identify the hidden kernel.

Recommendation: retain the explicit n=3 serial proposition as a modest
increment. Do not claim general n-state hidden-rate identifiability unless a
future paper first fixes a canonical structured representation and treats the
minimality and collision strata explicitly.
