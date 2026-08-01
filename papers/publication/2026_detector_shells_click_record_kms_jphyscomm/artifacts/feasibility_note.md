# Feasibility note: n-state killed-reset D-MAP identifiability

## Decision

A universal labelled-kernel inverse is false, but a sharp minimal-class
dichotomy is attainable. Deterministic reset reduces the visible law to the
scalar Palm tail S_k = e_n^T K^k 1. Standard minimal realization theory says
that two rank-n representations of this sequence differ by a unique
similarity preserving 1 and e_n^T. Therefore a declared subclass is
identifiable, up to its allowed state relabellings, exactly when the
intersection of each such similarity orbit with the subclass's nonnegative
substochastic cone has one declared structural-equivalence class.

This orbit--cone criterion is necessary and sufficient, but its realization
input is established theory rather than a new general phase-type theorem.
The new model-specific conclusion is the location of two opposite classes:

- every minimal interior point of the unrestricted killed-reset cone has a
  continuum visible fibre;
- the pure serial absorption subclass identifies the unordered rate multiset
  for all positive rates, including repeated rates.

Pole collision is therefore not the identifiability boundary. In the serial
model it produces confluent Prony terms and singular finite-sample root
coordinates, while algebraic multiplicity still identifies the repeated rate
at population level. The boundary is the Markovian orbit fibre.

## Scope

The theorem assumes minimal/Hankel rank n. Lower-rank nominal n-state
representations require a separate stratified augmentation theory. For an
arbitrary fixed nonserial zero pattern, deciding the orbit--cone intersection
remains a graph-specific semialgebraic problem. These limitations are explicit
open interfaces in the manuscript.

## Machine evidence

verify_nstate_identifiability.py evaluates representative n=2,3,4 serial
models, including repeated sampled poles. It computes Palm tails and stationary
click moments, reconstructs the order-n Hankel recurrence, verifies full
Hankel rank, checks permutation invariance, runs deterministic fibre searches,
and constructs distinct reset-preserving similarity equivalents with identical
visible tails. The saved output is
artifacts/verify_nstate_identifiability_output.txt.

Exact citations, arXiv API queries, DOI checks, and the restricted novelty
claim are recorded in artifacts/literature_check.md.
