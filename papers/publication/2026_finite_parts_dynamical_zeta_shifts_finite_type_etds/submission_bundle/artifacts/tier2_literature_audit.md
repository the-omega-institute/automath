# Tier-2 literature audit

Search date: 2026-08-14. Sources checked: arXiv API and full texts, Crossref
DOI metadata, zbMATH Open API, and the open-problem sections of the cited
papers. Semantic Scholar and OpenAlex API calls returned HTTP 429, so they
did not supply affirmative status evidence. Exact-title and exact-phrase
searches located no later paper claiming to resolve the four questions below;
they are therefore treated as open, not as proved unresolved by this audit.
The later arXiv papers found for linear Mahler equations (arXiv:2308.16765,
2412.04928, and 2503.12995) concern twisted summability or Hahn-series
solutions and do not claim the all-parameter polynomial-time bound in item 3.

1. M. Boyle and S. Schmieding, *Finite group extensions of shifts of finite
   type: K-theory, Parry and Livsic*, Ergodic Theory Dynam. Systems 37 (2017),
   1026-1059, DOI 10.1017/etds.2015.87, Realization Problem 6.1(2):
   "Given a finite abelian group \(G\), characterize the polynomials
   \(\det(I-tA)\) arising from \(G\)-primitive matrices \(A\) over \(\mathbb ZG\)."

2. Boyle-Schmieding, ibid., Realization Problem 6.1(3): "Given a finite group
   \(G\), characterize the trace series \(T_A\) and conjugate trace series
   \(\kappa T_A\) arising from \(G\)-primitive matrices \(A\) over
   \(\mathbb ZG\)."

3. F. Chyzak, T. Dreyfus, P. Dumas, and M. Mezzarobba, *Computing solutions
   of linear Mahler equations*, Math. Comp. 87 (2018), 2977-3021,
   DOI 10.1090/mcom/3359, Section 4.3: "This result leaves open the question
   of devising algorithms for computing solutions of linear Mahler equations
   that run in polynomial time in r and d, for all possible combinations of
   these parameters, even when the trailing coefficient \(\ell_0\) of the
   equation is zero."

4. T. A. O'Hare, *Finite data rigidity for one-dimensional expanding maps*,
   Ergodic Theory Dynam. Systems 45 (2025), 1597-1618,
   DOI 10.1017/etds.2024.83, Introduction: "It would be interesting to study
   finite data rigidity (Theorem 1.3 below) for unimodal and Markov maps as
   well."

## Machinery map

- Problems 1-2: the manuscript computes the realized determinant and
  conjugate trace data and proves their equivalence to primitive class data.
  It does not characterize positivity/realizability and therefore does not
  answer either problem.
- Problem 3: Theorem `thm:effective-rational-mahler-coboundary` gives a
  polynomial-time finite Pade test for one normalized nonlinear order-one
  coboundary equation. It does not cover arbitrary linear Mahler order and
  degree or a vanishing trailing coefficient.
- Problem 4: Theorem `thm:finite-radial-sampling` is exact finite-data
  recovery for a Markov symbolic model. Its data are class Euler values, not
  periodic derivatives, and no distortion estimate transfers it to unimodal
  or Markov maps.

## A/B/C/D audit

- A: none of the named problems is solved.
- B: Proposition `prop:c2-standard-zeta-ratio` canonically identifies the
  binary determinant ratio with a ratio of ordinary Artin-Mazur zeta
  functions of standard two-sheeted covers.
- C: Theorems `thm:determinant-boundary-lifting`,
  `thm:finite-radial-sampling`, and `thm:radial-profile-recovery` no longer
  assume a strict twisted gap in the open Perron interval. The gap is retained
  exactly for endpoint evaluation.
- D: the cubic collision bound is not shown sharp. The four-vertex example
  proves only that one Perron-endpoint sample is insufficient; it is not a
  matching lower bound for the sampling budget.
