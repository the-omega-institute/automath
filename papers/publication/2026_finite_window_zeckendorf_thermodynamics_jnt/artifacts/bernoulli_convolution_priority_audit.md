# Golden-ratio Bernoulli-convolution priority audit

Checked 2026-08-15 against primary papers or journal metadata.  This audit
uses the convention
\[
\tau_\mu(q)=\lim_{n\to\infty}
 \frac{\log\sum_{I\in\mathcal N_n}\mu(I)^q}{\log(\varphi^{-n})}.
\]

## Direct finite-count identification

- N. Sidorov and A. Vershik, *Ergodic properties of the Erdos measure, the
  entropy of the goldenshift, and related problems*, Monatsh. Math. 126
  (1998), 215-261, DOI 10.1007/BF01367764; preprint arXiv:math/9612223.
  Section 2 identifies \(f_n(k)\) both as the number of finite Fibonacci
  representations and as the vertex frequency on level \(n\) of the Fibonacci
  graph, and states that \(2^{-n}f_n(k)\) gives the finite masses converging to
  the Erdos measure.  Thus these are the manuscript's representation
  coefficients up to its unit/index convention, not an analogous object.

## Local dimensions and positive-q spectrum

- T.-Y. Hu, *The local dimensions of the Bernoulli convolution associated
  with the golden number*, Trans. Amer. Math. Soc. 349 (1997), 2917-2940,
  DOI 10.1090/S0002-9947-97-01474-8.  This predates the manuscript's
  normalized log-multiplicity discussion and determines extremal local
  dimensions for the same golden-ratio convolution.
- K.-S. Lau and S.-M. Ngai, *L^q-spectrum of the Bernoulli convolution
  associated with the golden ratio*, Studia Math. 131 (1998), 225-251.
  The paper's main result gives an exact formula for the golden-ratio
  \(L^q\)-spectrum for every \(q>0\).  Its block denominator
  \(Q_J=[1\ 1]P_J(1,1)^T\), block length \(2k+3\), and normalized mass
  \(2^{-(2k+3)}Q_J\) match, respectively, the renewal-letter denominator,
  letter cost, and normalized Fibonacci representation mass used here.

## All-real spectrum and negative phase transition

- D.-J. Feng and E. Olivier, *Multifractal analysis of weak Gibbs measures
  and phase transition: application to some Bernoulli convolutions*, Ergodic
  Theory Dynam. Systems 23 (2003), 1751-1784,
  DOI 10.1017/S0143385703000051.  Theorem 2.9 proves that the Erdos measure is
  weak Gibbs.  Theorem 2.10 gives its complete \(L^q\)-spectrum and a critical
  \(q_c<0\) such that the spectrum is linear exactly for \(q\le q_c\).
  Appendix Theorem A.1 proves nondifferentiability at the critical value.
  The paper explicitly calls this a first-order phase transition.
- D.-J. Feng, *The limited Rademacher functions and Bernoulli convolutions
  associated with Pisot numbers*, Adv. Math. 195 (2005), 24-101,
  DOI 10.1016/j.aim.2004.06.011.  Theorem 1.3(i), proved through the
  golden-ratio calculation in Theorem 4.4, gives the \(L^q\)-spectrum for
  every real \(q\).  It defines \(x(q)\) by the same matrix-block renewal
  series, proves a unique \(q_0<-2\), gives the positive-root branch for
  \(q>q_0\), sets \(x(q)=1\) for \(q\le q_0\), and proves that \(x\) is not
  differentiable at \(q_0\).  Feng's author bibliography records 1999
  preprints containing the underlying Parts I-II; the citable final article
  is 2005.

## Exact normalization and coverage

At level \(m\), a net-interval mass is \(2^{-m}f_m(k)\), while the geometric
scale is \(\varphi^{-m}\).  Therefore
\[
\log\sum_I\mu(I)^t=-mt\log2+\log\sum_k f_m(k)^t
\]
and hence, after the manuscript's finite layer/window index changes,
\[
P(t)=t\log2-\tau_\mu(t)\log\varphi.
\]
Consequently the prior literature covers: existence for every real tilt; the
positive implicit pressure equation; the negative linear/frozen phase; the
negative critical value as the solution of the block-renewal equation; its
first-order nondifferentiability; and the generic Legendre multifractal
formalism.  These cannot be novelty claims of the manuscript.

The present renewal alphabet sums over all reduced \(p/q\in(0,1)\).  At the
critical boundary its letter sum is
\[
\sum_{q\ge2}\varphi_{\rm E}(q)q^{-s}
=\frac{\zeta(s-1)}{\zeta(s)}-1.
\]
Thus Feng's implicit condition becomes
\(\zeta(\sigma_0-1)/\zeta(\sigma_0)=2\).  The located papers do not state this
totient/zeta evaluation, the critical constants \(2/\mu_C\) and \(4/\mu_C\),
the uniform finite-layer coexistence limit, the explicit orbit-filling lower
bound at nonexposed uniform-layer slopes, or the finite-window affine/fiber
identities.  Those are the defensible incremental claims, subject to the
proofs in the manuscript; absence from these sources is not a claim that no
other paper contains them.
