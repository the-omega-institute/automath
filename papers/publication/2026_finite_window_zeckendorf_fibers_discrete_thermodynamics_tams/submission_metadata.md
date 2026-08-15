# Submission Metadata

## Journal

Transactions of the American Mathematical Society

## Title

Condensation in Denominator-Weighted Brocot Fractions and Fibonacci Partition
Thermodynamics

## Authors

- Haobo Ma, AELF PTE LTD., Singapore
- Wenlin Zhang, National University of Singapore, Singapore

## 2020 Mathematics Subject Classification

11A55, 11B39, 60F10, 05A17

## Keywords

Brocot fractions; continued fractions; continuants; condensation; Fibonacci
partition function; large deviations

## Summary

The manuscript's central result is a total-variation condensation theorem for
canonical Brocot fractions of fixed order (n), sampled with probability
proportional to the inverse (s)-th power of the denominator, (s>2). With
probability tending to one there is a unique partial quotient larger than
(n/2); its left and right words converge to explicit independent
inverse-continuant laws. The theorem gives the exact defect distribution, the
joint location/side-length limit, and an asymptotic denominator factorization.

The same fixed-order estimate is the arithmetic input for the Fibonacci
partition function and an exact finite-window Zeckendorf fold. It identifies
the arithmetic critical parameter
by

\[
\frac{\zeta(\sigma_0-1)}{\zeta(\sigma_0)}=2,
\]

identifies the local denominator-layer sum exactly with Dushistova's
fixed-digit-sum continuant sum, corrects its printed leading coefficient from
\(R_s+2R_s^2\) to \(2R_s^2\), and gives a simplified
one-large-partial-quotient proof. It then derives the critical cost tail and
the second-order \(m^{3-\sigma_0}\) corrections beyond the leading constants
\(2/\mu_C\) and \(4/\mu_C\). It also proves uniform coexistence limits and
finite-layer large deviations at nonexposed slopes, and establishes exact
finite-window fiber identities. On
each fixed finite prime support it retains an exact rational coefficient
generating function. It asserts no directional coefficient asymptotic and no
quenched-velocity asymptotic.

## Relation To Prior Results

Sidorov and Vershik use \(F^{\mathrm{SV}}_1=1\) and
\(F^{\mathrm{SV}}_2=2\), so their indexing is

\[
F^{\mathrm{SV}}_j=F_{j+1}.
\]

Their finite representation frequency \(f_m(k)\) is therefore the same raw
finite Fibonacci subset-sum coefficient used in the manuscript, after this
index shift, and \(2^{-m}f_m(k)\) gives the finite masses approximating the
Erdos measure. Hu treated local dimensions of the golden-ratio Bernoulli
convolution. Lau and Ngai determined its positive-\(q\) \(L^q\)-spectrum.
Feng--Olivier and Feng determined the all-real spectrum and its negative
first-order phase transition.

Moshchevitin and Zhigljavsky studied the global entropy of Farey-tree
partitions. Dushistova subsequently defined the identical fixed-digit-sum
continuant sum and stated a fuller expansion. Under \(s=2\beta\) and
\(n=d+1\), the exact identity is

\[
b_{2d+1}(s)=\sigma_{s/2}(d+1).
\]

Her printed leading coefficient is \(R_s+2R_s^2\); separating the left
contexts of digit sums zero, one, and greater than one gives the corrected
coefficient \(2R_s^2\). The manuscript localizes this discrepancy to the loss
of the restriction \(u>1\), causing an endpoint overcount, in the proof of her
Lemma 7: the empty left context is included in the doubled canonical
convolution, so that endpoint is counted twice and the excess is exactly
\(R_s\). It makes no broader claim about that paper.

Armendariz--Loulakis prove conditional product limits for independent
subexponential variables, and Stufler proves total-variation condensation for
product-weighted Gibbs partitions. Neither theorem applies directly here:
\(\mathcal K(a_1,\ldots,a_r)^{-s}\) is not a product of component weights.
The manuscript proves the required two-sided continuant factorization,
summable domination, and negligibility of every noncondensed word before
applying the discrete Scheffe lemma.

With

\[
\tau_\mu(t)=\lim\frac{\log\sum_I\mu(I)^t}{\log|I|},
\]

the exact normalization used throughout the submission is

\[
P(t)=t\log 2-\tau_\mu(t)\log\varphi.
\]

Accordingly, the all-real pressure formula and the frozen negative branch are
recorded as attributed recovery and consistency results. The surviving
contributions are the arithmetic evaluation of the critical point, the
one-sided critical moment, the corrected local denominator-layer constant and
simplified proof, the new renewal/Fibonacci transfer to stable second-order
critical finite-size laws and coexistence laws, the finite-layer
nonexposed-slope lower bounds, and the exact finite-window correspondences and
identities.

## Venue Positioning

The primary submission target is *Transactions of the American Mathematical
Society*, as an honest ambitious test rather than the predicted outcome. The
current external assessment places technical correctness of the condensation
theorem at 92--95 percent, survival of the novelty boundary before an informed
specialist referee at 75--80 percent, and the probability that the complete
73-page package clears the *Transactions* significance and coherence bar at
roughly 35--45 percent. The principal editorial risk is architecture and
significance density, not a gap in Theorem 2.1 or direct subsumption by the
product-weight condensation literature.

The most natural median outcome is *Journal of Number Theory*. That venue is
the predicted natural level for the arithmetic continued-fraction theorem,
the Dushistova correction, and the downstream Fibonacci partition results.
*Ergodic Theory and Dynamical Systems* is demoted below it: the manuscript
attributes the all-real pressure and its phase transition to prior work and
disclaims new pointwise local dimensions, multifractal spectra, finite-type
neighbour graphs, net intervals, transition matrices, normalization
transducers, transfer operators, and Stern--Brocot multifractal results. The
new centerpiece is therefore arithmetic and probabilistic rather than
dynamical. Nothing in the present package supports a venue above
*Transactions*.

In the assessor's summary, this is "a strong number-theory paper with a real,
novel structural centerpiece; a credible but borderline TAMS paper; and a
very strong JNT paper." The corresponding submission judgment is:
"Transactions is now the right level to test, but not the level I would
predict."

## Exact Scope Of Finite Formulas

The affine fiber--partition correspondence and partition-difference formula
hold for every integer \(m\ge 1\). The two-interval fiber identity itself is
stated for \(m\ge 0\).

For the maximizing-residue formulas, write \(G_j=F_{j+1}\). The odd-index
quantity

\[
I_{2k+1}=
\begin{cases}
G_{k+1}G_{k-3}+1,&k\text{ even},\\
G_kG_{k-2}+1,&k\text{ odd}
\end{cases}
\]

is defined only for \(k\ge 5\). The even-index quantities

\[
I_{2k}=
\begin{cases}
G_{k+2}G_{k-5}+G_3+1,&k\text{ even},\\
G_{k+1}G_{k-4}+G_3+1,&k\text{ odd}
\end{cases}
\]

and

\[
J_{2k}=
\begin{cases}
G_{k+1}G_{k-3}+1,&k\text{ even},\\
G_kG_{k-2}+1,&k\text{ odd}
\end{cases}
\]

are defined only for \(k\ge 7\). The exceptional initial maximizing residues
are listed separately in the manuscript and are not obtained by extending
these generic formulas below their stated ranges.

The largest-fiber values have their own ranges:

\[
D_0=D_1=1,\qquad D_{2k}=F_{k+2}\quad(k\ge0),\qquad
D_{2k+1}=2F_{k+1}\quad(k\ge1),
\]

and the recurrence \(D_m=D_{m-2}+D_{m-4}\) holds for \(m\ge6\).

## Submission Files

- `main.tex` and its section inputs: main article
- `sec_brocot_condensation.tex`: central fixed-order continued-fraction theorem
- `supplement.tex`: separately compiled supplement
- `sec_references.tex`: manually maintained bibliography; BibTeX is not used
- Transactions of the American Mathematical Society cover letter

## Assessed Structural Alternative - Awaiting Author Decision

This is additional decision information only; it does not change the recorded
target or status above. The assessor's definite verdict was to **SPLIT**.
Paper A - Brocot condensation, the Dushistova correction, and only those
Fibonacci consequences that genuinely depend on the scalar denominator-layer
asymptotic - was estimated at 30-34 pages, with TAMS 55-65 percent and JNT
82-90 percent. Paper B - the autonomous finite-window identities, extremal
transfers, pressure recoveries and large-deviation package - was estimated at
42-48 pages, with TAMS 10-20 percent and JNT 50-65 percent, and remains
independently publishable.

The present combined 73-page article was assessed at 35-45 percent at TAMS,
with JNT the predicted median. A single article plus large supplement was
assessed at 45-55 percent and explicitly **NOT recommended**. The assessor's
author-level decision was: two papers, Paper A to TAMS first, Paper B to JNT.
Full report: `artifacts/oracle_sprint_A6_split_value.md`.
