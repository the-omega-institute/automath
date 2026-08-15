# Submission Metadata

## Journal

Journal of Number Theory

## Title

Arithmetic Criticality and Large Deviations for Fibonacci Partitions and
Finite-Window Fibers

## Authors

- Haobo Ma, AELF PTE LTD., Singapore
- Wenlin Zhang, National University of Singapore, Singapore

## 2020 Mathematics Subject Classification

11B39, 05A17, 60F10

## Keywords

Fibonacci partition function; Erdos measure; Bernoulli convolution;
Zeckendorf representation; large deviations

## Summary

The manuscript studies the Fibonacci partition function and an exact
finite-window Zeckendorf fold. It identifies the arithmetic critical parameter
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
coefficient \(2R_s^2\). The manuscript localizes this discrepancy to the
proof of her Lemma 7 and makes no broader claim about that paper.

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
- `supplement.tex`: separately compiled supplement
- `sec_references.tex`: manually maintained bibliography; BibTeX is not used
- Journal of Number Theory cover letter
