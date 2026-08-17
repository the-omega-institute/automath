1. Verdict: minor revision
Single strongest reason: the manuscript materially overstates the generality of its polynomial-tail theorem. The abstract claims an optimal exponent “for every smooth polynomial-tail kernel,” but the actual theorem requires bounded normalized derivatives through a kernel-dependent order. Smoothness and two-sided polynomial decay alone do not imply those bounds.  
I do not see a corresponding defect in the principal proofs. In particular, the finite-entropy/no-moment dissipation argument is sound. This is therefore a minor revision, not a major revision.
2. JFA significance threshold
Yes. The complete manuscript clears the Journal of Functional Analysis significance threshold. It is not merely correct but too small.
The reason is not the basic two-solution entropy identity, whose algebra is classical. The JFA-level contribution is the combination of:


the all-order first-unmatched-tensor asymptotic with the exact endpoint moment exponent, endpoint sufficiency, and matching counterexamples below that endpoint; 


the genuinely separate second threshold for power divergences, including the distinction between failure of the asymptotic and divergence being infinite at every scale; 


the positive tail-jet decomposition, which identifies a nonnegative law-by-law obstruction rather than replacing it with another sufficient moment condition; 


the sharp extension from stable kernels to an explicit polynomial-tail kernel class. 


That is a real theorem package, not a technical note. The subject is also squarely within the journal’s current Hardy–Stein/Bregman-form territory; JFA recently published closely adjacent work on polarized Hardy–Stein identities. 科学直通车
A paper consisting only of Theorems 3.2 and 3.4 would probably be too small for JFA; Potential Analysis would be a more natural size for that isolated contribution. That is not the manuscript presently submitted.
3. The first hostile attack
The vulnerable sentence is the abstract’s claim:

“we identify the optimal uniform complete-moment exponent for every smooth polynomial-tail kernel”


That statement is false at the level of generality in which it is written. Theorem 6.8 assumes not only that p is positive, smooth, and satisfies
p(y)≍(1+∣y∣)−β,
but also
1≤∣γ∣≤m+1max​​p∂γp​​∞​<∞.

These derivative bounds are not automatic. In one dimension, for example,
p(x)=Z−1(1+x2)−β/2(2+sin(ex2)),β>1,
is strictly positive, C∞, and comparable above and below with (1+∣x∣)−β, but p′/p is unbounded because of the rapidly oscillating factor. Thus it is a smooth polynomial-tail density in the ordinary meaning of those words but lies outside Theorem 6.8.
More importantly, the extra hypothesis is used at the critical step: it controls the Taylor remainder of the normalized translate quotient and produces the global Lq estimate (6.43). Without it, the proof does not go through, and no replacement argument is supplied. 
A hostile referee can therefore say that the headline kernel class is broader than the proved class. This is not harmless promotional language because the claimed breadth is part of the paper’s significance case. The correction is straightforward but necessary: everywhere in the abstract and introduction, replace “every smooth polynomial-tail kernel” with something such as “every strictly positive polynomial-tail kernel satisfying the normalized derivative bounds (6.37)”. Do not suggest those bounds follow from smoothness and tail comparability.
4. The no-moment dissipation argument
Yes, the simultaneous removal is justified. Monotone convergence is not hiding an illicit interchange. The important point is that the proof does not pass n→∞ through a time derivative. It passes to the limit only after obtaining an integrated identity for each fixed n.
For fixed n, Φn′​ and
χn​(r)=Φn​(r)−rΦn′​(r)
are bounded. Hence the two Green pairings in
Hn′​(t)=−∫Φn′​(ut​)Aft​−∫χn​(ut​)Agt​
exist separately: ft​,gt​∈W2,1, the annular generators converge in L1, and the test functions are bounded. No cancellation between two divergent quantities is being used. 
On a finite annulus, the algebra produces the nonnegative symmetrized integrand
gt​(x)Λn​(ut​(x),ut​(y))+gt​(y)Λn​(ut​(y),ut​(x)).
Taking, for example, the nested annuli
{k−1<∣x−y∣<k},
monotone convergence removes the jump cutoff. Because the two individual Green pairings already have finite limits, this also proves that the resulting truncated jump form Iα,d(n)​(t) is finite at the relevant times. 
The second monotonicity, in n, is genuine. For a≥b,
Λn​(a,b)=∫ba​(a−r)r1[1/n,n]​(r)​dr,
while for a<b,
Λn​(a,b)=∫ab​(r−a)r1[1/n,n]​(r)​dr.
The weights are nonnegative and the intervals [1/n,n] increase with n, so
Λn​(a,b)↑Λ(a,b).
The same nested-second-derivative argument gives Φn​↑Φ.
Crucially, the authors then integrate the fixed-n derivative identity before removing n:
Hn​(s)−Hn​(t)=∫st​Iα,d(n)​(r)dr.
At this point:
Hn​(s)↑H(s),Hn​(t)↑H(t),
and data processing gives
H(s),H(t)≤DKL​(μ∥ν)<∞.
Therefore
Hn​(s)−Hn​(t)⟶H(s)−H(t);
there is no ∞−∞ problem. On the right,
Iα,d(n)​(r)↑Iα,d​(r),
so monotone convergence in time gives
n→∞lim​∫st​Iα,d(n)​(r)dr=∫st​Iα,d​(r)dr.
This yields
H(s)−H(t)=∫st​Iα,d​(r)dr<∞,
which simultaneously proves local integrability of Iα,d​, local absolute continuity of H, and the almost-everywhere derivative identity. 
So data processing is doing only one job: it ensures that the two endpoint entropies are finite. It is not being used as a substitute for convergence of derivatives or jump forms. The limit order is:
fix n⟶remove annular cutoff⟶integrate in time⟶n→∞.
That order is legitimate. I would ask the authors to write the nested annular sequence explicitly and emphasize that they never claim Hn′​→H′, but this is an expositional tightening, not a mathematical gap.
