
============================================================
1. Overall assessment
Major revision
The main arguments appear technically credible, and I did not find a direct counterexample to Theorems 3.12, 3.16, 3.18, 3.31, or 4.10. In particular, the bounded-mode proof of the infinite-variance direction in Theorem 3.18 and the regularly varying boundary calculation in Theorem 3.16 are substantial.
The present version is nevertheless not acceptable as written because its headline “sharp moment characterization” conflates two different assertions:


a genuinely analytic characterization at order  $t^{-4}$ ; and


a formally defined domain of evaluation for a universal moment polynomial at higher orders.


For  $m\ge3$ , the displayed iff is true largely because Definition 3.4 defines  $A_{2m}(\nu)\in\mathbb R$  to require every moment occurring in the reduced polynomial to exist. The paper does not prove an analytic iff for the entropy remainder at those orders. This distinction is acknowledged locally but obscured in the title, abstract, introduction, and Main Theorem A.
Theorem C also needs a more candid comparison with general relative- $\Phi$ -entropy dissipation for two distributions evolved by the same symmetric jump semigroup. Its value appears to lie in the finite-variance domain verification and endpoint passage, rather than in the Bregman differentiation formula itself.

2. Novelty ratings
These ratings cover every statement formally labelled “Theorem.” The Main Theorems are composite restatements of later results.
TheoremRatingJustificationMain Theorem AHIGHThe unconditional variance threshold is strong; the higher-order “iff,” however, is only a polynomial-domain statement.Main Theorem BMEDIUMThe  $L^\infty\cap L^1$  quotient route and tensor transfer are useful, but largely follow Taylor expansion plus a deliberately strong  $L\ge d+1$  tail bound.Main Theorem CMEDIUMThe finite-variance domain closure is useful, but the underlying two-solution jump-semigroup Bregman identity is structurally standard.Theorem 3.3LOWDirect use of the Chebyshev generating function and parity.Theorem 3.5LOWFormal coefficient extraction from the Taylor series of  $(1+s)\log(1+s)-s$ .Theorem 3.6LOWA useful finite Laurent algorithm, but mathematically an elementary Fourier/constant-term conversion.Theorem 3.7MEDIUMThe nonzero top-moment layer is informative, but the iff depends decisively on the stipulated definition of canonical evaluability.Theorem 3.12MEDIUMA clean exact-moment entropy expansion; its proof is a technically sound Taylor-remainder transfer rather than a fundamentally new semigroup principle.Theorem 3.16HIGHThe truncated-moment normalization and signed  $t^{-2N}\ell_L(t)$  residual under asymmetric regular variation appear genuinely new and sharp within the stated class.Theorem 3.18HIGHThe bounded Cayley-mode/Pinsker argument gives a genuinely analytic and tail-class-free variance iff.Theorem 3.27MEDIUMProvides the multidimensional quotient bridge, although the moment threshold comes from the chosen uniform norm.Theorem 3.34LOWExplicit but routine beta-prime and spherical tensor contractions.Theorem 3.36LOWA standard quadratic entropy transfer criterion; moreover, one of its hypotheses is redundant.Theorem 4.10MEDIUMThe compact-window justification is valuable, but the identity is a specialization of general moving relative-entropy dissipation.Theorem 4.14LOWExplicit substitution of the already established Laurent constants.

3. Issue table
IDSectionSeverityDescriptionSuggested fixI1Abstract; §1; Def. 3.4; Thms. 3.7, 3.12BLOCKERThe central “sharp moment characterization” is presented as an analytic statement, but for  $m\ge3$  it is an iff about a specially defined polynomial-evaluation domain.Recast it as minimality of the absolute-moment assumption for universal polynomial evaluation; reserve “analytic iff” for Theorem 3.18.I2§1, Table 1, Appendix A, §4BLOCKERThe novelty claim for Theorem C is not tested against the general two-solution relative- $\Phi$ -entropy calculus for symmetric jump semigroups.State and compare with the general generator identity; identify finite-variance domain verification as the actual increment.I3Lemma 3.35; Theorem 3.36MEDIUMThe “non-uniform criterion” separately assumes (\int\Phi(\delta_t)-\delta_t^2/2I4§3.4MEDIUMThe restriction  $L\ge d+1$  is explained as sufficient for the  $L^\infty$  quotient route but its sharpness is not established, leaving the reader unsure whether it is intrinsic to KL asymptotics.Add a spike counterexample showing sharpness for uniform quotient convergence, while expressly leaving open weaker  $L^2$ /KL thresholds.I5Def. 3.24; Lemma 3.25MEDIUMThe equivalence (R_{d,L}(t)=o(t^{-L})\iff EX_cI6Throughout §§1, 3, 4MEDIUMThe theorem hierarchy is excessively repetitive: Main A–C, later theorem restatements, a hypothesis ledger, multiple proof roadmaps, two comparator tables, and repeated coefficient routes.Reduce to four primary results and move algebraic certificates and journal-comparison material to a supplement.I7Table 1; Appendix AMEDIUMThe related-work selection is journal- and date-driven rather than mechanism-driven. Several mathematically closer works are absent.Compare with moment expansions of convolution semigroups, relative  $\Phi$ -entropy for jump processes, and general Bregman/Dirichlet-form identities.I8Theorem 3.16; abstractLOW“Tauberian replacement for the unavailable coefficient” may suggest universality beyond the regularly varying divergent-integral subclass.Consistently say “regularly varying boundary replacement”; retain the non-RV limitation currently stated only near Appendix E.I9§4 roadmapLOW“Theorem 4.2” should be “Lemma 4.2.” The phrase “Subsection 3” before Theorem 3.12 is incomplete.Correct cross-references globally.I10Thm. 4.14 and Appendix DLOWNotation such as  $\sigma^6+6\mu_3^2$  is typographically easy to misread, and the order-eight certificate occupies disproportionate space.Use explicit parentheses/subscripts consistently and move Appendix D to ancillary material.I11Reference [9]LOWThe title in the bibliography does not match the current title of arXiv:1702.06573.Reconcile the arXiv and journal records and verify the current publication status before relying on it.

4. Missing or insufficiently discussed references


D. Chafaï, “Entropies, convexity, and functional inequalities: on  $\Phi$ -entropies and  $\Phi$ -Sobolev inequalities,” J. Math. Kyoto Univ. 44 (2004), 325–363.
This is important for relative  $\Phi$ -entropy, biconvexity, and pure-jump Lévy semigroups, and is substantially closer to Theorem C than several entries in Tables 1–2. Primary record


J. Duoandikoetxea and E. Zuazua, “Moments, masses de Dirac et décomposition de fonctions,” C. R. Acad. Sci. Paris Sér. I Math. 315 (1992), 693–698.
This is foundational for moment-based large-time convolution/heat-kernel expansions and should be discussed before claiming novelty for the multidimensional moment jet. Bibliographic record


D. Bakry, T. Coulhon, M. Ledoux, and L. Saloff-Coste, “Sobolev inequalities in disguise,” Indiana Univ. Math. J. 44 (1995), 1033–1074.
Relevant for the early appearance of nonlinear/nonlocal energy forms underlying later Sobolev–Bregman formulas. Author-hosted paper


The comparison with Bogdan–Gutowski–Pietruska-Pałuba, “Polarized Hardy–Stein identity” should be expanded from a table entry into an explicit formula-level comparison: which hypotheses or conclusions of Theorem C are not obtainable by specializing the polarized identity? Preprint record


The bibliography should reconcile Bañuelos–Kim with the current arXiv record, whose title is “On square functions and Fourier multipliers for nonlocal operators.” Current arXiv record



5. Specific improvements needed for acceptance


Make Theorems 3.18 and 3.16 the principal results. They contain the clearest analytic novelty.


Demote Theorem 3.7 to an algebraic minimality proposition unless a genuine higher-order analytic converse is proved.


Reformulate Theorem C as a domain-and-endpoint theorem for the general simultaneous-semigroup relative-entropy identity.


Strengthen Theorem 3.36 by removing its redundant nonlinear assumption.


State precisely that  $L\ge d+1$  is sharp for the chosen  $L^\infty$  quotient topology—not necessarily for existence of the leading KL coefficient.


Replace the manufactured  $R_{d,L}$  hierarchy by a shorter two-region remainder.


Reduce the manuscript substantially. The current 70-page presentation makes elementary coefficient algebra appear coequal with the genuinely new results. A focused version should probably be approximately 40–45 pages, with the order-eight certificate and journal-comparator material separated.


Replace “last-five-years JFA comparators” with a mathematically organized related-work section: convolution moment expansions, stable/fractional entropy dissipation, jump-semigroup Bregman identities, and Cauchy-family divergence formulas.



6. Concrete fixes for BLOCKER and MEDIUM issues
I1 — Correct the status of the higher-order “iff”
Replace the first clause of Main Theorem A by something of the following form:

For  $m\ge2$ , let  $\mathcal A_{2m}\in\mathbb Q[m_2,\ldots,m_{2m-2}]$  be the reduced universal polynomial defined by the constant-term rule. Then

$$\mathcal A_{2m}
=\kappa_m m_2m_{2m-2}
+P_m(m_2,\ldots,m_{2m-3}),
\qquad
\kappa_m=(-1)^m(m-1)2^{-2m+2}\ne0.$$

Consequently  $E|X_c|^{2m-2}<\infty$  is sufficient for evaluating every monomial of  $\mathcal A_{2m}$ , and it is the minimal absolute-moment assumption that guarantees such evaluation uniformly over all centred probability laws.

Then state separately:

$$E X_c^2<\infty
\quad\Longleftrightarrow\quad
\limsup_{t\to\infty}t^4H(t)<\infty,$$

which is the genuine analytic iff.
For  $m\ge3$ , the paper already has the appropriate analytic boundary statement inside the regularly varying class:

$$\frac{t^{2m}}{M_{2m-2}(t)}
\left(
H(t)-\sum_{j=2}^{m-1}A_{2j}t^{-2j}
\right)
\longrightarrow \kappa_m\mu_2.$$

This should be advertised as a class-conditional analytic sharpness theorem, not used to suggest an unconditional higher-order iff.
I2 — Place Theorem C within the general jump-semigroup formula
For a symmetric jump generator

$$Lf(x)=\int\bigl(f(y)-f(x)\bigr)J(x,y)\,dy,
\qquad J(x,y)=J(y,x),$$

and two solutions  $\partial_t h_t=Lh_t$ ,  $\partial_t g_t=Lg_t$ , put  $u_t=h_t/g_t$ . The formal identity is

$$-\frac{d}{dt}D_{\mathrm{KL}}(h_t\|g_t)
=
\frac12\iint J(x,y)
\left[
g_t(x)\Lambda(u_t(x),u_t(y))
+
g_t(y)\Lambda(u_t(y),u_t(x))
\right]dx\,dy.$$

By exchanging  $x$  and  $y$  in the second term,

$$-\frac{d}{dt}D_{\mathrm{KL}}(h_t\|g_t)
=
\iint J(x,y)g_t(x)\Lambda(u_t(x),u_t(y))\,dx\,dy.$$

For the Cauchy generator,

$$J(x,y)=\frac1{\pi(x-y)^2},$$

which is exactly the paper’s  $I_\nu(t)$ .
Therefore the theorem’s defensible new content should be stated as:


finite variance implies uniform compact-window upper and lower bounds for  $u_t$ ;


the required noncompact Green pairings are valid;


the Bregman kernel is integrably dominated;


 $H(T)\to0$ , permitting integration to infinity.


The paper should say explicitly whether any cited general theorem already supplies part of this package.
I3 — Remove the redundant hypothesis in Lemma 3.35
Let  $z_t=t^2\delta_t$  and suppose  $z_t\to b$  in  $L^2(\lambda)$ . Define

$$r(s)=
\begin{cases}
\dfrac{\Phi(s)-s^2/2}{s^2},&s\ne0,\\[4pt]
0,&s=0.
\end{cases}$$

For  $\Phi(s)=(1+s)\log(1+s)-s$ ,  $r$  is bounded on  $[-1,\infty)$  and continuous at zero. Then

$$t^4\int\left|\Phi(\delta_t)-\frac12\delta_t^2\right|d\lambda
=
\int
\left|r\!\left(\frac{z_t}{t^2}\right)\right|z_t^2\,d\lambda.$$

Because  $z_t\to b$  in  $L^2$ , the family  $z_t^2$  is uniformly integrable, while  $z_t/t^2\to0$  in probability. Vitali’s theorem therefore yields

$$\int
\left|r\!\left(\frac{z_t}{t^2}\right)\right|z_t^2\,d\lambda
\longrightarrow0.$$

Thus Lemma 3.35 can be strengthened to:

$$t^2\delta_t\to b\quad\text{in }L^2
\quad\Longrightarrow\quad
\int\Phi(\delta_t)\,d\lambda
=
\frac{t^{-4}}2\int b^2\,d\lambda+o(t^{-4}).$$

No separate nonlinear-integrand hypothesis is needed.
I4 — Establish the sharp scope of  $L\ge d+1$ 
The manuscript can prove that  $L\ge d+1$  is sharp for its uniform quotient topology.
For  $L<d+1$ , choose  $R_n\uparrow\infty$  rapidly and set

$$w_n=R_n^{-L}n^{-2},\qquad
\nu=(1-W)\delta_0+\sum_{n\ge1}\frac{w_n}{2}
\bigl(\delta_{R_ne_1}+\delta_{-R_ne_1}\bigr).$$

Then

$$E|X|^L=\sum_{n\ge1}w_nR_n^L=\sum_{n\ge1}n^{-2}<\infty.$$

Set

$$t_n=8^{-1/(d+1)}
R_n^{(d+1-L)/(d+1)}n^{-2/(d+1)},$$

choosing  $R_n$  so that  $t_n\to\infty$ . At  $x_n=R_ne_1$ ,

$$\frac{(P_{t_n}^{(d)}*\nu)(x_n)}
{P_{t_n}^{(d)}(x_n)}
\ge
\frac{w_n}{2}
\frac{P_{t_n}^{(d)}(0)}
{P_{t_n}^{(d)}(R_ne_1)}
\ge
\frac{w_n}{2}\left(\frac{R_n}{t_n}\right)^{d+1}
=4.$$

Hence  $\|\delta_{t_n}^{(d)}\|_\infty\ge3$ , despite the finite  $L$ -moment. This proves that  $L=d+1$  is the correct threshold for the paper’s uniform quotient strategy.
The authors must then add:

This does not prove that  $d+1$  moments are necessary for the leading KL asymptotic under a weaker  $L^2(\Omega_d)$  or entropy topology.

I5 — Simplify the two-region remainder
For  $L\ge d+1$ , every far-region term in (3.36) is bounded by the top tail term. Replace  $R_{d,L}$  by

$$\widetilde R_{d,L}(t)
=
t^{-(L+1)}
E\!\left[|X_c|^{L+1};\,|X_c|\le t\right]
+
t^{-L}
E\!\left[|X_c|^L;\,|X_c|>t\right].$$

Indeed, for  $d+1\le k\le L$  and  $|X_c|>t$ ,

$$t^{-k}|X_c|^k
\le t^{-L}|X_c|^L.$$

Similarly,

$$t^{-(d+1)}|X_c|^{d+1}
\le t^{-L}|X_c|^L.$$

Thus the existing  $R_{d,L}$  is bounded by a constant depending only on  $d,L$  times  $\widetilde R_{d,L}$ , and

$$E|X_c|^L<\infty
\quad\Longrightarrow\quad
\widetilde R_{d,L}(t)=o(t^{-L})$$

by dominated convergence and tail integrability. This is shorter and makes clear that the equivalence is a technical encoding of the moment assumption.
I6 — Reorganize the theorem hierarchy
A substantially clearer structure would be:


Theorem A: finite-moment coefficient expansion and Laurent rule.


Theorem B: unconditional variance threshold.


Theorem C: regularly varying boundary residual.


Theorem D: multidimensional quotient/KL expansion.


Proposition: moving Cauchy relative-entropy domain and tail identity.


The current Main Theorem A combines a formal-domain result, an analytic iff, and supporting expansion machinery of very different strength. Splitting these claims would materially improve the paper’s logical precision.
I7 — Replace journal-driven comparison with mathematical comparison
The related-work section should compare formulas, not journal venues. At minimum, it should answer:


Which classical moment-expansion results already yield

$$P_t*\nu=\sum_{|\alpha|\le L}
\frac{(-1)^{|\alpha|}}{\alpha!}\mu_\alpha\,\partial^\alpha P_t
+\text{remainder}?$$



What is new in passing from that density expansion to the matched quotient and then to KL?


Which general relative- $\Phi$ -entropy identity already gives the derivative of  $D_\Phi(P_t\mu\|P_t\eta)$ ?


Which part of the finite-variance domain verification is specific to the Cauchy kernel?


Is the Cayley transform essential to the theorem, or primarily an efficient coefficient-evaluation device?


Answering these questions directly would make the genuine contribution—especially Theorems 3.16 and 3.18—considerably more convincing.
