1. Overall assessment
Major revision
I found no counterexample to Theorems A–E, 3.33, or 3.40. The principal two-state identities are algebraically consistent, and I independently reproduced the Appendix B covariance calculation:

$$\Sigma_\sigma(1/2)\approx
\begin{pmatrix}
25.06452279&17.22225932\\
17.22225932&11.88846499
\end{pmatrix},
\qquad
\det\Sigma_\sigma(1/2)\approx1.372485374>0.$$

The recommendation is nevertheless major revision because:


the novelty claims are not evaluated against the closest discrete phase-type and order-two DMAP canonical-representation literature;


the higher-state “sharp boundary” is largely a reformulation of minimal-realization uniqueness;


Theorem E stops at an oracle, single-point calibration and does not establish coverage for the feasible statistic described later;


quantitative conditioning and uniformity near the quotient and root singularities are absent;


the 123-page presentation is disproportionate to the mathematical contribution and substantially obscures the original content.


The first two issues below are publication blockers rather than demonstrated counterexamples.
2. Novelty ratings
ResultRatingJustificationTheorem AMEDIUMThe exact combination of gap law, monotone hazard, covariance tail, 1-dependence threshold, and non-Markovianity is useful for this constrained kernel, but follows from elementary two-state spectral and renewal calculations.Theorem BMEDIUMThe three-inclusion quotient formula is the manuscript’s strongest potentially original result, but its distinction from existing order-two DMAP canonical-coordinate theory has not been established.Theorem CLOWThis is a standard regenerative reward CLT with model-specific bookkeeping for the three inclusion statistics.Theorem DLOWIt is the ordinary multivariate delta method applied to Theorems B and C; the more relevant root/rate transport is relegated to Corollary 3.86.Theorem ELOWThe tangent-cone projection limit is standard boundary asymptotics; novelty is limited to a numerical full-rank certificate at one fixed point  $z_0=1/2$ .Theorem 3.33LOWContinuum nonidentifiability follows from standard minimal-realization similarity and openness of the interior Markov cone.Theorem 3.40LOWThis is a separated-batch covariance consistency argument for 1-dependent regenerative rewards.Corollary 3.32, although not formally a theoremMEDIUMRecovery of repeated serial rates from finitely many sampled survival coordinates is potentially useful, but it is closely connected to established confluent-Prony and acyclic DPH canonical-form results.
No theorem presently merits a HIGH novelty rating without a substantially more convincing comparison to the direct prior literature.
3. Issue table
IDSectionSeverityDescriptionSuggested fixB1§§1.2–1.3, 3.3.1, 4BLOCKERNovelty is not established against canonical order-two DMAP, discrete PH, and minimal MAP representation results. Proposition 3.31(ii)—identifiability iff the orbit fibre is a singleton—is essentially definitional once standard minimal-realization uniqueness is invoked.Add a theorem-by-theorem comparison with the direct literature; demote standard realization facts; strengthen Theorem 3.33 to a quantitative orbit-dimension result or solve a genuinely nontrivial structured fibre.B2§3.4, Theorem E, §§3.5 and A.1BLOCKERTheorem E uses the population covariance and limiting critical value and treats only the preselected point  $z_0=1/2$ . The optional conditional plug-in convergence is not converted into a feasible coverage theorem. Thus the lengthy diagonal-inference development ends before an operational inferential result.State and prove coverage for the plug-in statistic and conditional simulated critical value; otherwise remove the confidence-procedure rhetoric and present E only as a pointwise projection example.M1Theorems B–D, §§3.23–3.37MEDIUMAll inverse and delta-method results are pointwise. No lower bound is given for  $r_0$ , (r_1-r_0^2M2Theorem D; Corollary 3.86MEDIUMThe headline delta-method theorem stops at  $(p+s,ps)$ . The visible, canonically ordered root/rate CLT is not stated in Theorem D; the later corollary instead emphasizes an externally labelled branch.State a sorted-root CLT, which requires no external label, and its log-rate push-forward directly in Theorem D.M3Theorem 3.40, Lemma 1.5, Appendix AMEDIUMThe stopped separated-batch proof has the correct outline, but the passage from deterministic independent prefixes to the random  $M_N$ , and the uniform plug-in perturbation, are compressed into references to “usual” inequalities. The required triangular-array probability bound is not displayed.Add the explicit maximal and Chernoff/union bounds given below.M4Assumption 1.1; Proposition 1.3; §5.1MEDIUMThe phrase “classical sampled counter” is too broad. The kernel requires a latching rule that kills all post-click evolution until the next boundary. A continuously recovering detector need not satisfy  $T_1(\cdot,R)=0$ .Give an explicit within-bin protocol deriving every kernel entry, narrow the physical terminology, and compare with continuous exponential-recovery models.M5Appendix B; Data availabilityMEDIUMThe supplied material did not include the claimed replay script, JSON transcript, environment, or hash. The printed intervals are numerically consistent, but the directed-rounding claim cannot be mechanically reproduced from the submitted files.Supply the complete replay archive or replace the machine dependency with a short analytic interval proof.M6Entire manuscriptMEDIUMResults are repeatedly stated as A–E, detailed propositions, supporting lemmas, later corollaries, and appendix interfaces. Extensive disclaimers and protocol material obscure the mathematical contribution. At 123 pages, the article is not publication-ready.Reduce the main paper to approximately 40–50 pages and move duplicated statements, algorithms, diagnostics, comparator tables, and certificate transcripts to a supplement.L1Corollary 3.30LOW“Complete quotient coordinates” proves sufficiency for reconstructing the visible law, not cardinality minimality.Define “complete” explicitly as law-determining, or use “finite generating coordinates.”L2Theorem ALOW“Exact 1-dependent” should explicitly exclude 0-dependence.Add  $\gamma_1=\rho(a-\rho)<0$ , hence adjacent observations are not independent.L3§§1.1, 3.5LOWThe diagnostics have no stated size, power, or post-selection guarantee. The disclaimers are correct, but applications could still misread the resulting reports as model-validated.Keep all inferential claims explicitly conditional on Assumption 1.1 or introduce an independent/split-sample model check.L4Assumption 3.56 and reporting gatesLOWConditions such as  $M_N\ge2$  and fixed  $K_{\min}$  are asymptotically harmless but allow extremely unstable finite reports.For operational reporting, require  $M_N\ge m_N$ , where  $m_N\to\infty$  and  $m_N=o(N/b_N)$ .L5ThroughoutLOWThere are duplicated cross-references (“Theorem C, Theorem C”), inconsistent capitalization, overloaded cycle-count notation, and unusually long scope paragraphs.Perform a full notation and copy-editing pass after restructuring.L6Tables and navigationLOWThe dense comparison tables are difficult to read, and a 123-page manuscript lacks adequate navigational structure.Shorten the tables, add a contents/road-map section if the paper remains long, and move bibliographic comparisons to the supplement.
4. Missing references
The following are directly relevant and should be discussed, not merely appended to the bibliography:


Mészáros and Telek, “Canonical Representation of Discrete Order 2 MAP and RAP” (2013). This is the closest omitted reference for order-two DMAP canonical representations and is essential for assessing Theorem B’s novelty.


Telek and Horváth, “A minimal representation of Markov arrival processes and a moments matching method” (2007). Directly relevant to Proposition 3.31 and the finite-coordinate realization discussion.


Bobbio, Horváth, Scarpa, and Telek, “Acyclic discrete phase type distributions: properties and a parameter estimation algorithm” (2003). Relevant to the sampled serial absorption-time representation and Corollary 3.32.


Papp and Telek, “Canonical representation of discrete phase type distributions of order 2 and 3” (2013). Particularly relevant to pole collisions, repeated geometric factors, and canonical DPH coordinates.


Mészáros, Papp, and Telek, “Fitting traffic traces with discrete canonical phase type distributions and Markov arrival processes” (2014). Relevant to the practical and inferential significance of discrete canonical DMAP/DPH representations.


Cumani, “On the canonical representation of homogeneous Markov processes modelling failure-time distributions” (1982), and O’Cinneide, “Phase-type distributions and invariant polytopes” (1991). These are important predecessors for serial/bidiagonal forms and representation nonuniqueness.


Kalman, “Mathematical Description of Linear Dynamical Systems” (1963). This should at least be acknowledged as the classical origin of the controllable/observable minimal-realization uniqueness used in Proposition 3.31.


Krause and Walenta, “Exponential-recovery model for free-running SPADs with capacity-induced dead-time imperfections” (2025). This is a particularly close physical comparator: it treats exponential detector recovery and parameter extraction from inter-detection intervals.


5. Specific improvements needed to reach acceptance


Establish precisely what is new relative to order-two DMAP and discrete PH canonical-representation theory. Each claimed contribution should be identified as either a new theorem, a specialization yielding a simpler formula, or a standard tool.


Make the quotient inversion the mathematical center of the paper. If its formula is not already implicit in the canonical DMAP2 literature, explain exactly why the three low-order inclusion probabilities provide a simpler or structurally different inverse.


Either complete Theorem E with a feasible plug-in calibration theorem or remove most of the diagonal confidence-procedure apparatus. An oracle single-point event does not justify the present inferential emphasis.


Add explicit stable parameter regions and conditioning bounds. Pointwise consistency alone is inadequate when the quotient denominator and root discriminant can approach zero.


State the identifiable unordered root/rate CLT in the main theorem block. External side data are needed only to attach the physical labels  $\Gamma$  and  $\kappa_r$ , not to impose a canonical numerical ordering on the roots.


Complete the stopped-batch proof with explicit maximal inequalities, rather than relying on compressed prose.


Derive the killed-leakage kernel from a precise latched measurement protocol and narrow the physical claims accordingly.


Supply the certificate replay materials and substantially shorten the manuscript. If the novelty analysis shows that the higher-state results are standard consequences, they should be condensed to a short section or appendix.


6. Concrete fixes
B1 — Replace the “sharp boundary” claim with a substantive structural result
Proposition 3.31(i) can be retained as a standard minimal-realization lemma. Part (ii) should not itself be presented as a new sharp boundary: after defining

$$\mathcal F_{\mathcal C}(K)=
\{M^{-1}KM\in\mathcal C:M\mathbf1=\mathbf1,\ \beta M=\beta\}/\!\sim_{\mathcal C},$$

the assertion “identifiable iff  $\#\mathcal F_{\mathcal C}(K)=1$ ” is immediate.
A meaningful strengthening of Theorem 3.33 is available. Let

$$\mathfrak g_n=\{B:B\mathbf1=0,\ \beta B=0\}.$$

For a minimal  $K$ , the differential of the orbit map at the identity is

$$D\psi_I(B)=[K,B].$$

This differential is injective. Indeed, if  $[K,B]=0$ , then

$$BK^j\mathbf1=K^jB\mathbf1=0,\qquad j=0,\ldots,n-1.$$

Since the reachability matrix

$$[\mathbf1,K\mathbf1,\ldots,K^{n-1}\mathbf1]$$

has rank  $n$ , it follows that  $B=0$ . Hence the reset-preserving orbit through a minimal interior  $K$  is locally a smooth immersed manifold of dimension

$$\dim\mathfrak g_n=(n-1)^2.$$

Interior positivity ensures that a neighbourhood of this orbit remains in the Markovian cone. This yields a quantitative fibre-dimension theorem, rather than merely existence of a continuum.
The serial result should then be presented separately as an orbit-intersection calculation:

$$\mathcal F_{\mathcal C_{\rm serial}}(K(\theta))
 =\{\text{permutations of the rate multiset }\theta\}.$$

Its novelty must be compared explicitly with the cited acyclic DPH and confluent canonical-form literature.
B2 — Add a feasible version of Theorem E
Let

$$X_N=\sqrt N\{\widehat\sigma_N-\sigma_0\},
\qquad
\widehat\Sigma_N=\widehat\Sigma_{\sigma,N},$$

and retain the paper’s thresholded inverse  $\widehat\Sigma_N^+$ . Define the observable statistic

$$\widehat T_N=X_N^\top\widehat\Sigma_N^+X_N.$$

Conditionally on the record, simulate

$$Z_N^*\sim N(0,\widehat\Sigma_N),\qquad
T_N^*=(\Pi_{H_{z_0}}Z_N^*)^\top
       \widehat\Sigma_N^+
       (\Pi_{H_{z_0}}Z_N^*),$$

and let  $\widehat c_{1-\alpha,N}$  be its conditional  $1-\alpha$  quantile.
The following should be stated and proved:

If  $\lambda_{\min}\{\Sigma_\sigma(z_0)\}>0$ ,
 $\|\widehat\Sigma_N-\Sigma_\sigma(z_0)\|_{\rm op}=o_P(t_N)$ ,
 $t_N\downarrow0$ , and the raw quotient CLT holds, then

$$P_{\sigma_0}\!\left(
E_N\cap
\{\widehat T_N\le\widehat c_{1-\alpha,N}\}
\right)\longrightarrow1-\alpha .$$


Proof:


Weyl’s inequality and full rank imply

$$\widehat\Sigma_N^+\to_P\Sigma_\sigma(z_0)^{-1}.$$



The projection expansion and Slutsky’s theorem give

$$\widehat T_N\Rightarrow
T=(\Pi_{H_{z_0}}Z)^\top
   \Sigma_\sigma(z_0)^{-1}
   (\Pi_{H_{z_0}}Z).$$



The manuscript’s conditional weak-convergence result, together with continuity of the distribution of  $T$  at  $c_{1-\alpha}$ , gives

$$\widehat c_{1-\alpha,N}\to_Pc_{1-\alpha}.$$



The random-threshold lemma yields

$$P(\widehat T_N\le\widehat c_{1-\alpha,N})\to1-\alpha.$$

Intersecting with  $E_N$  changes probability by at most  $P(E_N^c)\to0$ .


For Monte Carlo implementation, take  $B_N\to\infty$  conditional draws and use the DKW allowance

$$\varepsilon_N=
\sqrt{\frac{\log(2/\delta_N)}{2B_N}},
\qquad \delta_N\downarrow0,$$

with the empirical quantile at level  $1-\alpha+\varepsilon_N$ .
This still produces only a test at a preselected  $z_0$ . A claim about an unspecified exchange diagonal would require uniform calibration over  $z$ , or inversion over a predeclared compact interval.
M1 — Add an explicit stable chart
Let

$$x=\Gamma\Delta\tau,\qquad y=\kappa_r\Delta\tau,$$

and restrict initially to

$$\Theta_{\varepsilon,M}
 =\{(x,y):\varepsilon\le x,y\le M\}.$$

Put  $q=1-e^{-x}$  and  $q_{\min}=1-e^{-\varepsilon}$ . From the integral defining  $b$ ,

$$b
=y\int_0^1e^{-yt-x(1-t)}\,dt
\ge \varepsilon e^{-M}.$$

Moreover,

$$1-s\ge q_{\min},\qquad
a\le q(1-s),\qquad
q-a\ge qs\ge q_{\min}e^{-M}.$$

Using

$$\rho=\frac{q(1-s)}{q+b},
\qquad
\rho-a=\frac{b(q-a)}{q+b},$$

one obtains the explicit quotient-denominator bound

$$|\Delta_{\rm inv}|
=\rho(\rho-a)
=\frac{q(1-s)b(q-a)}{(q+b)^2}
\ge
\frac{\varepsilon e^{-2M}(1-e^{-\varepsilon})^3}{4}.$$

Also,

$$r_0=\rho\ge\frac{(1-e^{-\varepsilon})^2}{2}.$$

These inequalities uniformly bound  $D\Phi$  on  $\Theta_{\varepsilon,M}$ .
For root/rate inference, add

$$|p-s|\ge\delta>0.$$

Then the root Jacobian is  $O(\delta^{-1})$ , while
 $p,s\ge e^{-M}$  bounds the logarithmic rate derivative. This gives a genuine uniformly stable separated-root chart. The diagonal must remain a separate nonregular regime.
M2 — State the visible unordered root/rate CLT
Let  $z_-<z_+$  be the roots of

$$z^2-\sigma_1z+\sigma_2=0$$

when  $\sigma_1^2-4\sigma_2>0$ . The sorted roots constitute a canonical visible estimand and require no external physical label.
Their Jacobian is

$$J_{\rm root}=
\begin{pmatrix}
\dfrac{z_-}{z_--z_+}&-\dfrac1{z_--z_+}\\[6pt]
\dfrac{z_+}{z_+-z_-}&-\dfrac1{z_+-z_-}
\end{pmatrix}.$$

Therefore Theorem D should include

$$\sqrt N
\begin{pmatrix}
\widehat z_- -z_-\\
\widehat z_+ -z_+
\end{pmatrix}
\Rightarrow
N\!\left(
0,\,
J_{\rm root}\Sigma_\sigma J_{\rm root}^{\top}
\right).$$

For known  $\Delta\tau$ , define the canonically root-ordered rates

$$\vartheta=
\begin{pmatrix}
-\log z_-/\Delta\tau\\
-\log z_+/\Delta\tau
\end{pmatrix}.$$

Then

$$J_{\rm rate}
=
\begin{pmatrix}
-\dfrac1{\Delta\tau z_-}&0\\
0&-\dfrac1{\Delta\tau z_+}
\end{pmatrix}J_{\rm root},$$

and

$$\sqrt N(\widehat\vartheta-\vartheta)
\Rightarrow
N(0,J_{\rm rate}\Sigma_\sigma J_{\rm rate}^{\top}).$$

Only the assignment of these two numerical entries to the names  $\Gamma$  and  $\kappa_r$  requires side data.
M3 — Make the stopped-batch argument explicit
For

$$X_{\ell,N}
=b_N^{-1}\{B_{\ell,N}B_{\ell,N}^{\top}
-E(B_{\ell,N}B_{\ell,N}^{\top})\},$$

the separated blocks are independent and

$$\sup_{\ell,N}E\|X_{\ell,N}\|_F^2\le C.$$

On

$$cN/b_N\le M_N\le CN/b_N,$$

Kolmogorov’s maximal inequality, applied entrywise, gives

$$P\!\left[
\max_{m\le CN/b_N}
\left\|\sum_{\ell=1}^mX_{\ell,N}\right\|_F
>\eta N/b_N
\right]
\le
\frac{C_d\,b_N}{\eta^2N}.$$

Together with the renewal bound for  $M_N$ , this proves

$$\left\|
\frac1{M_N}\sum_{\ell=1}^{M_N}X_{\ell,N}
\right\|_{\rm op}
=O_P\!\left(\sqrt{\frac{b_N}{N}}\right).$$

For the plug-in term, the exponential moment of  $L_j$  yields, for sufficiently large  $C_0$ ,

$$P\!\left(
\max_{\ell\le CN/b_N}
\sum_{j\in I_{\ell,N}}L_j>C_0b_N
\right)
\le
\frac{CN}{b_N}e^{-c b_N}=o(1).$$

Hence

$$\max_{\ell\le M_N}
\|\widehat B_{\ell,N}-B_{\ell,N}\|
=O_P(b_NN^{-1/2}),$$

and Cauchy–Schwarz gives a covariance cross-term

$$O_P\!\left(\sqrt{\frac{b_N}{N}}\right)$$

and a quadratic term  $O_P(b_N/N)$ . Combining these with the block bias  $O(b_N^{-1})$  proves

$$\|\widehat\Sigma_N-\Sigma\|_{\rm op}
=
O_P\!\left(
b_N^{-1}+\sqrt{\frac{b_N}{N}}
\right).$$

M4 — Derive the physical kernel from an explicit protocol
State the following latched protocol:


Starting in  $R$ , let  $E_\Gamma\sim{\rm Exp}(\Gamma)$ . If  $E_\Gamma>\Delta\tau$ , record zero and end in  $R$ ; otherwise record one and latch the counter in  $D$  until the boundary.


Starting in  $D$ , let  $R_\kappa\sim{\rm Exp}(\kappa_r)$ . If  $R_\kappa>\Delta\tau$ , record zero and end in  $D$ . If recovery occurs at  $r<\Delta\tau$ , start a fresh  $E_\Gamma$ ; record zero and end in  $R$  when  $E_\Gamma>\Delta\tau-r$ , and otherwise record one and latch in  $D$ .


This gives

$$T_0(R,R)=e^{-\Gamma\Delta\tau}=p,\qquad
T_1(R,D)=1-p,$$


$$T_0(D,D)=e^{-\kappa_r\Delta\tau}=s,$$


$$T_0(D,R)=
\int_0^{\Delta\tau}
\kappa_re^{-\kappa_rr}
e^{-\Gamma(\Delta\tau-r)}\,dr=b,$$

and

$$T_1(D,D)=
\int_0^{\Delta\tau}
\kappa_re^{-\kappa_rr}
\{1-e^{-\Gamma(\Delta\tau-r)}\}\,dr=a.$$

The latching clause is essential. Without it, post-click recovery can produce positive  $T_1(\cdot,R)$ , and the deterministic-reset renewal argument no longer applies. The paper should consequently use “latched killed-leakage sampled counter,” not the broader “classical sampled counter.”
M5 — Make the certificate independently reproducible
Submit, with immutable hashes:


certificates/diagonal_branch_certificate.py;


the exact JSON transcript;


Python and decimal-library versions;


dependency lockfile or container digest;


command line and SHA-256 hashes.


A cleaner mathematical alternative is to use the printed enclosure for  $\log2$  and exact rational outward arithmetic to prove directly

$$1.37248
<
\det\Sigma_\sigma(1/2)
<
1.37249.$$

The large positive margin makes a 90-digit transcript unnecessary in the main article. The full transcript can be supplementary.
M6 — Restructure the manuscript
A publication-ready version should contain each result once:


model and exact record law;


quotient inversion and its relation to DMAP2 canonical theory;


higher-state serial versus unrestricted fibres;


retained-record CLT and feasible quotient/root inference;


diagonal projection only if the feasible theorem B2 is added.


Move the following to a supplement:


repeated “detailed forms” of Theorems A–E;


implementation algorithms and withholding rules;


general diagnostic protocols;


long comparator tables;


labelled side-data corollaries;


the 90-digit certificate transcript;


standard regenerative lemmas that can be cited.


Without this reduction and a clarified novelty claim, the manuscript is unlikely to reach acceptance even if all current formulas remain correct.

