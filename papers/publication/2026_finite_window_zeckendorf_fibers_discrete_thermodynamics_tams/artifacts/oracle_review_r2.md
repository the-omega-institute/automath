
============================================================
Referee report
1. Overall assessment
Major revision
The finite identities in Sections 3–6 appear mathematically sound; I independently checked the fiber identities, extremal values, maximizing residues, and quadratic recurrence for small and moderate windows, without finding counterexamples.
However, the principal new result—Theorem 4.5—is not yet proved at publication standard. Its argument requires the uniform bound

$$N_j(k)\le 2\Psi(k)\qquad\text{for every }j\ge0,$$

whereas Weinstein’s published theorem establishes eventual equality only once the layer index exceeds  $2k$ . The manuscript proposes a plausible strengthening but presently supplies only an informal description of the orbit geometry. Since Theorem 4.5, the endpoint  $t=-\sigma _0$ , and Proposition 4.6 all depend on that strengthening, this is a blocker.
The paper should not be rejected outright: the missing argument appears repairable from Weinstein’s explicit formulas. Nevertheless, most other results are elementary transfers or reformulations of known partition results, so acceptance depends heavily on making the freezing theorem completely rigorous and moderating its current “threshold” interpretation.
2. Novelty assessment
Theorems A–C package the numbered results; their effective ratings are A: MEDIUM, B: MEDIUM, and C: HIGH, conditional on repairing the proof.
ResultRatingJustificationTheorem 3.1LOWDirect restatement of the residue definition of the fold.Theorem 3.2LOWStandard finite Fourier inversion and Parseval/character orthogonality.Theorem 3.6MEDIUMThe explicit reversal/complement bijection and affine residue permutation appear to be a genuinely useful pointwise correspondence.Theorem 3.9MEDIUMNew as a fiber formula, although the proof is an elementary truncation of the indexed partition generating function.Theorem 4.1MEDIUMThe two-interval identity is simple but structurally strong and appears to be the paper’s cleanest new finite result.Theorem 4.2LOWThe values and maximizing arguments are translations of the published extremal classification in Kocábová–Masáková–Pelantová, Theorems 4.7 and 5.3. Source paperCorollary 4.3LOWImmediate Fibonacci recurrence applied to Theorem 4.2.Theorem 4.5HIGHA genuine negative-tilt freezing result would be new and significant, but the proof currently depends on an unproved uniform layer estimate.Proposition 4.6MEDIUMThe analytic obstruction is conceptually useful, although it is a short consequence of Theorem 4.5 and analytic perturbation theory.Theorem 5.2LOWReindexing of Theorem 3.9 followed by summation.Theorem 5.3LOWElementary pointwise domination and truncation.Theorem 5.4LOWDirect sandwich transfer of Sanna’s known asymptotic constants. Sanna, Theorem 1.1Corollary 5.7LOWStandard diagonal/constant-term extraction.Theorem 5.9MEDIUMThe direct finite-window derivation is worthwhile, although the governing cubic was already known from the quadratic partition problem.Theorem 5.11LOWStandard solution and root analysis of the recurrence in Theorem 5.9.Proposition 6.1LOWImmediate log-convexity from Cauchy–Schwarz.Corollary 6.2LOWAlternative norm-squeeze proof of Sanna’s existing endpoint theorem.Theorem 6.3LOWStraightforward diagonal consequence of the maximum-norm bounds.
3. Issue table
IDSectionSeverityDescriptionSuggested fixI-01§4.2, uniform layer-count lemmaBLOCKERWeinstein proves eventual stabilization for layers  $j>2k$ ; the manuscript needs a new bound valid for every early layer. The phrases “shifts the relevant indices” and “complementary branch” do not prove uniqueness of layer occupancy.Introduce the largest Zeckendorf index  $L(n)$ , derive exact formulas for  $L([a]g)$ ,  $L([a]\tau g)$ , and  $L(\sigma n)$ , and count each orbit explicitly as described below.I-02§§2.1, 4.2MEDIUMThe assertion that every fiber is nonempty is used to define  $d_m(x)^t$  for  $t<0$ , but surjectivity/nonemptiness is never proved.Add an interval-completeness lemma for subset sums of  $F_1,\ldots,F_m$ , then invoke Theorem 3.6.I-03Abstract, §§1.1, 4.2, 7MEDIUMThe term “freezing threshold” suggests that  $-\sigma _0$  is the exact transition point. The paper proves only  $P(t)=0$  for  $t\le-\sigma _0$ ; it does not prove  $P(t)>0$  immediately above it.Call it a “proved frozen half-line” or “Dirichlet-series freezing bound,” unless positivity for  $t>-\sigma _0$  is established.I-04Proposition 4.6MEDIUMAnalytic perturbation gives local eigenvalue branches, but positivity and simplicity alone do not identify the arbitrarily selected  $r(t)$  with one branch. The proof omits the required continuity argument.First derive continuity of  $r(t)$  from convexity of the pressure, then use a Riesz contour to identify it locally with the unique analytic eigenvalue branch.I-05§§1.1–1.3MEDIUMThe novelty boundary is insufficiently explicit. Several prominently stated results are direct consequences of Kocábová–Masáková–Pelantová or Sanna, while important representation-function literature is omitted.State exactly which ingredients are new, transferred, or alternative proofs; add the references listed below.I-06Theorems 3.9 and 5.2LOWThe quantifier in  $m$  is missing even though  $\pi_m$  was defined only for  $m\ge1$ .Write “For every  $m\ge1$  and every integer  $0\le n<F_{m+2}$ .”I-07Corollary 4.7LOW“Assume Section 4.2” is not a mathematical hypothesis.Replace by “Assume the residual real-pressure hypothesis stated above.”I-08§5.2LOW $t$  is reserved for real tilt but is reused as the integer coefficient index in  $B_m(t)$ .Rename it  $h$ ,  $r$ , or  $\ell$ .I-09Theorem 5.11LOWThe displayed arithmetic value  $p(-2)=-2$  is false.Replace it by  $p(-2)=-10$ ; the sign argument remains valid.I-10Theorem 4.2LOWThe exceptional table jumps from  $m=9$  to  $m=11$ , making it easy to think  $m=10$  was omitted accidentally.State explicitly that  $m=10,12$  are covered by the generic even formula.I-11BibliographyLOWReference [8] gives pages 343–357; the published pagination is 343–359.Correct the page range. Official metadataI-12ThroughoutLOWThe original Zeckendorf theorem is invoked without citation; several hyperlink borders remain visibly red/green; PDF metadata are empty.Add the original citation, suppress link borders, and populate title/author metadata.
4. Missing references
The following are materially relevant:


E. Zeckendorf, “Représentation des nombres naturels par une somme des nombres de Fibonacci ou de nombres de Lucas,” Bull. Soc. Roy. Sci. Liège 41 (1972), 179–182. This should accompany Proposition 2.2.


C. G. Lekkerkerker, “Voorstelling van natuurlijke getallen door een som van getallen van Fibonacci,” Simon Stevin 29 (1952), 190–195. Repository record


J. Berstel, “An exercise on Fibonacci representations,” RAIRO Theor. Inform. Appl. 35 (2001), 491–498. This is important background for normalization and representation automata, even if the current paper withdraws its own transducer. Numdam


M. Bicknell-Johnson and D. C. Fielder, “The number of representations of  $N$  using distinct Fibonacci numbers, counted by recursive formulas,” Fibonacci Quart. 37 (1999), 47–60. Article PDF


P. K. Stockmeyer, “A smooth tight upper bound for the Fibonacci representation function  $R(n)$ ,” Fibonacci Quart. 46/47 (2008/09), 103–106. This is directly relevant to extremal growth. Article PDF


J. Shallit, “Robbins and Ardila meet Berstel,” Inform. Process. Lett. 167 (2021), 106081. This is relevant modern automata-based work on the same partition function. Preprint


N. H. Zhou, “On the representation functions of certain numeration systems,” arXiv:2305.00792. This should be discussed alongside Sanna when positioning moment asymptotics. Preprint


5. Improvements required for acceptance


Supply a complete proof of the uniform early-layer inequality, including all orbit branches and boundary conventions.


Add a proof that every fiber has positive multiplicity before introducing negative powers.


Remove the claim that  $-\sigma _0$  is the exact phase-transition threshold unless positivity above it is proved.


Repair Proposition 4.6 using continuity and Riesz projections.


Rewrite the introduction so that the genuinely new contributions are visibly separated from transferred results and alternative proofs.


Correct the statement, notation, arithmetic, bibliographic, and PDF-production defects listed above.


Consider shortening Sections 3.1 and 5.1: standard Fourier inversion and immediate moment reindexings currently occupy space disproportionate to their novelty.


6. Concrete fixes for all BLOCKER and MEDIUM issues
I-01: rigorous uniform layer-count proof
Let  $f_j=F_{j+1}$  be Weinstein’s convention and define

$$L(n):=\max Z(n),$$

the largest index in the Zeckendorf partition of  $n$ . For  $R(n)>1$ , Weinstein’s Lemma 2.19 gives

$$n\in [f_j-1,f_{j+1}-1)\quad\Longleftrightarrow\quad L(n)=j,$$

because the exceptional endpoints have partition value  $1$ .
For  $k>2$ , every solution lies uniquely in an orbit

$$[a]\tau^\varepsilon\sigma^\delta(g),
\qquad
g\in G(k),\quad a\ge0,\quad \varepsilon,\delta\in\{0,1\}.$$

The authors must derive from Weinstein’s formulas (17)–(19) the explicit index relations

$$L([a]g)=L(g)+2a,
\qquad
L([a]\tau g)=L(\tau g)+2a,$$

together with

$$L(\tau g)\equiv L(g)+1\pmod 2.$$

Consequently, for fixed  $j$ , the two  $N_1$ -branches together contain at most one orbit point with largest index  $j$ : their index progressions have opposite parity, and within each progression  $a$  is uniquely determined.
On  $N_1$ ,  $\sigma$  adds  $1$  to every Zeckendorf index, hence

$$L(\sigma n)=L(n)+1.$$

Thus the  $\sigma$ -branches contribute at most one additional point to layer  $j$ . Freeness of the  $H$ -action prevents collisions between different generators. Therefore each generating orbit contributes at most two points, giving

$$N_j(k)\le 2|G(k)|=2\Psi(k).$$

The cases  $k=1,2$  may then be treated separately as in the manuscript. This is the argument that the current prose gestures toward, but every displayed index identity must actually be proved.
The accompanying Dirichlet-series step should also be written explicitly. For  $s>2$ , put

$$A(s):=\sum_{n\ge2}\frac{\varphi(n)}{n^s}
     =\frac{\zeta(s-1)}{\zeta(s)}-1.$$

The free-monoid decomposition and Tonelli give

$$1+\sum_{k\ge2}\frac{\Psi(k)}{k^s}
   =\sum_{r\ge0}A(s)^r.$$

Hence convergence is equivalent to  $A(s)<1$ , i.e.

$$\frac{\zeta(s-1)}{\zeta(s)}<2.$$

This proves the precise abscissa claim without appealing circularly to Equation (4.2) “in its half-plane of convergence.” Weinstein’s published statement supplies eventual stabilization, not the manuscript’s required uniform inequality. Weinstein, Theorem 5.1 and proof
I-02: prove nonempty fibers
Add the following lemma before negative tilts.

Lemma. Every integer  $0\le r<F_{m+2}$  is a subset sum of  $F_1,\ldots,F_m$ .

Proof by induction. For  $m=1$ , the sums are  $0,1$ . If the claim holds for  $m-1$ , then the subset sums using  $F_1,\ldots,F_m$  contain

$$[0,F_{m+1}-1]
\quad\text{and}\quad
F_m+[0,F_{m+1}-1]
   =[F_m,F_{m+2}-1].$$

These intervals overlap because  $F_m\le F_{m+1}$ , so their union is

$$[0,F_{m+2}-1].$$

Therefore  $\widetilde d_m(r)\ge1$  for every residue. Theorem 3.6 then gives  $d_m(x)\ge1$  for every  $x\in X_m$ , making  $d_m(x)^t$  well-defined for every real  $t$ .
I-03: correct the threshold claim
Replace “freezing threshold” by a statement such as:

Let  $\sigma_D$  be determined by

$$\zeta(\sigma_D-1)/\zeta(\sigma_D)=2.$$

We prove the certified frozen region

$$P(t)=0\qquad(t\le-\sigma_D).$$

We do not determine whether this is the maximal zero-pressure interval.

The terms “freezing point,” “positive-pressure phase,” and “above the freezing threshold” should likewise be made conditional. Establishing that  $-\sigma_D$  is the exact threshold would require a lower bound proving  $P(t)>0$  for every  $t>-\sigma_D$ , which is absent.
I-04: repair Proposition 4.6
For each  $m$ ,

$$p_m(t):=\frac1m\log\sum_x d_m(x)^t$$

is convex by Hölder’s inequality. Under the representation hypothesis,  $p_m(t)\to P(t)=\log r(t)$  for every real  $t$ . Hence  $P$  is finite and convex on  $\mathbb R$ , therefore continuous; consequently  $r(t)=e^{P(t)}$  is continuous.
Fix  $t_0$ . Choose a contour  $\Gamma$  enclosing  $r(t_0)$  and no other point of  $\sigma(L_{t_0})$ . For complex  $z$  near  $t_0$ , define the Riesz projection

$$\Pi(z)=\frac{1}{2\pi i}\int_\Gamma
       (\lambda I-L_z)^{-1}\,d\lambda .$$

It is analytic and has rank one. It therefore determines a unique analytic eigenvalue branch  $\mu(z)$  inside  $\Gamma$ . Continuity of  $r(t)$ , together with the local spectral gap, implies

$$r(t)=\mu(t)$$

for real  $t$  sufficiently close to  $t_0$ . Thus  $r$ , and hence  $\log r$ , is locally real analytic everywhere. The identity theorem then gives the desired contradiction.
Alternatively, add continuity of  $r(t)$  or uniqueness of the distinguished positive eigenvalue directly to the proposition’s hypotheses.
I-05: clarify novelty and prior art
The introduction should explicitly say:


Theorems 3.1–3.2 are standard Fourier reformulations.


Theorem 4.2 is an exact convention-and-interval transfer of published extremal results.


Theorems 5.4 and 6.2 transfer or reprove Sanna’s results.


The substantive new claims are the explicit affine permutation in Theorem 3.6, the interval fiber identity in Theorem 4.1, the uniform early-layer strengthening and freezing theorem in §4.2, and the direct finite-window recurrence in Theorem 5.9.


That separation would make the paper’s contribution both more credible and easier to evaluate.
