Referee report
1. Overall assessment: Reject
The manuscript contains a potentially publishable core—especially the affine fiber/partition correspondence and the negative-temperature freezing argument—but the present version cannot be accepted or repaired by ordinary revision.
Two central defects are decisive:


The printed finite-state normalizer fails its stated contract. A direct run through the published table contradicts Theorem A.4 even for  $m=1$ , and a longer input shows that changing “first” to “last” in the flush convention does not repair normalization.


The arithmetic-window recurrences are asserted rather than certified. The manuscript explicitly says that the supplied local artifact does not reconstruct the enormous histogram matrices, yet Theorem 8.1 and Table 6 treat the unverified identities

$$R_qP_q(\widetilde A_q)\widetilde v_q=0$$

and the associated rank equalities as certificate output. Thus Theorems 8.6, 8.9, 8.15, 8.20 and their corollaries do not presently have a reproducible proof.


These are not local typographical errors. Correcting them requires a different normalizer, reconstruction of the collision kernels, recomputation of all arithmetic data, and new independently executable certificates. The surviving unconditional part would then need substantial repositioning because several headline consequences are transfers or short deductions from existing work.
A substantially shorter paper centered on Theorems B, 4.1, 4.5, and perhaps the independently proved quadratic recurrence could merit reconsideration.

2. Novelty ratings
Novelty is assessed independently of correctness; “claimed” means that the novelty would be significant if a valid proof were supplied.
Main theorems A–H
TheoremRatingJustificationALOWThe extremal values and maximizing arguments are transferred from Kocábová–Masáková–Pelantová through the interval identity; the transfer is useful but not a new extremal classification.BMEDIUMThe explicit affine permutation and Fibonacci-lag difference formula appear to be a genuinely useful finite-window identification.CLOWThis is a short nonnegativity sandwich followed by direct application of Sanna’s existing power-sum theorem.DMEDIUMAlgebraicity of every  $\lambda_q$  via polynomial-size integer kernels would be new, but the supplied normalizer proof is invalid.EMEDIUMThe exact frozen half-line and threshold are potentially high novelty; the LDP half is a standard conditional Gärtner–Ellis consequence of a hypothesis that already assumes the difficult regularity.FLOWStandard exponential Markov inequalities using adjacent moment ratios.GLOWStandard cardinality and mass estimates extracted from Theorem F.HLOWThe diagonal limit follows from (D_m^q\le S_q(m)\le
Numbered and appendix theorems
TheoremRatingJustification3.1LOWRestatement of the residue characterization.3.2LOWStandard character orthogonality/Fourier inversion.3.6MEDIUMExplicit affine conjugacy between two subset-sum spectra.3.9MEDIUMUseful pointwise fiber/partition-difference identity.4.1MEDIUMClean exact interval decomposition with useful consequences.4.2LOWImported extremal theorem plus indexing translation.4.5HIGHA new exact freezing threshold would be significant if the cited level-set bounds are stated and transferred rigorously.4.7LOWDirect conditional application of the full-domain Gärtner–Ellis theorem.5.2LOWImmediate reindexing of Theorem 3.9.5.3LOWElementary nonnegativity sandwich.5.4LOWTransfers Sanna’s already established exponential constants.5.9MEDIUMThe exact cubic recurrence is a concrete and plausibly new finite-window identity.5.11LOWStandard analysis of a simple-root cubic recurrence.6.3MEDIUMFinite-state collision realization is worthwhile, but the current construction is not valid.6.5MEDIUMHistogram compression is a useful general construction, though its stated dimension is computationally enormous.6.11LOWLog-convexity of moment sequences and passage to limits.6.16LOWStandard size-bias/Markov concentration.6.17LOWRoutine moment-to-microcanonical bounds.6.19LOWReformulation of the extremal asymptotic.6.20LOWImmediate norm squeeze for diverging real moments.6.21LOWElementary concentration around the maximum.7.3LOWDirect Rényi-entropy calculation from  $S_q(m)$ .8.1LOWA certificate declaration is not itself a mathematical discovery; moreover, the declared protocol is presently incomplete.8.6MEDIUMExact all-tail recurrences for  $q=9,\ldots,17$  would be useful if independently certified.8.9MEDIUMIntegral principalization of the selected Hankel kernels is a nontrivial computational statement.8.15HIGHFull symmetric Galois groups across nine recurrence polynomials would be substantial computational arithmetic, conditional on valid recurrence certificates.8.20MEDIUMLinear disjointness is interesting but its proof needs an additional group-theoretic lemma.A.4LOWNormalization by finite transducer is classical; the printed instance is incorrect.A.5LOWElementary consequence of a correct padded normalizer.B.15LOWStandard Cayley–Hamilton residual propagation.B.16LOWMerely instantiates the unverified certificate assertions.B.19LOWRestates the consequence of B.15 for Table 5.

3. Issue table
IDSectionSeverityDescriptionSuggested fixB1Appendix A, Lemma A.3 and Theorem A.4BLOCKERThe printed transducer does not implement the stated padded Zeckendorf normalizer. For  $m=1,w=1$ , the run  $000\xrightarrow{1/0}001\xrightarrow{0/0}010\xrightarrow{0/0}100\xrightarrow{0/1}000$  emits  $0001$ . Retaining the first  $m+1=2$  digits gives  $00$ , whereas A.5 asserts  $\Lambda(1)=01$ .Replace the table by a genuinely verified normalization transducer and mechanically verify totality, value preservation, legality, length, and terminal output.B2Appendix A, Theorem A.4BLOCKERChanging “first” to “last” does not suffice. For  $w=10110$ , the table plus three zeros emits  $00011000$ ; the last six digits are  $011000$ , which represents the correct integer  $13$  but contains adjacent ones. Hence the device is value-preserving but not a Zeckendorf normalizer.Use the established Berstel transducer or construct and verify the relation between arbitrary and canonical Fibonacci representations; then rebuild A.11.B3§§6, 8 and Appendix BBLOCKERB1–B2 invalidate the collision automaton,  $A_q$ ,  $\widetilde A_q$ , the claimed Perron representation, and every recurrence polynomial derived from those kernels.Withdraw Theorem D and Section 8 until the complete finite-state construction has been rebuilt and independently checked.B4Theorem 8.1; Tables 6–7; B.16BLOCKERThe exact-kernel certificate is circular/incomplete. Table 6 prints the desired residual and rank equalities, but no verifiable witness is given. Pages 86–87 explicitly state that the local artifact does not rebuild  $\widetilde A_q$ . B.16 then concludes acceptance because the equalities are “records specified in Theorem 8.1.”Supply an executable sparse-kernel or compressed-quotient certificate that reconstructs all objects and checks the claimed identities rather than storing their conclusions.B5Theorem 6.5; Table 7BLOCKERThe stated a priori dimension makes the advertised dense certificate infeasible. With (QM1Theorem 4.5MEDIUMThe proof needs an explicit convention-transfer lemma from Weinstein. The manuscript uses the uniform bound  $N_j(k)\le2\Psi(k)$  for every layer and every  $k\ge2$ , whereas the readily stated published result emphasizes eventual equality for  $k>2$ . The cases  $k=1,2$ , endpoints, and early layers are not documented.State and prove the exact layer-count lemma needed for the inequality, with the translation  $f_j=F_{j+1}$  and separate treatment of  $k=1,2$ .M2Theorem 4.5, final conclusionMEDIUM“No compact, uniformly positive real-tilt transfer operator … can represent these sums” is not a formally defined assertion. Compactness, analytic dependence, the Banach space, and the meaning of “represent” are unstated.Replace it by a precise impossibility proposition with explicit operator hypotheses and cite analytic perturbation theory.M3Theorem 4.7 and abstractMEDIUMThe “full real-tilt LDP” assumes existence, differentiability, analyticity, and  $P''>0$ —essentially the entire unresolved pressure problem. Its prominence makes the manuscript appear to establish an LDP that it does not establish.Rename it “Conditional corollary,” remove it from the headline contribution list, or prove the residual hypothesis.M4Theorem 8.20MEDIUMSquareclass independence alone is invoked to classify  $L_q\cap M_q$ , but the manuscript does not prove that every quadratic subfield of the compositum  $M_q$  is generated by products of the other discriminant fields, nor that a full  $S_n$ -intersection cannot arise through a nonabelian common quotient.Add an induction using Goursat’s lemma, the abelianization  $S_n^{\mathrm{ab}}\cong C_2$ , and the simplicity of  $A_n$ .M5§§1.1–1.2, 6.13MEDIUMThe novelty discussion fails to acknowledge that Sanna already proved  $\lim_{q\to\infty}\lambda_q^{1/q}=\varphi^{1/2}$ . Corollary 6.13 is therefore an alternative proof, not a new endpoint law.Correct the attribution and isolate only the genuinely new diagonal  $q=q(m)$  consequence.M6Appendix A.1 and Theorem 8.1MEDIUMHashes alone do not provide durable availability. No certificate JSON or verifier accompanied the supplied PDF, and the manuscript gives no archival DOI or permanent repository.Deposit source, artifacts, environment lockfile, and machine-readable outputs in a permanent archive; include a small independent verifier.M7Corollary 8.16MEDIUM“Unramified primes for which  $P_q\bmod p$  is irreducible” conflates field unramifiedness with good polynomial reduction. Dedekind factorization is immediate for  $p\nmid\operatorname{Disc}(P_q)$ ; primes dividing the polynomial index require separate exclusion.State the result for  $p\nmid\operatorname{Disc}(P_q)$ , noting that deletion of finitely many primes does not change density.M8Theorem 4.2MEDIUMThe proof relies almost entirely on an indexing translation of two theorems of [12], but that translation is not stated as a precise lemma. This makes the exceptional maximizer list difficult to audit.Give a dictionary between the two Fibonacci conventions and reproduce the exact source formulas before substitution.M9Theorems 6.3–6.5MEDIUM“Dimension polynomial in  $q$ ” is formally true for fixed  $k$  but misleading computationally: the degree is  $k-1$ , with (k=2QL1ThroughoutLOW“Stabilization,” “resonance window,” and “discrete thermodynamics” are used more strongly than the underlying modular subset-sum construction warrants.Define these terms operationally or use neutral terminology.L2§§1, 8 and AppendicesLOWThe same certificate caveat and dependency chain is repeated many times, substantially inflating the paper without adding proof.Replace the repetitions by one formal certificate specification and one dependency diagram.L3NotationLOW $d_m,d_m^\#, \widetilde d_m,R,R^\dagger,S_q,T_q^\dagger$  are introduced in rapid succession;  $q$  alternates between integer and real roles.Add a notation table and reserve  $q$  for integers,  $t$  for real tilts.L4References/typographyLOWThe citation string “[10, 5][4, Thm. 2.3.6]” is malformed; some long tables and formulas are needlessly difficult to audit.Correct citations and move raw certificate digests to supplementary material.

4. Missing or inadequately treated references
The following are important omissions:


J. Berstel, “An Exercise on Fibonacci Representations,” RAIRO 35 (2001), 491–498. This is indispensable because it gives a length-preserving transducer from arbitrary Fibonacci representations to canonical ones—the exact function Appendix A attempts to construct. Official article


J. Shallit, “Robbins and Ardila Meet Berstel,” Information Processing Letters 167 (2021), 106081. This provides a direct automata-theoretic comparator and explicitly uses Berstel’s four-state conversion mechanism. Article page


D. A. Klarner, “Partitions of  $N$  into Distinct Fibonacci Numbers,” Fibonacci Quarterly 6 (1968), 235–243. Foundational work on the level sets and recurrences of the Fibonacci partition function. Paper


L. Carlitz, “Fibonacci Representations,” Fibonacci Quarterly 6 (1968), 193–220. A major early source for exact formulas and should appear in any serious historical account.


M. Bicknell-Johnson and D. C. Fielder, “The Number of Representations of  $N$  Using Distinct Fibonacci Numbers, Counted by Recursive Formulas,” Fibonacci Quarterly 37 (1999), 47–60. Directly relevant to the recurrence claims. Bibliographic source


M. Edson and L. Q. Zamboni, “On Representations of Positive Integers in the Fibonacci Base,” Theoretical Computer Science 326 (2004), 241–260. Important for regularity and structural properties of the same representation-count function. Article


P. K. Stockmeyer, “A Smooth Tight Upper Bound for the Fibonacci Representation Function  $R(n)$ ,” Fibonacci Quarterly 46/47 (2008/09), 103–106. Relevant to extremal bounds and the positioning of Theorem A. Paper


The already cited Sanna paper must also be described accurately: its main result includes both the power-sum growth and

$$\lim_{q\to\infty}\lambda_q^{1/q}=\varphi^{1/2}.$$

Published article
Finally, the use of Frougny [9] is inaccurate: Corollary 4 concerns online addition of normal Fibonacci representations, not correctness of the manuscript’s particular ten-state table on arbitrary binary inputs. Official paper

5. Improvements required to reach acceptance
At minimum, a resubmission would need to:


Replace Appendix A with a correct, independently verified normalization relation or transducer.


Reconstruct Theorems 6.3–6.5 from that corrected object and publish exhaustive small-word tests, including all inputs up to a stated length.


Recompute every arithmetic-window polynomial. None of the current Table 5 rows may be retained merely because they fit short scalar windows.


Replace the symbolic astronomical kernel certificate by a small, executable reachable/observable quotient certificate.


Supply the complete artifact, verifier, deterministic environment, archival DOI, and a verification log.


Add the missing lemma in the freezing proof that precisely transfers Weinstein’s level-count statements, including  $k=1,2$ .


Recast Theorem 4.7 as conditional supporting material unless the residual pressure hypothesis is actually proved.


Correct the novelty narrative: Theorem A is a transfer, Theorem C is a transfer, Corollary 6.13 is already known, and F–H are largely moment inequalities.


Either shorten the paper radically or separate it into:


an unconditional combinatorial/thermodynamic paper; and


a computer-assisted arithmetic paper with a standalone certificate package.





6. Concrete fixes for every BLOCKER and MEDIUM issue
B1–B3: Correct the normalization layer
A sound replacement is available using the Berstel normalization relation.
Let  $\mathcal B$  be a finite transducer accepting pairs  $(u,v)$  such that:

$$\operatorname{val}_F(u)=\operatorname{val}_F(v),\qquad
v\in 0^*(0+10)^*,$$

where the second condition says that  $v$  contains no adjacent ones. For a length- $m$  raw word, feed  $0\omega^{\rm rev}$  so that the canonical output has length  $m+1$ . Prove mechanically:

$$\forall u\in 0\{0,1\}^m\quad
\exists!\,v\in\{0,1\}^{m+1}:
(u,v)\in L(\mathcal B).$$

The proof obligations are finite:


transition completeness;


accepting-path unambiguity;


preservation of Fibonacci value;


output-language inclusion  $v\in0^*(0+10)^*$ ;


exhaustive boundary handling for the lowest two Fibonacci places.


Then define

$$\operatorname{Fold}_m(\omega)
  =\operatorname{rev}\bigl(v_2\cdots v_{m+1}\bigr).$$

For the collision kernel, take the synchronized  $q$ -fold product of  $\mathcal B$ , require identical canonical output symbols, and project away the shared output. Because the transducer is unambiguous, the accepted-path count equals  $S_q(m)$  without the unresolved-suffix argument of A.8–A.11.
At minimum, the verifier must explicitly check the manuscript’s counterexamples:

$$\Lambda(1)=01,\qquad
\Lambda(10110)=100000.$$

B4–B5: Replace the non-executable recurrence certificate
For each  $q$ , construct the actually reachable trimmed sparse kernel

$$A_q^{\rm reach}\in M_{D_q}(\mathbb Z),$$

and publish  $D_q$ , not the formal bound  $\binom{k+q-1}{k-1}$ .
Given

$$P_q(X)=X^{d_q}-\sum_{i=1}^{d_q}c_{q,i}X^{d_q-i},$$

the verifier should compute exactly

$$e_t=u_q^TA_q^{\,t}P_q(A_q)v_q,
\qquad t=2,\ldots,D_q+1,$$

and check  $e_t=0$ . Cayley–Hamilton then gives

$$e_t=0\qquad(t\ge2),$$

hence

$$S_q(m)=\sum_{i=1}^{d_q}c_{q,i}S_q(m-i)
\qquad(m\ge d_q+2).$$

If  $D_q$  is still too large, provide a genuinely compressed realization

$$S_q(m)=a_q^TB_q^mb_q,\qquad B_q\in M_{r_q}(\mathbb Z),$$

together with an exact intertwining proof from the reachable automaton. Merely supplying short Hankel windows cannot replace this proof.
M1: Repair the freezing proof
Introduce a lemma in the manuscript’s notation. If

$$N_j(k)=\#\{n\in[F_j-1,F_{j+1}-1):R(n)=k\},$$

prove explicitly that

$$N_j(1)=1,\qquad N_j(k)\le 2\Psi(k)\quad(k\ge2)$$

for every relevant  $j$ , with eventual equality stated separately.
Then, because the fiber list covers two adjacent layers,

$$S_t(m)
 \le 2+4\sum_{k\ge2}\Psi(k)k^t.$$

For  $t<-\sigma_0$ , convergence follows from

$$1+\sum_{k\ge2}\frac{\Psi(k)}{k^s}
 =\left(2-\frac{\zeta(s-1)}{\zeta(s)}\right)^{-1}.$$

At  $t=-\sigma_0$ , write for any  $\varepsilon>0$ 

$$k^{-\sigma_0}
 \le D_m^\varepsilon k^{-(\sigma_0+\varepsilon)}$$

and conclude

$$0\le\limsup_{m\to\infty}\frac1m\log S_{-\sigma_0}(m)
 \le \frac{\varepsilon}{2}\log\varphi.$$

This makes the endpoint argument complete once the uniform level-count lemma is proved.
M2: Make the operator obstruction precise
Replace the present prose by:

There is no analytic family  $t\mapsto\mathcal L_t$  of bounded operators on a fixed Banach space such that, for every  $t\in\mathbb R$ ,  $\mathcal L_t$  has a positive simple isolated eigenvalue  $r(t)$ , the remainder of the spectrum is uniformly separated locally from  $r(t)$ , and  $P(t)=\log r(t)$ .

Analytic perturbation theory would make  $r(t)$ , hence  $P(t)$ , real analytic. Since  $P$  vanishes on  $(-\infty,-\sigma_0)$  but  $P(0)=\log\varphi$ , this is impossible.
M3: Reposition the conditional LDP
State it as:

Conditional Corollary. If the residual pressure hypothesis holds, then the Gärtner–Ellis theorem gives …

Do not count it as an established principal contribution. The substantive open problem is precisely to prove existence and differentiability of  $P(t)$  on  $(-\sigma_0,\infty)$ .
M4: Complete the linear-disjointness proof
Proceed inductively. Suppose  $M=L_1\cdots L_{r-1}$  already has

$$\operatorname{Gal}(M/\mathbb Q)\cong\prod_{i<r}S_{n_i}.$$

For  $L_r$ , the intersection  $L_r\cap M$  corresponds to a normal subgroup of  $S_{n_r}$ , so it is  $\mathbb Q$ , the discriminant field  $K_r$ , or  $L_r$ .


Every quadratic character of  $\prod_{i<r}S_{n_i}$  is a product of sign characters. Hence every quadratic subfield of  $M$  corresponds to a product of the previous discriminant squareclasses. Independence excludes  $K_r\subset M$ .


Any surjection

$$\prod_{i<r}S_{n_i}\twoheadrightarrow S_{n_r}$$

factors through one coordinate: the coordinate images commute, while  $S_{n_r}$  is centerless and has  $A_{n_r}$  as its unique nonabelian simple composition factor. Thus  $L_r\subset M$  would force  $L_r=L_i$  for some equal degree, contradicting discriminant independence.


Therefore  $L_r\cap M=\mathbb Q$ , completing the induction.
M5: Correct the prior-art claims
State explicitly that Sanna already obtained

$$\lim_{q\to\infty}\frac{P_q}{q}
 =\frac12\log\varphi.$$

Present Corollary 6.13 only as a short finite-window reproof. The genuinely additional statement is the diagonal uniformity

$$\frac{1}{mq(m)}\log S_{q(m)}(m)
 \longrightarrow \frac12\log\varphi,$$

which follows from the elementary maximum-norm squeeze.
M6: Make the computation archival and independently checkable
The permanent archive should contain:


canonical transducer edge list;


reachable sparse kernels or compressed quotient matrices;


polynomial rows  $P_q$ ;


residual and rank witnesses;


finite-field factors and Bézout identities;


Smith matrices;


discriminants and Euler witnesses;


verifier source and dependency lockfile;


expected digest and runtime log.


The manuscript should state exactly which files establish which theorem.
M7: Correct the Chebotarev statement
Use:

$$\mathcal P_q=
\{p:p\nmid\operatorname{Disc}(P_q),\ 
P_q\bmod p\text{ is irreducible}\}.$$

For such primes, the reduction is squarefree and irreducibility is equivalent to Frobenius having cycle type  $(d_q)$ . Hence

$$\delta(\mathcal P_q)=\frac{(d_q-1)!}{d_q!}=\frac1{d_q}.$$

Any additional finitely many field-unramified but polynomial-bad primes do not affect the density.
M8: Make the extremal translation auditable
Insert a lemma giving the exact conversion between the source convention  $G_0=G_1=1$  and the manuscript convention  $F_0=0,F_1=F_2=1$ . It should state the source maximizing intervals and arguments verbatim in converted notation before subtracting the endpoint  $F_{m+2}$ . The exceptional cases  $m=8,11$  should be checked in a displayed table of actual partition arguments, not only residues.
M9: State honest complexity
Report:

$$k=2|Q|(2^{L+2}-1),\qquad
\dim\widetilde A_q=\binom{k+q-1}{k-1}.$$

Then distinguish:


formal asymptotic polynomiality in  $q$  with  $k$  fixed;


the degree  $k-1$ ;


actual reachable-state counts;


time and memory required for each certified  $q$ .


Without this information, “polynomial-size” materially misdescribes the computational construction.
The manuscript’s unconditional combinatorial core is promising, but the finite-state and arithmetic layers require complete reconstruction before the paper can be reconsidered.

