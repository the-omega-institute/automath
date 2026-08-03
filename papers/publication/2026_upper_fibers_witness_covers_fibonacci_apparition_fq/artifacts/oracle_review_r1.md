
============================================================
1. Overall assessment: Major revision
The principal structural results—especially the minimal-generator criterion, witness-cover bijection, and connected-block factorization—appear mathematically correct. I found no counterexample to the theorem chain, and I independently reproduced all values of  $A(n)$  and  $M_n$  for  $2\le n\le30$ , as well as

$$M_{42}=\{52,58,211,1684,12209\}.$$

The manuscript is nevertheless not ready for acceptance. Two matters are blocking:


The novelty boundary is not adequately established. Several advertised theorems are nearly formal consequences of classical strong divisibility, rank-lcm identities, and elementary irredundant-cover combinatorics.


The claimed “sharp minimal-generator growth” is sharp only after separating the uncontrolled arithmetic quantity  $R(n)$ . The actual normal and mean orders remain conditional on hypotheses constructed precisely to make the error term negligible.


For a specialist venue such as The Fibonacci Quarterly, the paper is potentially publishable after substantial reframing and compression. At a broader number-theory journal, the present theorem package would probably be judged insufficiently deep.
2. Novelty ratings
The preview Theorems A–D duplicate the numbered results and are not rated separately.
TheoremRatingJustification2.3LOWThis is the classical primitive-divisor theorem of Carmichael/Bilu–Hanrot–Voutier, with small cases handled separately.3.2 / Preview ALOWThe identity follows immediately from  $q\mid F_m\iff\alpha(q)\mid m$ ; its cardinality form is already contained in the cited  $\alpha$ -contraction formula.3.3LOWThis is the coordinatewise characterization of a minimal lcm representation after prime-power factorization.3.6 / Preview BMEDIUMThe witness-cover language and resulting bijection appear new in this setting, although the proof is essentially Theorem 3.3 translated into irredundant-cover terminology.4.1LOWThe primitive/ladder dichotomy is a direct consequence of the classical prime-power rank formulas.4.2LOWThis is the standard private-coordinate injection for an irredundant cover.4.13MEDIUMThe exhaustive support-three classification and arithmetic slot test appear new, but constitute a finite case classification rather than new Fibonacci arithmetic.5.2LOWPairwise coprimality of disjoint coordinate blocks is immediate from strong divisibility.5.3 / part of Preview DMEDIUMThe connected-component factorization of the complete fiber is a useful new formulation, although it is a generic hypergraph decomposition.5.4 / part of Preview DMEDIUMPassing the component factorization to minimal elements and obtaining the partition sum is a substantive structural consequence.6.1 / Preview CMEDIUMThe coefficient  $(\log2)/4$  in the combinatorial cover entropy appears novel, but the actual order of  $\log\#M_n$  is unresolved because of  $R(n)$ ; the asymptotic equivalents are conditional.
No theorem presently merits a HIGH rating: the deepest arithmetic input remains classical, while the new material is predominantly structural and combinatorial.
3. Issue table
IDSectionSeverityDescriptionSuggested fixB1Introduction; §§3–5BLOCKERThe novelty boundary is unclear. Theorems 3.2, 3.3, 4.1, 4.2 and 5.2 are largely formal consequences of known identities, while 3.6 and 5.3–5.4 are generic strong-divisibility constructions.Formulate and prove an abstract strong-divisibility-sequence theorem, then identify precisely which Fibonacci-specific consequences are new; otherwise downgrade the elementary results to lemmas and narrow the novelty claims.B2Abstract; title; §6BLOCKER“Sharp minimal-generator growth” is not established for  $\#M_n$ . The upper bound retains  $k\log R(n)$ , and (6.8)–(6.9) merely become asymptotics after assuming that term is negligible.Either prove genuine control of  $R(n)$ , or retitle/reframe the result as combinatorial support entropy with an unresolved arithmetic multiplicity. Move (H1)–(H2) to conjectures and the resulting equivalents to conditional corollaries.M1§2.3; Remark 6.2MEDIUMExisting results on the number and structure of primitive prime divisors are not compared with  $R(n)$ , even though this is the paper’s sole unresolved arithmetic interface.State the elementary bound  $R(n)\le1+\omega(F_n)=O(n)$ , discuss Stroiński’s cumulative bound, and explain quantitatively why neither approaches (H1).M2Proposition 2.5MEDIUMThe proof silently replaces  $\nu_p(r)$  by  $\nu_p(u)$  when  $r=z_pu$ ; this requires  $p\nmid z_p$ , which is neither proved nor cited.Insert  $z_p\mid p-(5/p)$  for  $p\ne2,5$ , hence  $\nu_p(z_p)=0$ , before deriving the displayed lifting formula.M3§§2.2, 2.6, 4.7MEDIUM“Primitive atom,” “primitive prime,” and “primitive divisor” are conflated. In the BHV convention, divisors of the discriminant are excluded, whereas the paper treats  $5$  as a primitive prime at rank  $5$ .Reserve “exact-rank prime” or “prime atom” for  $\alpha(p)=d$ , and use “primitive divisor” only after explicitly fixing the conventional definition.M4Corollary 3.8MEDIUM“Subject only to” coverage and irredundance is false for Fibonacci witness types: Theorem 4.1 imposes the additional constraint  $I=J$  or (IM5Lemma 4.11; Theorem 4.13; Appendix AMEDIUMThe uniqueness language is ambiguous after “all coordinate permutations” are applied. Stabilizers of  $\Gamma_1,\Gamma_4,\Gamma_9$ , etc. make the enumeration repeat the same labelled row or product.State uniqueness for the labelled support set  $T(m)$ , uniqueness only up to the  $S_3$ -orbit for  $\Gamma_i$ , and explicitly deduplicate products or choose a canonical orbit representative.M6§7MEDIUMThe PDF asserts that scripts and generated artifacts are supplied, but the submitted review package contains only the PDF. The  $n\le210$  verification is therefore not reproducible from the submission.Attach the scripts, factorization inputs, generated tables, exact output and checksums; specify the Python version and factorization library/algorithm.L1Proposition 7.1(d)LOWThe algorithm tests divisibility only by previously retained elements, while the proof refers to all previous elements of  $B_n$ .Add the short induction showing that every discarded element has a retained minimal divisor.L2§§1–6LOW $\omega$ ,  $A_{\rm pr}$ ,  $\operatorname{Part}(P(n))$ , the logarithm convention, and connectivity for a one-vertex hypergraph are not all explicitly defined.Add a notation paragraph.L3§6LOW“Hardy–Ramanujan maximal-order scale” conflates their normal-order theorem with the separate maximal-order statement for  $\omega(n)$ .Distinguish normal and maximal order and cite a modern standard reference for each.L4Corollary 3.13LOWThe interval is called “canonical,” although it depends on an arbitrary choice of primitive prime  $\pi_n$ .Replace “canonical” by “natural after choosing  $\pi_n$ .”L5ThroughoutLOWThe abstract is excessively long and repeats much of the introduction; Theorem 4.13 is preceded and followed by several near-duplicate explanations.Reduce the abstract to the unconditional results and compress the support-three mechanics into one theorem plus an appendix.L6pp. 12, 14, 34LOWThere is a literal qquad typesetting error; “FQ-facing,” “counterexample battery,” and deepening_delta are internal workflow language rather than publication prose. Hyperlink borders are visually intrusive.Correct the source and replace internal terminology with standard academic language.L7Lemma 4.8; Corollary 5.5LOWHall’s theorem and partition-lattice Möbius inversion are used without standard combinatorial references.Cite a standard source and shorten the ad hoc proof of Hall’s theorem.
4. Missing or insufficiently discussed references


Stroiński is cited, but his explicit cumulative primitive-prime estimate is not discussed. His Theorem 7 gives an upper bound for

$$\pi_\alpha(x)=\#\{p:\alpha(p)\le x\},$$

directly relevant to Remark 6.2. See Stroiński, On Dirichlet Products Evaluated at Fibonacci Numbers.


Marc Renault proves the lcm identity for ranks in the more general  $(a,b)$ -Fibonacci setting. This is important to the novelty assessment of Theorems 2.2, 3.3 and 5.2: Renault, The Period, Rank, and Order of the  $(a,b)$ -Fibonacci Sequence Mod  $m$ .


The modern valuation treatment of Lengyel’s formulas should be cited alongside the 1995 paper: Medina–Rowland,  $p$ -regularity of the  $p$ -adic valuation of the Fibonacci sequence.


The primitive-divisor discussion should include Granville, Primitive prime factors in second-order linear recurrence sequences and Kiss, Primitive Divisors of Lucas Numbers.


For the current arithmetic context around sizes of primitive divisors, cite Hong, On big primitive divisors of Fibonacci numbers. This does not prove (H1), but it helps delimit what modern primitive-divisor results actually control.


The computational discussion should acknowledge the classical factorization literature, notably Brillhart–Montgomery–Silverman, Tables of Fibonacci and Lucas Factorizations, Math. Comp. 50 (1988), 251–260.


5. Specific improvements needed for acceptance


Reorganize the paper around genuinely new endpoints: the witness-cover bijection, support-three classification, minimal connected factorization, and combinatorial entropy bound.


State the structural results first in a general strong-divisibility setting. This would turn their formal nature into a conceptual theorem rather than an unacknowledged limitation.


Reframe Section 6 so that “sharp” always modifies support-type entropy, not the unknown arithmetic growth of  $\#M_n$ .


Add unconditional consequences currently omitted: an almost-everywhere lower bound and a maximal-order lower bound along primorial indices.


Repair Proposition 2.5, Corollary 3.8, the primitive-divisor terminology, and the support-three uniqueness statement.


Supply the complete computational archive.


Remove internal editorial language and reduce the manuscript substantially; approximately 20–25 pages plus a computational appendix would be more appropriate.


6. Concrete fixes for all BLOCKER and MEDIUM issues
B1: Extract the general structural theorem
A suitable replacement for much of §§3 and 5 is the following.

General strong-divisibility fiber theorem.
Let  $(u_n)_{n\ge1}$  be a positive strong divisibility sequence with

$$u_1=1,\qquad \gcd(u_a,u_b)=u_{\gcd(a,b)}.$$

For every  $q$  dividing some term, put

$$\alpha_u(q)=\min\{r\ge1:q\mid u_r\}.$$

Then

$$q\mid u_m\iff \alpha_u(q)\mid m,
\qquad
\alpha_u(\operatorname{lcm}(a,b))
=\operatorname{lcm}(\alpha_u(a),\alpha_u(b)).$$

Consequently, for

$$B_n(u)=\{q\mid u_n:\alpha_u(q)=n\},$$

one has

$$B_n(u)=\operatorname{Div}(u_n)
\setminus\bigcup_{p\mid n}\operatorname{Div}(u_{n/p}).$$

If  $m=\prod_i p_i^{e_i}\mid u_n$ , then  $m$  is minimal in  $B_n(u)$  iff

$$\operatorname{lcm}_i\alpha_u(p_i^{e_i})=n$$

and, for every  $i$ ,

$$\operatorname{lcm}\!\left(
\alpha_u(p_i^{e_i-1}),
\{\alpha_u(p_j^{e_j}):j\ne i\}\right)<n.$$


The duality proof is short: if  $q\mid u_{\alpha(q)}$  and  $q\mid u_m$ , then

$$q\mid\gcd(u_{\alpha(q)},u_m)=u_{\gcd(\alpha(q),m)}.$$

Minimality of  $\alpha(q)$  forces  $\gcd(\alpha(q),m)=\alpha(q)$ .
The witness-cover and connected-component statements can then be proved in this general theorem. The Fibonacci-specific contribution begins only when the prime-power valuation formulas imply the primitive/ladder dichotomy. This separation would make the novelty intellectually transparent.
B2: Correct the growth claims
The unconditional statement should be presented exactly as

$$\frac{\log2}{4}\omega(n)^2-O(1)
\le \log\#M_n
\le
\frac{\log2}{4}\omega(n)^2
+\omega(n)\log R(n)+O(\omega(n)).$$

The sentence following it should say:

The coefficient  $(\log2)/4$  is the exact entropy constant for the support combinatorics. This is not an asymptotic formula for  $\log\#M_n$  unless  $R(n)=\exp(o(\omega(n)))$ .

Then add two genuinely unconditional corollaries.
From Hardy–Ramanujan,

$$\omega(n)=(1+o(1))\log\log n$$

for almost all  $n$ , hence

$$\log\#M_n\ge
\left(\frac{\log2}{4}+o(1)\right)(\log\log n)^2
\quad\text{for almost all }n.$$

For the primorial sequence  $N_y=\prod_{p\le y}p$ ,

$$\omega(N_y)\sim\frac{\log N_y}{\log\log N_y},$$

and therefore

$$\log\#M_{N_y}\ge
\left(\frac{\log2}{4}+o(1)\right)
\frac{(\log N_y)^2}{(\log\log N_y)^2}.$$

These are meaningful unconditional growth theorems. Hypotheses (H1) and (H2) should then be labelled conjectures, and (6.8)–(6.9) conditional corollaries.
M1: Quantify the known baseline for  $R(n)$ 
Every prime atom occurring in  $A_{I,J}(n)$  divides  $F_n$ , while a fixed ladder family contributes at most one atom. Thus

$$R(n)\le 1+\omega(F_n).$$

Since

$$2^{\omega(F_n)}\le\operatorname{rad}(F_n)\le F_n$$

and  $\log F_n=n\log\varphi+O(1)$ ,

$$\log R(n)\le \log n+O(1).$$

This should be stated before (H1). It also demonstrates the strength of the conjecture: for almost all  $n$ , (H1) asks for

$$\log R(n)=o(\log\log n),$$

whereas the elementary bound gives only  $O(\log n)$ .
Stroiński’s cumulative estimate should then be quoted:

$$\limsup_{x\to\infty}
\frac{\log x}{x^2}\,
\#\{p:\alpha(p)\le x\}
\le \frac{3\log\varphi}{2\pi^2}.$$

Explain explicitly that this is also far too weak to imply (H1).
M2: Repair Proposition 2.5
Insert the missing step:
For  $p\ne2,5$ , the classical congruence

$$F_{p-(5/p)}\equiv0\pmod p$$

implies

$$z_p=\alpha(p)\mid p-\left(\frac5p\right).$$

Therefore  $p\nmid z_p$ . Lengyel’s formula gives, whenever  $z_p\mid r$ ,

$$\nu_p(F_r)=\nu_p(F_{z_p})+\nu_p(r).$$

Writing  $r=z_pu$  now yields

$$\nu_p(F_{z_pu})=h_p+\nu_p(u).$$

Hence  $p^e\mid F_{z_pu}$  iff

$$\nu_p(u)\ge e-h_p,$$

and the least admissible  $u$  is

$$u=p^{\max(e-h_p,0)}.$$

This proves

$$\alpha(p^e)=z_pp^{\max(e-h_p,0)}$$

without a hidden assumption.
M3: Separate the primitive notions
Use the following terminology consistently:


Prime atom of rank  $d$ : a prime  $p$  with  $\alpha(p)=d$ .


Ladder atom: an atomic prime power  $p^e$  with  $e>1$ .


Primitive divisor of  $F_d$ : a prime satisfying the explicitly adopted Carmichael/BHV convention.


Then replace “primitive family”  $P_J(n)$  by “exact-rank prime slot” unless every member is primitive under the declared convention. In particular, treat  $p=5$  at  $d=5$  as an exceptional exact-rank prime if the BHV discriminant-excluding definition is adopted.
M4: Correct Corollary 3.8
The admissible pair universe should be reduced to

$$\mathcal P_k=
\{(I,J):\varnothing\ne I\subseteq J\subseteq[k],
\ I=J\text{ or }|I|=1\}.$$

Its cardinality is

$$N'_k=(2^k-1)+k(2^{k-1}-1).$$

A correct statement is:

Every minimal generator with  $\omega(n)=k$  determines a set

$$T(m)\subseteq\mathcal P_k,\qquad |T(m)|\le k,$$

satisfying coverage and private-coordinate irredundance. Consequently the number of possible labelled support types is at most

$$\sum_{r=1}^{k}\binom{N'_k}{r}.$$

The converse need not hold: arithmetic realization additionally requires nonempty atom families and a system of representatives with distinct underlying primes.

This removes the false “subject only to” claim and strengthens the numerical bound.
M5: Correct the support-three uniqueness claim
The precise statement should be:

Each  $m\in M_n$  determines a unique labelled atomic factor set

$$\{(\theta,E_n(\theta),T_n(\theta)):\theta\mid m\}.$$

Its unlabelled support shape is the unique  $S_3$ -orbit  $\Gamma_i$  containing the labelled support set. Enumeration over all coordinate permutations may list the same labelled row or product more than once because of stabilizers; the final result is the set of distinct products.

For the algorithm, either:


insert products into a mathematical set, or


replace each labelled row by the lexicographically least member of its  $S_3$ -orbit.


Do not claim uniqueness of the raw permuted enumeration.
M6: Supply a reproducible computational supplement
The archive should contain:


compute_birth_layer_table.py;


verify_deepening_delta.py;


the exact factorization data used through  $n=210$ ;


generated TeX/TSV tables;


the complete verification log;


Python and dependency versions;


SHA-256 hashes.


The verification should compare the actual sets

$$B_n^{\rm direct}=B_n^{\rm upper\ fiber},
\qquad
M_n^{\rm direct}=M_n^{\rm witness}$$

rather than only their cardinalities. Until that material is part of the submission, Section 7 should not claim reproducibility.
In summary, the manuscript contains a sound and potentially publishable structural core, but acceptance requires a more honest theorem hierarchy: general structural facts first, Fibonacci-specific atom arithmetic second, and the unresolved  $R(n)$  problem clearly separated from the proved combinatorial entropy.
