[dispatch-nyxid] ERROR: rc=1; Submitted task a0544460-a890-4aa7-824f-c03e5869d4b1 to pool 'company-chatgpt-pro'. Waiting for an answer� � dispatched � uploading_pdf � sent � waiting_response {"error":"cli_error","message":"GET /oracle/tasks/a0544460-a890-4aa7-824f-c03e5869d4b1 failed: error sending request for url (https://nyx-api.chrono-ai.fun/api/v1/oracle/tasks/a0544460-a890-4aa7-824f-c03e5869d4b1): client error (SendRequest): connection error: peer closed connection without sending TLS close_notify: https://docs.rs/ru...
[dispatch] ERROR: No response received (status=failed)
[dispatch-nyxid] PDF: main.pdf (332 KB)
[dispatch-nyxid] Submitting task to pool company-chatgpt-pro ...
does not certify priority; the closest ordered-language numeration literature is currently missing.
TheoremRatingJustification2.2LOWImmediate consequences of the definition and finite Zeckendorf uniqueness.2.3LOWRestates the definition of the fibers as modular subset-sum counts.2.4LOWStandard roots-of-unity filtering and Parseval/character orthogonality.2.6MEDIUMThe explicit affine permutation induced by reversal/complementation is a nontrivial map-specific calculation.3.1LOWStandard de Bruijn presentation and resolving-graph argument.3.3HIGHThe exact  $m=3$  Fibonacci block-injectivity threshold and explicit decoder are substantive and apparently original for this fold.3.7MEDIUMExact classification of the sole two-window trajectory fiber is specific and useful, though elementary once the local table is known.3.13LOWSFT closure and finite-memory conjugacy are standard consequences of the block decoder.3.14LOWRepackages Theorems 3.7 and 3.13 rather than adding a new result.4.3MEDIUMGives a concrete two-window inverse for the constant-type family; the Ostrowski interpretation needs correction.4.4HIGHThe all-aperture metallic block-bijection theorem is one of the paper’s genuine main results.4.5MEDIUMThe threshold classification is important but mostly follows from Theorems 3.3, 4.3, and 4.4.4.6LOWPeriodic counts, entropy, and zeta functions follow routinely from conjugacy and the known exceptional fiber.4.8MEDIUMIdentification of this particular labeled overlap graph as the Fischer cover is meaningful, but alphabet-dependent.4.9LOWOmnibus restatement of prior results.5.4HIGHThe full two-chamber classification is the principal claimed advance, conditional on repairing Proposition 5.2, Lemma 5.3, and the  $m=2$  proof.A.3LOWStandard full-support consequence of a strictly positive finite channel.B.1LOWFinite-partition entropy and KL chain rules.C.1LOWA bijection gives deterministic Blackwell equivalence and divergence invariance.C.3LOWStandard pressure/equilibrium-state invariance under topological conjugacy.E.1LOWStandard interval-discrepancy bound followed by deterministic data processing.E.5LOWPullback of observables through an already established finite-block bijection.
2. Issue table
IDSectionSeverityDescriptionSuggested fixB1Abstract, Introduction, §§4–5BLOCKERThe manuscript repeatedly presents the construction as a quadratic-Pisot “normalization,” but the general object is a colexicographic language rank reduced modulo the number of legal words. It is not arithmetic equality in  $\mathbb Z[\beta]$  or standard  $\beta$ -normalization.Reframe it as a newly defined cyclic rank recoding attached to the  $\beta$ -language. Change the title/abstract and explicitly state the distinction from numerical  $\beta$ -value normalization.B2§5.1, Proposition 5.2, pp. 37–38BLOCKERIn the positive-conjugate chamber, the “simultaneous induction” establishing both  $Q_m=aQ_{m-1}-bQ_{m-2}$  and consecutiveness of the rank is only asserted. The bounded sublanguage is not defined, and the induction invariant is absent. Since the fold uses the inverse rank map, this is foundational.Introduce the boundary-bounded sublanguage  $B_m$ , prove two coupled recurrences, and prove simultaneously that the ranks of  $X_m$  and  $B_m$  are initial integer intervals; details below.B3§5.2, Lemma 5.3, equation (5.5), pp. 38–40BLOCKERThe crucial separation bound is not proved. After inserting the recurrence, the text omits the assumed error term and does not bound the nearest integer  $k$ ; “induction from the displayed  $Q_2$  row” is not an argument. Theorem 5.4 depends directly on this inequality.Replace the paragraph with a standalone nearest-multiple lemma, including complete sign cases and explicit ratio bounds. The exact reduced inequalities are given below.B4§5.3, Theorem 5.4, pp. 40–41BLOCKERFor nonextremal bases with  $m^*(\beta)=2$ , the proof establishes two-sided trajectory recovery but not the claimed finite-block injectivity for  $n\ge2$ , equation (5.7), or the stated memory-zero future decoder. A two-sided conjugacy with a past-dependent inverse does not by itself prove boundary-block injectivity.Prove injectivity of  $\Phi_{\beta,2,2}$  explicitly from two output symbols, then cover longer raw blocks by consecutive length-two output blocks. A complete decoder is given below.B5Appendix C.2, Corollary C.2, p. 47BLOCKERThe assertion that  $d_k=D(\mu_{[0,k-1]}\Vert\nu_{[0,k-1]})$  is superadditive for arbitrary stationary  $\mu,\nu$  is false. Hence Fekete’s lemma cannot establish the asserted existence of the relative-entropy-rate limit.State equality of upper and lower rates via limsup/liminf. Assert an actual limit only under an additional condition such as a stationary finite-order Markov reference measure.M1§4.1, Lemma 4.1, pp. 26–27MEDIUMThe model is not “exactly” the standard Ostrowski numeration: standard weights are convergent denominators  $q_k$ , the first digit satisfies  $b_1<a_1$ , whereas the manuscript uses  $Q_j=q_j+q_{j-1}$  and permits  $x_1=A$ .Rename it a boundary-modified constant-type recurrence model using the Ostrowski local constraint, or redefine it using genuine Ostrowski digits and re-prove the threshold.M2§4.3, Theorem 4.8MEDIUM“Intrinsic” and “forced” overstate the Fischer-cover state count. The  $2^{m-1}$  count is canonical for the shift  $Y_m$  in its stabilized output alphabet, but is not invariant under topological conjugacy:  $Y_m$  is conjugate to the binary full shift, whose usual Fischer cover has one state.Add an explicit qualification that the Fischer cover is canonical for the presented labeled shift, not a conjugacy-invariant complexity measure.M3Introduction and §5MEDIUMThe novelty table compares only broad  $\beta$ -expansion and symbolic-dynamics work. It omits the closest framework: ranking regular languages, abstract numeration systems, Bertrand systems, and direct  $\beta$ -shift/numeration correspondences.Add the references listed below and compare the new ingredient specifically with ordered-language ranking and cyclic reduction.M4§5MEDIUMNo complete worked example is supplied from either genuinely nonmetallic chamber. This makes it difficult to verify how Parry rank, the fold,  $\kappa$ , and the extremal classification interact.Add at least four examples: one extremal and one nonextremal base from each sign chamber.M5Data availability, p. 56MEDIUMInternal paths such as artifacts/... are not a persistent or reviewable archive. The phrase “independently certified” is also inappropriate unless the code proves infinitely many parameters symbolically.Deposit code and saved outputs in a versioned archive with DOI, state exact tested parameter ranges, and describe computation as regression testing rather than proof.M6Overall organizationMEDIUMRoughly one quarter of the manuscript consists of standard entropy, Blackwell, pressure, source-law, and discrepancy consequences. Omnibus Theorems 3.14 and 4.9 duplicate earlier statements. This obscures the genuine theorem package.Retain the threshold proofs and Fischer result in the main text; move Appendices A–F and routine corollaries to supplementary material, except any application essential to the target journal.L1§3.1LOW $Y_m^+$  is used in Corollaries 3.11–3.12 without a formal definition.Define it as the image of the one-sided full shift under the one-sided sliding fold.L2§§5.1–5.2LOWThe symbol  $c$  denotes  $a-b-1$  and is then reused locally for  $a-b$ .Use distinct symbols, e.g.  $c_0=a-b-1$  and  $C=a-b$ .L3Definition 5.1LOWThe recurrences (5.1)–(5.2) appear inside the definition before Proposition 5.2 proves them.Define (Q_m=L4§5.1LOW“Colexicographic order” and the finite-word interpretation of comparison with  $c^\infty$  are not explicitly defined.Give the reversal convention and lexicographic boundary rule before Proposition 5.2.
3. Concrete mathematical repairs
B1: Correct the mathematical interpretation
For the positive-conjugate example

$$\beta^2-3\beta+1=0,\qquad d=\lfloor\beta\rfloor=2,\qquad
(Q_0,Q_1,Q_2)=(1,3,8),$$

the manuscript’s rank gives

$$\operatorname{Rank}_{\beta,2}(2,2)=2+2Q_1=8\equiv0\pmod{Q_2},$$

so  $\operatorname{Fold}_{\beta,2}(2,2)=(0,0)$ . No result establishes a corresponding congruence

$$2+2\beta\equiv0$$

in a natural quotient of  $\mathbb Z[\beta]$ . The operation is therefore a cyclic congruence of language ranks.
A defensible title would be:

“Overlap-injectivity thresholds for cyclic ranks of quadratic Pisot  $\beta$ -languages.”

The abstract should say that the paper defines a new recoding; it should not imply classification of established Pisot normalization transducers.
B2: Complete Proposition 5.2 by coupled induction
In the positive chamber put

$$d=a-1,\qquad c=a-b-1.$$

Define

$$B_m=\left\{x\in X_m^{(\beta)}:
(x_m,\ldots,x_1)\le_{\rm lex}c^m\right\},
\qquad R_m=|B_m|.$$

Prove simultaneously:

$$\operatorname{Rank}(X_m)=\{0,\ldots,Q_m-1\},
\qquad
\operatorname{Rank}(B_m)=\{0,\ldots,R_m-1\}.$$

The high digit decomposition gives

$$Q_m=dQ_{m-1}+R_{m-1},
\qquad
R_m=cQ_{m-1}+R_{m-1}.$$

Since

$$R_{m-1}=Q_{m-1}-(d-c)Q_{m-2}
       =Q_{m-1}-bQ_{m-2},$$

one obtains

$$Q_m=(d+1)Q_{m-1}-bQ_{m-2}
   =aQ_{m-1}-bQ_{m-2}.$$

For the rank induction, digits  $0,\ldots,d-1$  produce consecutive intervals

$$[hQ_{m-1},(h+1)Q_{m-1}-1],$$

while high digit  $d$  contributes

$$[dQ_{m-1},dQ_{m-1}+R_{m-1}-1].$$

The analogous decomposition with high digits  $0,\ldots,c$  proves the  $B_m$  invariant. This supplies the missing bijectivity, count recurrence, and order preservation.
B3: Replace the unsupported separation paragraph
Let

$$R_r=\frac{Q_{r-1}}{Q_{r-2}}.$$

First establish from the recurrence:

$$a+\frac{b}{a+1}\le R_r<a+\frac ba
\quad(s=+1),$$

and

$$a-\frac{b}{a-1}<R_r\le a-\frac ba
\quad(s=-1),$$

for the relevant indices.
If  $k$  is a nearest integer to  $beQ_{r-1}/Q_r$ , show explicitly that  $0\le k\le b$ . With

$$h=be-ak,$$

division by  $Q_{r-2}$  reduces the desired estimate exactly to

$$|hR_r-kb|\ge1 \quad(s=+1),$$

or

$$|hR_r+kb|\ge1 \quad(s=-1),$$

for

$$1\le e\le d,\qquad 0\le k\le b.$$

The proof must then split according to the sign of  $h$ ; the noncancelling signs are immediate, while the cancelling signs require the ratio bounds and the integral relation  $h=be-ak$ . These inequalities—not the current informal “division”—are the actual finite arithmetic lemma needed to infer

$$\operatorname{dist}(beQ_{r-1},Q_r\mathbb Z)\ge Q_{r-2}.$$

If the authors cannot prove these two reduced inequalities uniformly, Theorem 5.4 must be restricted to the parameter range actually verified.
B4: Supply the missing  $m=2$  block decoder
Let  $d>\kappa$ , and write

$$y_i=(p_i,q_i)
 =\operatorname{Fold}_{\beta,2}(a_i,a_{i+1}).$$

From  $y_0,y_1$ , recover  $a_1$  by

$$a_1=
\begin{cases}
q_0,&q_0>0,\\
0,&q_0=0,\ p_1=0,\\
d,&q_0=0,\ p_1\in\{d-\kappa,d\}.
\end{cases}$$

Then recover  $a_0$ :

$$a_0=
\begin{cases}
p_0,&q_0>0,\\
p_0,&q_0=0,\ a_1=0,\\
p_0+\kappa,&q_0=0,\ a_1=d.
\end{cases}$$

Finally recover  $a_2$ :

$$a_2=
\begin{cases}
q_1,&q_1>0,\\
0,&q_1=0,\ p_1=a_1,\\
d,&q_1=0,\ p_1=a_1-\kappa.
\end{cases}$$

The last two alternatives are disjoint because  $\kappa>0$ . Thus

$$\Phi_{\beta,2,2}:A_\beta^3\longrightarrow
\bigl(X_2^{(\beta)}\bigr)^2$$

is injective. Consecutive two-output blocks then cover every raw block, proving injectivity for all  $n\ge2$  and

$$|L_n(Y_{\beta,2})|=(d+1)^{n+1}.$$

B5: Correct Corollary C.2
The claimed superadditivity already fails for simple stationary Markov laws. Let  $P$  be i.i.d. with marginal  $(3/4,1/4)$ , and let  $Q$  be the stationary Markov chain with

$$T_Q=
\begin{pmatrix}
1/2&1/2\\
1/4&3/4
\end{pmatrix},
\qquad \pi_Q=(1/3,2/3).$$

Then

$$D(P_1\Vert Q_1)\approx0.362990,
\qquad
D(P_2\Vert Q_2)\approx0.598426
 <2D(P_1\Vert Q_1).$$

The universally valid conclusion from the manuscript’s exact block identity is instead

$$\limsup_{N\to\infty}\frac1N
D(\eta_{[0,N-1]}\Vert\xi_{[0,N-1]})
=
\limsup_{k\to\infty}\frac{d_k}{k},$$

and the same equality for  $\liminf$ . This follows directly from

$$D(\eta_{[0,N-1]}\Vert\xi_{[0,N-1]})=d_{N+m-1}$$

and  $(N+m-1)/N\to1$ .
If an actual limit is desired, assume that the reference law  $\nu$  is a stationary finite-order Markov law with stationary transitions. Gray explicitly treats the general rate using a limsup and gives the Markov-reference condition under which the limit exists: R. M. Gray, Entropy and Information Theory.
Medium-issue repairs


M1: Replace “Constant-type Ostrowski origin” with “Boundary-modified constant-type recurrence model.” Standard Ostrowski digits satisfy  $b_1<a_1$  and use  $q_k$ , as stated explicitly by Hieronymi–Terry.


M2: Add: “The  $2^{m-1}$ -state conclusion is relative to the stabilized output alphabet  $X_m$ ; Fischer-cover state counts are not invariants of arbitrary topological conjugacy.”


M4: Include the worked cases

$$x^2-2x-2,\quad x^2-3x-2,\quad x^2-3x+1,\quad x^2-4x+2.$$

These respectively exhibit negative extremal, negative nonextremal, positive extremal, and positive nonextremal behavior.


M5: Archive code with a DOI and report whether tests cover, for example,
 $1\le a\le A_{\max}$ ,  $1\le b\le a$ , and  $m,n\le M_{\max}$ . Finite testing must not be described as an independent certificate of an infinite theorem.


M6: Remove Theorems 3.14 and 4.9 as theorem-level repetitions. Move Appendices A, B, C, E, and F to supplementary material unless required by the chosen venue.


4. Important missing references
The following are substantially closer to the manuscript’s actual construction than several references currently used in the novelty table:


A. Rényi, “Representations for real numbers and their ergodic properties,” Acta Math. Acad. Sci. Hungar. 8 (1957), 477–493. DOI


S. Ito and Y. Takahashi, “Markov subshifts and realization of  $\beta$ -expansions,” J. Math. Soc. Japan 26 (1974), 33–55. Article


A. Bertrand-Mathis, “Développement en base  $\theta$ , … langages codés et  $\theta$ -shift,” Bull. Soc. Math. France 114 (1986), 271–323. Article


F. Blanchard, “ $\beta$ -expansions and symbolic dynamics,” Theoret. Comput. Sci. 65 (1989), 131–141. DOI


C. Frougny and B. Solomyak, “Finite  $\beta$ -expansions,” Ergodic Theory Dynam. Systems 12 (1992), 713–723. Article


D. Berend and C. Frougny, “Computability by finite automata and Pisot bases,” Math. Systems Theory 27 (1994), 275–282. DOI


N. Loraud, “ $\beta$ -shift, systèmes de numération et automates,” J. Théorie des Nombres de Bordeaux 7 (1995), 473–498. Article


V. Bruyère and G. Hansel, “Bertrand numeration systems and recognizability,” Theoret. Comput. Sci. 181 (1997), 17–43. DOI


P. B. A. Lecomte and M. Rigo, “Numeration systems on a regular language,” Theory Comput. Systems 34 (2001), 27–44. This is especially important because it treats numeration by ordering a regular language. Article


P. Hieronymi and A. Terry Jr., “Ostrowski numeration systems, addition, and finite automata,” Notre Dame J. Formal Logic 59 (2018), 215–232. Article


5. Acceptance conditions
Acceptance would require all of the following:


A complete proof of Proposition 5.2 in both chambers.


A valid uniform proof of the separation estimate (5.5).


The missing  $m=2$  finite-block proof for Theorem 5.4.


Correction of Corollary C.2 to limsup/liminf, or addition of sufficient Markov hypotheses.


Explicit reframing of the construction as a cyclic language-rank recoding, not standard  $\beta$ -normalization.


A genuine comparison with abstract/regular-language numeration and classical  $\beta$ -shift literature.


Worked nonmetallic examples and a persistent computational archive.


Substantial compression of standard auxiliary material.


If these points are addressed, the paper could become a strong specialized contribution in symbolic dynamics and numeration. Algebraic patching alone would not suffice: the construction’s naturality and relation to existing ordered-language numeration must also be made convincing.

