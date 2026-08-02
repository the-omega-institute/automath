
============================================================
1. Overall assessment
Major revision
The central mathematical correction appears valid under the manuscript’s strict twisted-gap hypothesis. In particular, I found no error in the Adams–Möbius inversion (13)–(15), the corrected constant (33), or the  $S_3$  contradiction (43)–(48).
Acceptance is nevertheless premature because the manuscript presents itself as a formal correction of Mohamed–Noorani while leaving two essential points unresolved:


The 1999 theorem, as printed, assumes only mixing of the base. That is insufficient even for the exponent  $|C|/|G|$ ; the strict twisted gap repairs a second, independent defect that must be acknowledged.


The manuscript does not formally translate the original two-sided, left-multiplication cocycle convention into its one-sided edge-label convention.


The paper is potentially publishable as a focused correction note after these issues and the reproducibility deficiencies are resolved.
2. Novelty ratings
Statements labelled “Theorem”
ResultRatingJustificationTheorem 2.2MEDIUMThe fixed-label determinant formula is useful and apparently new in this setting, but the underlying Adams/Möbius–Euler inversion belongs to standard necklace/Witt formalism.Theorem 3.2MEDIUMThis is the principal new result: a corrected explicit constant. Its significance is real but narrow, and the derivation is essentially finite-dimensional Fourier and Möbius bookkeeping.Theorem 3.3MEDIUMIt identifies a genuine error in a published formula, but is largely a formal consequence of distinguishing  $\chi(g_\gamma)$  from  $\chi(g_\gamma^r)$ .Theorem 4.3MEDIUMThe exact  $S_3$  witness decisively proves that the two constants differ; the construction is valuable but elementary once found.Theorem 5.1LOWThe determinant/trace/periodic-data equivalence is established background, consistent with Boyle–Schmieding and gain-graph cospectrality theory.
Supporting results: Lemmas 2.1, 3.1, 4.1 and Propositions 2.3, 2.4, 5.3, 5.5, Corollary 5.6, Proposition 6.1 are LOW novelty; Lemmas 2.5 and 4.2 are MEDIUM as paper-specific technical ingredients. Boyle–Schmieding explicitly establish completeness of conjugacy-class periodic data on periodic points, while Cavaleri–Donno establish the representation-theoretic  $G$ -cospectrality and simultaneous-conjugacy framework cited in Section 5. Boyle–Schmieding, Cavaleri–Donno.
3. Issue table
IDSectionSeverityDescriptionSuggested fixB11.1, 3.3BLOCKERThe correction is incomplete as a correction of the 1999 theorem. The original printed theorem assumes only a mixing base, which does not imply uniform Frobenius density or the strict twisted gap. Thus  $L_\rho\mapsto F_\rho$  is not the only necessary repair.State explicitly that the 1999 theorem also requires a transitivity/aperiodicity or equivalent strict-gap hypothesis. Add the trivial-cocycle counterexample below and restate Theorem 3.3 accordingly.B22.1, 3.3BLOCKERNo precise bridge is given between the original two-sided cocycle  $\widetilde\sigma(x,g)=(\sigma x,\alpha(x)g)$ , whose holonomy is reverse-ordered, and the present chronological one-sided edge product.Add a recoding/convention lemma showing how periodic orbits, inverse classes, characters, and determinant blocks correspond.M12.1–3.1MEDIUMSeveral convergence and trace estimates use  $\operatorname{rad}(A_\rho)\le\lambda$ , but this domination is never proved. It is needed before Lemmas 2.1 and 2.5 and in (30).Insert the Perron-weighted block-norm proof given below and derive an explicit trace bound.M23.3, ConclusionMEDIUMThe correction’s propagation to the homogeneous-extension theorem in the same 1999 paper is omitted. Later work citing that theorem is also not discussed.State the corrected union-of-classes constant and explain whether later class-Mertens results use the erroneous explicit constant.M34.2, 6.2MEDIUMThe exact window (46) is delegated to a script that is not publicly accessible; Section 6 states that a future DOI/URL remains to be assigned.Make (46) self-contained using explicit rational bounds, or delete the narrow window and retain only  $F_\varepsilon(1/2)<0$ . Deposit all code before publication.M41.1, 2.2MEDIUMThe novelty discussion does not acknowledge that Möbius inversion between primitive cycles and Euler/ghost coordinates is standard necklace/Witt calculus.Cite the relevant literature and state that novelty lies in identifying the correct fixed-label coordinate and applying the transform to the finite determinant family.M55.2MEDIUMProposition 5.3 imports an undirected gain-graph argument into a directed multigraph without defining the gain of a fundamental cycle when tree edges are traversed backward.Extend each marked directed edge formally by an inverse orientation with gain  $\tau(e)^{-1}$ , then define the fundamental-cycle gains in this doubled graph.M66.1MEDIUMProposition 6.1 describes a possible exact computation but not a verifiable certificate format: compatible embeddings, conjugate-root pairing, and machine-readable sign data remain unspecified.Fix an embedding  $K\hookrightarrow\mathbb R$ , compatible extensions to the splitting field, and provide isolating data for every  $\lambda^2-\alpha\bar\alpha$ .M7ReferencesMEDIUMImportant dynamical-zeta, necklace/Witt, and post-1999 related work is absent, weakening both novelty and impact claims.Add and discuss the references listed below.L12.3LOWThe definition of  $\eta$  is undefined when  $G$  is trivial.Declare  $\max\varnothing=0$ , or treat the trivial group separately.L22.4LOWThe general peripheral-boundary construction is largely unused in the strict-gap theorem and introduces  $B_{k,\pi}^{\rm ren}$ -type terminology without a complete independent definition.Move it to an appendix or restrict the section to the endpoint actually used.L34.1LOWThe displayed real standard representation is not manifestly unitary in the displayed basis.Say that it is a non-orthonormal real model similar to a unitary realization, or provide the invariant Gram matrix.L45LOWRoughly one quarter of the paper is devoted to explicitly non-novel inverse material.Compress Theorem 5.1 and Proposition 5.3 to a short background section or appendix.L51.2, 6.2LOWPhrases such as “earlier version,” “referee-response edits,” and “as requested” are revision-history language, not archival mathematical prose.Remove all referee-process language.L66.2, final pageLOWThe repository is unidentified publicly, and the author affiliation “CHRONOAI” is incomplete.Supply permanent repository/DOI, institutional affiliation, and correspondence information.
4. Missing references
The following are important:


N. Metropolis and G.-C. Rota, “Witt vectors and the algebra of necklaces,” Adv. Math. 50 (1983), 95–125. This is necessary to calibrate the novelty of the Möbius/Euler transform. Publisher record.


R. Bowen and O. E. Lanford III, “Zeta functions of restrictions of the shift transformation,” Proc. Sympos. Pure Math. 14 (1970), 43–49/50. This is foundational for the determinant formula for shifts of finite type. Paper.


W. Parry and M. Pollicott, Zeta Functions and the Periodic Orbit Structure of Hyperbolic Dynamics, Astérisque 187–188 (1990). This should be cited for the periodic-orbit/zeta framework. NUMDAM edition.


W. Parry, “An analogue of the prime number theorem for closed orbits of shifts of finite type and their suspensions,” Israel J. Math. 45 (1983), 41–52.


M. S. M. Noorani, “Teorem Chebotarev Untuk Perluasan Kumpulan Terhingga Bagi Anjakan Terhingga,” Sains Malaysiana 24(4) (1995), 91–103. The 1999 article itself cites this for the Artin  $L$ -function and its analytic properties; it is therefore directly relevant to any formal correction. The definition and erroneous transition can be checked in the official 1999 paper.


A. Nordin and M. S. M. Noorani, “A short note on the orbit growth of sofic shifts,” arXiv:2202.03075. It explicitly invokes the 1999 Frobenius-class result in its finite-group extension discussion, so the present manuscript must state whether its constants are affected. Preprint.


If the graph-covering/Artin- $L$  context is retained: H. M. Stark and A. A. Terras, “Zeta functions of finite graphs and coverings,” Adv. Math. 121 (1996), 124–165. Publisher record.


5. Improvements required for acceptance
The paper should:


Recast itself as a concise correction note, not as a broad inverse-rigidity paper.


Correct both defects in the 1999 theorem: the fixed-label/periodic-label substitution and the missing extension-level mixing/gap hypothesis.


Add a formal recoding lemma connecting its conventions to those of the criticized paper.


Supply the missing spectral domination argument.


Make the  $S_3$  certificate self-contained and publicly reproducible.


State the corrected homogeneous-extension consequence.


Recalibrate novelty against necklace/Witt and dynamical-zeta literature.


Compress Section 5 and remove all manuscript-history language.


6. Concrete fixes for BLOCKER and MEDIUM issues
B1 — Correct the hypothesis as well as the constant
Add a counterexample immediately after Theorem 3.3:

Let the base be the full two-shift, represented by the one-vertex matrix  $A=[2]$ , and let  $G=C_2=\{e,s\}$ . Label every edge by  $e$ . Then the base is mixing and  $\lambda=2$ , but  $p_{n,\{s\}}=0$  for every  $n$ . Hence

$$P_{\{s\}}(N)=1,$$

whereas the asserted exponent  $|\{s\}|/|G|=1/2$  would force decay proportional to  $N^{-1/2}$ . In the sign representation,

$$A_\varepsilon=A,\qquad \operatorname{rad}(A_\varepsilon)=2=\lambda,$$

so the strict twisted gap fails.

The corrected historical statement should therefore read:

If the base matrix is primitive and the nontrivial twisted blocks satisfy

$$\max_{\rho\ne1}\operatorname{rad}(A_\rho)<\lambda,$$

then the Frobenius-class product has exponent  $|C|/|G|$  and constant (33). Under base mixing alone, neither that exponent nor the Artin-coordinate expression is valid in general.

The official 1999 article defines the powered-label Artin function but states its main theorem under mixing of the base; therefore this is an independent correction, not merely an expositional qualification. Original article.
B2 — Add the convention/recoding lemma
A suitable lemma is:

Let  $(\bar X_A,\sigma)$  be the two-sided edge shift and  $X_A^+$  its one-sided version. Primitive periodic orbits in both systems correspond to cyclic edge words, preserving least period. For the left cocycle

$$\widetilde\sigma(x,g)=(\sigma x,\alpha(x)g),$$

the period- $n$  holonomy is

$$h_\gamma=\alpha(e_{n-1})\cdots\alpha(e_0).$$

Set  $\tau(e)=\alpha(e)^{-1}$ . Then the chronological edge product satisfies

$$g_\gamma=\tau(e_0)\cdots\tau(e_{n-1})=h_\gamma^{-1}.$$

Consequently

$$p^{\rm MN}_{n,C}=p^{\rm edge}_{n,C^{-1}}.$$

Since  $\chi_\rho(g^{-1})=\overline{\chi_\rho(g)}$ , the corrected Fourier expression is transported by

$$C\longmapsto C^{-1},\qquad \rho\longmapsto\bar\rho,$$

and yields the same real class-product constant.

Also state that every logarithm of the original Artin  $L$ -function means the branch obtained by continuation from  $z=0$  along  $0\le z\le\lambda^{-1}$ .
M1 — Insert the missing spectral domination lemma
Let  $v>0$  satisfy  $Av=\lambda v$ . For a block vector  $x=(x_i)$ , define

$$\|x\|_v=\max_i\frac{\|x_i\|}{v_i}.$$

Because  $\rho(\tau(e))$  is unitary,

$$\begin{aligned}
\|(A_\rho x)_i\|
&\le \sum_j\sum_{e:i\to j}\|\rho(\tau(e))x_j\|\\
&\le \sum_j A_{ij}v_j\|x\|_v
=(Av)_i\|x\|_v
=\lambda v_i\|x\|_v.
\end{aligned}$$

Hence

$$\|A_\rho\|_v\le\lambda,\qquad
\operatorname{rad}(A_\rho)\le\lambda.$$

If  $D_\rho=|V|\dim\rho$ , it follows that

$$|\operatorname{Tr}(A_\rho^n)|\le D_\rho\lambda^n.$$

This also makes the estimate following (30) explicit. With

$$a_*=\max_{\rho,\pi,m}|a_{\rho,\pi}^{(m)}|,
\qquad D_*=\max_\pi |V|\dim\pi,$$

one obtains

$$|c_n(\chi_\rho)|
\le
\frac{D_\rho\eta^n}{n}
+\frac{a_*|\operatorname{Irr}(G)|D_*}{n}
  \sum_{\substack{m\mid n\\m\ge2}}\lambda^{n/m}
\le
\frac{D_\rho\eta^n+
a_*|\operatorname{Irr}(G)|D_*d(n)\lambda^{n/2}}{n}.$$

This proves the required absolute convergence and exponential tail without an implicit spectral assertion.
M2 — State the corrected homogeneous-extension constant
Let  $\mathcal C_\ell$  be the set of conjugacy classes whose cyclic subgroup action produces the partition  $\ell$ . Then

$$P_\ell(N)=\prod_{C\in\mathcal C_\ell}P_C(N)
=K_\ell N^{-\delta_\ell}\bigl(1+O(N^{-1})\bigr),$$

where

$$\delta_\ell=\frac1{|G|}
\sum_{C\in\mathcal C_\ell}|C|$$

and

$$\boxed{
\begin{aligned}
\log K_\ell
={}&-\delta_\ell\bigl(\gamma+\log C(A)\bigr)\\
&-\frac1{|G|}
\sum_{\rho\ne1}
\left(
\sum_{C\in\mathcal C_\ell}
|C|\,\overline{\chi_\rho(C)}
\right)
F_{\chi_\rho}(\lambda^{-1}).
\end{aligned}}$$

This is the exact downstream replacement for the Artin- $L$  coordinates in the homogeneous-extension theorem.
M3 — Make the interval (46) self-contained
Write

$$x_j=2^{1-2^{j+1}},\qquad
q_j=(1-x_j)^{-1},\qquad
u_j=\frac{q_j-1}{q_j+1}=\frac{x_j}{2-x_j}.$$

For  $j=0,1,2,3$ , define the rational numbers

$$L_j=2\sum_{k=0}^{3}\frac{u_j^{2k+1}}{2k+1},
\qquad
U_j=L_j+\frac{2u_j^9}{9(1-u_j^2)}.$$

Then

$$L_j<\log q_j<U_j.$$

Moreover,

$$0<
\frac12\sum_{j\ge4}2^{-j}\log q_j
<
\frac1{2^{35}-16}.$$

The following are exact rational comparisons:

$$\frac{380}{1000}
<
\frac12\sum_{j=0}^{3}2^{-j}L_j,$$

and

$$\frac12\sum_{j=0}^{3}2^{-j}U_j
+\frac1{2^{35}-16}
<
\frac{381}{1000}.$$

Therefore

$$\frac{380}{1000}<-F_\varepsilon(1/2)<\frac{381}{1000},$$

which proves (46) without relying on an unavailable script.
M4 — Recalibrate the novelty claim
Replace “we prove an Adams–Möbius determinant formula” by language such as:

Primitive/Euler coordinates and periodic ghost coordinates are related by the classical necklace/Witt Möbius transform. The new point here is that the Frobenius-class product selects the fixed primitive label, so the relevant transform must be applied before the Adams power operation. This produces the determinant expression (15) and prevents the substitution  $F_{\chi_\rho}=L_{\chi_\rho}$ .

This accurately distinguishes the paper’s contribution from standard formalism.
M5 — Repair Proposition 5.3 for directed graphs
Before the proposition, define the formal reversal  $\bar e$  of every directed marked edge and set

$$\tau(\bar e)=\tau(e)^{-1}.$$

A fundamental cycle may then traverse chosen tree edges in either direction, and its gain is the ordered product of  $\tau(e)$  or  $\tau(e)^{-1}$  according to the traversal. With this convention, tree normalization and simultaneous conjugation give (54) rigorously.
M6 — Make Proposition 6.1 an actual certificate specification
Require the deposited certificate to contain:


a squarefree polynomial  $f_\lambda\in\mathbb Z[t]$  and rational isolating interval selecting  $\lambda$ ;


a fixed embedding  $K=\mathbb Q(\lambda)\hookrightarrow\mathbb R$ ;


a splitting field  $L/K$  with explicit compatible embedding  $L\hookrightarrow\mathbb C$ ;


isolating rectangles for each root  $\alpha_j$  of  $q$ , paired with the rectangle for  $\bar\alpha_j$ ;


for

$$\beta_j=\lambda^2-\alpha_j\bar\alpha_j\in L\cap\mathbb R,$$

a defining polynomial and rational isolating interval contained in  $(0,\infty)$ ;


multiplicity data showing that exactly one trivial Perron root was removed.


Without these data, Section 6 should be described as an algorithmic criterion, not as a deposited exact certificate.
M7 — Literature repair
Add a dedicated paragraph distinguishing:


standard SFT determinant and periodic-orbit theory;


standard necklace/Witt inversion;


the 1999 erroneous explicit constant;


the present corrected fixed-label coordinate;


subsequent work citing the 1999 class-Mertens result and whether only its exponent, or also its constant, is used.


With these revisions, the paper would merit reconsideration as a mathematically sound and useful correction note.
