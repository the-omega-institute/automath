Overall judgment
I would not recommend acceptance in the present form. The mathematics appears correct, and the paper is now coherent, but the literature positioning has two material defects: it omits the Chow–Jones second-moment result from which the stated ordinary recurrence follows, and it incorrectly says that Sanna allows repeated Fibonacci parts. In addition, the claimed explanation for removal of the parity factor is true but not proved.
My editorial recommendation would be major revision if DMTCS permits a substantial repositioning; otherwise reject with encouragement to resubmit as a short note. This is no longer an unsalvageable paper. It is, however, a more modest note than the introduction claims.
1. Is losslessness really the substantive step?
Verdict: genuine proof, routine specialist verification
The losslessness argument is mathematically real. It is not an experimental state cutoff, and it does establish exactly the fact needed:


Lemma 3.1 enumerates the six possible first exits from {−1,0,1}2 and places them in four invariant escape regions which alternate under the carry update and cannot meet an accepting state. 


Lemma 3.2 applies that scalar no-return statement coordinatewise. Its carry identity
i=1∑k​ai​Fi​=pk​Fk+1​+rk​Fk​
is correct, and the bounds on pk​,rk​, together with gcd(Fn​,Fn+1​)=1, correctly force rn​=0 and pn​=σ at a target solution. 


Lemma 3.3 correctly converts equality modulo Fm+2​ into targets σj​Fm+2​, with σj​∈{−1,0,1}, and then invokes the no-return lemma to show that no accepting path has been removed. 


I found no hidden cascade issue or unjustified inference from growth. The proof does what it says.
But a competent reader in automatic numeration would indeed call the method standard and this particular instance routine. Finite-automaton normalization for recurrence numeration systems is classical; Berstel already describes Fibonacci representation counting through an unambiguous transducer and matrix products; and Sanna constructs fixed-p product automata, trims them, and proves strong connectivity and aperiodicity for ordinary Fibonacci power sums. arXiv+3Springer Nature Link+3Numdam+3
The only bespoke part here is the especially clean six-exit invariant-region check. Once Lemma 3.1 is seen, Lemmas 3.2–3.3 are standard carry bookkeeping. Moreover, one could obtain the existence of some finite automaton by taking the classical equality transducer and appending a terminal high digit to encode the three possibilities
Val(u)−Val(v)∈{−Fm+2​,0,Fm+2​}.
The manuscript’s contribution is therefore an explicit and economical automaton, not the discovery that a finite automaton exists.
So the distinction is:


Substantive for correctness: yes. Without it the displayed matrix might count the wrong object.


Substantive as research novelty: no. It is a necessary, elegant, routine verification.


Enough to carry the whole novelty claim: no.


The introduction should replace “the losslessness step is substantive” with something like “the key correctness verification is losslessness.” The present opening sentence about proving the state bound “exact” is also too strong: the paper proves that this cube is lossless, not that it is a minimal carry range or minimal state set. 
After losslessness, fixed-matrix rationality is the standard resolvent/Cayley–Hamilton argument, and the primitivity proof is a neat but short return-to-zero argument plus the zero-column loop.   That package is respectable note-level mathematics, not a major automata theorem.
One very small proof-writing point: in the q=2 calculation, the equation Bn+1​=Dn​ silently uses the fact that (1,1) and (−1,−1) are unreachable from the initial state. That is true by induction, but one sentence should be added. It is not a substantive gap. 
2. The literature comparison
2(a). Is the ordinary U(m) result known?
Yes, in substance it is already in Chow–Jones. It must be cited as a known consequence, not presented as an unaffiliated computation of the present paper.
Chow and Jones define
V(H)=0≤n≤H∑​R(n)2
and derive an exact inhomogeneous recurrence for vk​=V(Fk​). Its associated characteristic polynomial is
χ(X)=X5−2X4−3X3+4X2+2X−2=(X−1)(X+1)(X3−2X2−2X+2).
They then give an explicit solution containing the five characteristic modes together with the elementary endpoint term. arXiv+1
After shifting Fibonacci indices to the manuscript’s convention and passing from the inclusive V(Fk​) to the exclusive sum U(m), one subtracts
R(Fk​)2=⌊k/2⌋2.
This cancels the quadratic particular solution and leaves precisely the homogeneous fifth-order recurrence, including the +1 and −1 modes. Thus the manuscript’s exact U-polynomial is not written verbatim in Chow–Jones’s notation, but it is an immediate corollary of their recurrence and explicit solution. The authors may claim the indexing conversion and a separate minimality check, but not the underlying recurrence/factorization as a new computation.
For the other named works:


Chow–Slattery: no second-moment recurrence. Their paper gives an exact formula for R(n), an exact first-moment formula, and its asymptotics. arXiv


Stockmeyer: pointwise upper bounds and extremizers for R(n), not the interval second moment U(m). Chow–Jones themselves summarize Stockmeyer in exactly that role. arXiv


Bicknell-Johnson–Fielder: recursive formulas for individual values R(n), not the displayed second-moment recurrence. 泰尔与方在线+1


A more serious literature error: the statement about Sanna is false
The manuscript says that Sanna’s rF​(n) permits repetitions and is therefore a different counting function.  That is incorrect. Sanna defines rF​(n) as the number of representations of n as a sum of distinct Fibonacci numbers, using exactly the shifted convention f1​=1,f2​=2 employed here. He defines the ordinary power sums
SF(p)​(N)=n<N∑​rF​(n)p,
explicitly credits Chow–Jones for p=2, and lists the cubic X3−2X2−2X+2 as the minimal polynomial of the p=2 exponential rate. arXiv+1
This must be corrected. It is not a terminological nicety: Sanna is the closest existing automata-and-power-sums paper, and the manuscript currently manufactures distance from it by describing its basic counting function wrongly. Sanna also constructs fixed-p product automata and proves that the accessible graph is strongly connected and aperiodic, so the comparison must explain specifically what changes when ordinary equality is replaced by the residue fold. arXiv+1
The reference list presently contains neither Chow–Jones nor Chow–Slattery, despite making claims about the ordinary second moment that depend directly on that literature.  For DMTCS, whose own guidelines expressly require complete and correct credit to current related work, that is a publication-level defect. 离散数学与理论计算机科学
2(b). Is “pairing removes the parity factor” proved?
No. It is only asserted.
The introduction states that the fold’s pairing “is exactly what removes” the (X−1)(X+1) factor.  Later, Lemma 5.1 proves the individual-fibre identity
dm​(r)=Rm+1​(r)+Rm+1​(r+Fm+2​),
but the paper never sums this identity against the ordinary interval moments and never derives cancellation of the two characteristic modes. 
The missing proof is short and exact. With the manuscript’s indexing, one has
S2​(m)=U(m+1)−U(m−1)​(m≥1),
with the natural definition of the initial U-values.
Indeed, put F=Fm+2​, G=Fm+1​, and
an​=Rm+1​(n).
The fibre pairing gives
S2​(m)=0≤r<F∑​(ar​+aF+r​)2.
On the other hand, representations below Fm+3​=F+G, separated according as they use the part F, give
U(m+1)=0≤r<F∑​ar2​+0≤r<G∑​(ar​+aF+r​)2.
For r≥G, aF+r​=0, because the largest value representable with the first m+1 Fibonacci numbers is F+G−2. Subtracting the two displays leaves
U(m+1)−S2​(m)=0≤r<G∑​ar2​=U(m−1).
Now let E denote the shift in m. Then
S2​=(E−E−1)U=E−1(E2−1)U.
Consequently, if
(E2−1)(E3−2E2−2E+2)U=0,
then
(E3−2E2−2E+2)S2​=0.
This is the precise sense in which pairing annihilates the +1 and −1 modes.
So the explanatory sentence is correct but unsupported. The paper should add this identity as a proposition. Once it does, however, the exact S2​ recurrence becomes an elementary corollary of Chow–Jones plus the fold-pairing identity. The present automaton derivation remains a valid independent proof, but Theorem 1.2 can no longer be marketed as an isolated new recurrence discovered solely through the carry automaton.
3. Venue, form, and odds
Strongest genuinely plausible venue: DMTCS, as a short note
DMTCS is thematically appropriate: its automata section covers automata theory, and its author guidelines explicitly welcome self-contained short notes. Length is therefore not the problem. 离散数学与理论计算机科学+1
My estimates are:


As submitted: below 10% at DMTCS. A referee familiar with the recent literature is likely to catch both the false description of Sanna and the missing Chow–Jones citation immediately.


After a serious revision: approximately 30–35% at DMTCS.


The revision would need to do more than insert two citations. It should:


describe Sanna’s counting function correctly and compare the two fixed-degree automata directly;


cite Chow–Jones and present the U-recurrence as known in substance;


prove S2​(m)=U(m+1)−U(m−1);


recast the q=2 result as an independent automata derivation of a recurrence also obtainable from the ordinary second moment;


tone down “substantive losslessness” and “exact state bound” to a claim of an explicit, audited, lossless construction.


I am not naming Discrete Analysis as the next venue up. Sanna’s 13-page paper there treats all ordinary moment degrees, constructs the relevant product automata, obtains effective spectral data, and proves a nontrivial p→∞ result. The present manuscript is narrower, system-specific, and its q=2 theorem becomes an elementary corollary once the missing comparison is supplied. arXiv+1 I would put its chance there below 5%.
Note venue
If DMTCS declines it on significance, the natural home is the Journal of Integer Sequences, after explicitly connecting the S2​ and Mm​ sequences to OEIS entries or submitting them as new sequences. JIS specifically seeks nontrivial properties and connections among integer sequences. 滑铁卢大学计算机科学系+1 I would estimate roughly 55–65% there after the literature and framing repairs. The Fibonacci Quarterly would be an even safer, though less ambitious, fit.
Bottom line
The paper is not merely a computation, but neither is its losslessness lemma the conceptual advance the introduction says it is. The correct description is:

an explicit, lossless residue-fold automaton, a clean all-q primitivity argument, a sharp fibre-height conversion, and a few exact consequences for one Fibonacci-specific map.

That is enough for a respectable short note. It is not enough, without substantial reframing, for the current novelty narrative. The paper should be revised and submitted rather than withdrawn, but DMTCS is a borderline attempt, not a likely acceptance.
