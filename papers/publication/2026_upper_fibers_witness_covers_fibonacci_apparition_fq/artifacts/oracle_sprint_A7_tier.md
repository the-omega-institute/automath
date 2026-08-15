1. The single most valuable new result
Verdict
There is no theorem that is simultaneously reachable from the machinery presently in the paper and likely to raise it by one tier. The structural ceiling is real: the manuscript’s effective machinery is intrafiber and combinatorial—witness covers, exact-rank support windows, minimal transversals, and fibotomic size/radical bounds—whereas the plausible tier-raising problems require valuation parity, growing-rank prime distribution, or diagonal sieve/Chebotarev input.
I checked that the reconstruction now contains the claimed main infrastructure: the exact witness-cover bijection is Theorem 3.7, including uniqueness and the bound ω(m)≤ω(n); the prime-power lifting, prime–ladder dichotomy, and unique ladder-slot formulas are in the main text; and the rank-pure sector is canonically the squarefree part of Mn​ on squarefree indices.    The ceiling therefore is not caused by the earlier proof-closure defects. It is caused by what the closed machinery can and cannot see.
First-choice ceiling theorem: Fibonacci odd-multiplicity primitive divisors
The most valuable theorem adjacent to the paper is:

Theorem GF​ — Fibonacci odd-multiplicity primitive divisor theorem.
For every integer n>12, there exists a prime p such that
α(p)=nandνp​(Fn​)≡1(mod2).
Equivalently, every Fn​ with n>12 has a primitive prime divisor occurring to odd multiplicity.

The weaker eventual statement—there exists NF​ such that this holds for every n≥NF​—would already settle the Fibonacci case of Andrew Granville’s conjecture in §7, “Open problems,” of Primitive prime factors in second-order linear recurrence sequences, Acta Arithmetica 155 (2012), 431–452. Granville conjectures eventual odd-multiplicity primitive divisors for every nonperiodic Lucas sequence, proves a substantial even-parameter case, and explicitly identifies the odd-b, odd-c case, including Fibonacci, as the case where the required Jacobi-symbol formula was unavailable. 蒙特利尔大学数学与统计系
For n>12, the formulation with α(p)=n is the standard Fibonacci exact-rank formulation of being a primitive divisor, and νp​(Fn​) is precisely the lifting datum denoted hp​ in the manuscript. The manuscript itself correctly identifies Granville’s result and the exclusion of the Fibonacci recurrence.  
This is my first choice by mathematical value, but not a recommended revision target, because it is not realistically reachable from the present machinery.
Other candidates, ranked conceptually
Second: the exact-fiber normal-order theorem
∀ε>0,#{n≤x:​log#Mn​−4log2​(loglogn)2​>ε(loglogn)2}=o(x).(N)
This concerns the field’s standard object α−1(n), not merely an auxiliary class. It would complete the main counting programme of the paper and would unquestionably improve its mathematical level. But it is an open problem isolated by this manuscript rather than a previously named external problem.
Third: the Bugeaud–Luca–Mignotte–Siksek conjecture
∃c>0 ∃N ∀ composite n≥N,ω(Fn​)≥clogn.(BLMS)
This is Conjecture 5.1 of Bugeaud–Luca–Mignotte–Siksek, On Fibonacci numbers with few prime divisors, Proc. Japan Acad. Ser. A 81 (2005), 17–20. Their unconditional primitive-divisor argument gives only ω(Fn​)≥τ(n)−4, and they formulate the logarithmic lower bound as a heuristic conjecture. Samir Siksek
Fourth: the Cubre–Rouse diagonal entry-point problem
#{p≤x:p prime and α(p)=p+1}⟶∞.(CR)
Cubre and Rouse explicitly state that it is unknown whether infinitely many primes satisfy Z(p)=p+1, where Z=α, in the introduction to Divisibility properties of the Fibonacci entry point, Proc. Amer. Math. Soc. 142 (2014), 3771–3785. Their theorems concern densities of the fixed divisibility condition m∣Z(p), obtained by Galois theory and Chebotarev; the diagonal condition Z(p)=p+1 is materially different. arXiv
My bounded literature searches through 15 August 2026 found no indexed resolution of the Granville Fibonacci case or the Cubre–Rouse problem. That negative search is not proof of priority; both statuses would require a full citation-chain audit before any claim of settlement.

2. Reachability from the machinery already in the paper
Candidate 1: Theorem GF​
Existing machinery that would feed a proof
Three parts of the paper are directly relevant:


Classical prime-power rank lifting, Proposition 4.1. For p∈/{2,5},
α(pe)=pmax(e−hp​,0)α(p),hp​=νp​(Fα(p)​).
Thus the desired parity is parity of the exact datum already governing the ladder structure. 


Atomic classification and ladder slots. Once hp​ is known, the first nonprime atomic power over p occurs at exponent hp​+1. 


Fibotomic localization. Lemma 6.3 shows that the radical of the exact-rank prime family divides the fibotomic integer
Fn​=d∣n∏​Fdμ(n/d)​=Ψn​(1),
and Theorem 6.4 exploits its size together with p≡±1(modn).  


Deductions plausibly available from those ingredients
A plausible preparatory chain is:


Replace the radical divisibility statement by an exact valuation-by-valuation description of νp​(Fn​).


Separate the genuinely primitive exact-rank part from the small imprimitive correction caused by primes dividing the index.


Show that failure of Theorem GF​ forces the corrected primitive part of Fn​ to be a square.


Reformulate the desired theorem as a nonsquareness theorem for that corrected fibotomic primitive part.


The first two steps are plausible extensions of the paper’s lifting and fibotomic bookkeeping. They are not, however, presently proved in the manuscript: Lemma 6.3 deliberately stops at radical divisibility, and Theorem 6.4 discards all exponent parity information.
Genuinely new ingredient
The missing ingredient is a parity-sensitive nonsquare theorem, most naturally arising from a new Jacobi-symbol or quadratic-reciprocity identity for Fibonacci fibotomic quotients.
This is exactly the obstruction Granville identifies for odd b,c: his method proves odd primitive multiplicity in another parity regime but does not supply the required symbol formula for Fibonacci. 蒙特利尔大学数学与统计系 Size estimates, congruence classes, and radical divisibility cannot recover parity. All of them remain unchanged if every exact-rank exponent is replaced by a sufficiently large even exponent.
Reachability verdict: NO. Proposition 4.1 explains the consequences of hp​; it does not control whether hp​ is odd. Theorem 6.4 controls products of distinct exact-rank primes; it is invariant under the parity information needed here. A proof would require a new arithmetic mechanism at least as substantial as the missing part of Granville’s programme.
Falsification tests


The strong cutoff n>12 is falsified by any explicitly factored Fn​, n>12, for which every primitive prime divisor occurs to even exponent. The existing n≤210 battery is relevant sanity evidence but cannot support the infinite claim.


The proposed proof route is falsified if an exact computation of νp​(Fn​) leaves uncontrolled nonsquare imprimitive factors, so that “all primitive exponents even” does not yield a usable square-class statement.


A failed attempt to obtain a nontrivial Jacobi-symbol recurrence in the odd-b,c case would reproduce Granville’s stated barrier rather than advance it.


A prior paper proving the Fibonacci case, even in an equivalent fibotomic formulation, would eliminate the priority claim.



Candidate 2: exact-fiber normal order (N)
Existing machinery that would feed a proof
The lower half is effectively complete. Theorem 6.5 gives
log#Mn​≥4log2​ω(n)2−O(1),
and Hardy–Ramanujan supplies ω(n)∼loglogn almost everywhere. 
For the upper half, the manuscript supplies unusually precise reductions:


The exact rank-pure weighted sum and
log#Rnrp​=4log2​ω(n)2+logW(n)+O(ω(n)).


Necessity of
logW(n)=o((loglogn)2)
on almost all odd indices.


The explicit warning that this condition is not sufficient because of ladder and other non-rank-pure covers. 


Deaggregation of support windows to the visible single-rank maximum A∗(n). 


Singleton control of every labelled ladder slot.


A sharp proof that cumulative information such as ω(Fn​)=∑d∣n​a(d) cannot by itself control the weighted sum. 


Deductions plausibly available from those ingredients
Two further reductions appear plausible:


Sharpen the private-coordinate upper encoding so that the singleton ladder slots are separated from the genuinely multiplicative prime windows, rather than absorbed into the coarse factor R(n)ω(n).


Reformulate the remaining rank-pure term as a divisor-weighted average of loga(d), possibly after stratifying by support size and by the central cover sizes s∼ω(n)/2.


Such work could improve the interface and might replace H1/H2 by weaker, more nearly necessary conditions. It would be worthwhile, but it would still be an interface theorem, not the normal-order theorem itself.
Genuinely new ingredient
One needs actual inter-index arithmetic distribution of
a(d)=#{p:α(p)=d}
for many simultaneously moving divisors d=nS​ of a typical n. Plausible mechanisms would involve some combination of:


moving-parameter Chebotarev uniformity;


a large sieve for orders in the Fibonacci torus;


control of small exact-rank primes or of the least exact-rank prime;


upper-tail estimates for a(d) averaged over structured divisor lattices;


p-adic frequency information for the complementary ladder sector.


The manuscript correctly explains why fixed-d rank-divisibility densities and fixed-index results do not provide this growing exact-fiber uniformity.  It also correctly states that no implication from RH or ERH presently closes the interface. 
Reachability verdict: NO. The paper has successfully exposed the required new arithmetic theorem, but has not supplied any mechanism for proving it. Better cover enumeration cannot manufacture distribution of the weights a(d).
Falsification tests


Extend the exact calculations on completely factored layers and record separately
ω(n)2logW(n)​,ω(n)2log(#Mn​/#Rnrp​)​.
Persistent positive values on increasingly representative odd or squarefree samples would contradict the proposed coefficient.


A positive-density pattern in which one or several medium supports have a(nS​)=exp(cω(n)) would defeat the intended weighted-cover estimate.


The route through a weakened maximum estimate is unsound if the central weighted cover polynomial remains exponentially sensitive to a collection of moderate weights even when every individual a(d) is below the proposed maximum threshold.


The BLMS conjecture does not itself falsify (N); it falsifies H1 and H2, which are only sufficient conditions. The manuscript now states this distinction correctly. 



Candidate 3: BLMS
Existing machinery that would feed a proof
The exact-rank existence theorem gives at least one new prime for nearly every divisor d∣n, reproducing the classical lower bound
ω(Fn​)≥τ(n)−O(1).
The manuscript also partitions ω(Fn​) exactly as ∑d∣n​a(d) and gives upper constraints on individual a(d).
Genuinely new ingredient
For indices with few divisors—especially n=pq or p2—the divisor-by-divisor primitive-prime argument supplies only O(1) primes, whereas BLMS asks for ≫logn. The missing mechanism must produce many distinct prime factors within a small number of cyclotomic or fibotomic components. That requires new sieve, Diophantine-factorization, or arithmetic-geometric input, not cover theory.
Reachability verdict: emphatically NO. Indeed, the manuscript’s own Proposition 6.8 shows that BLMS would invalidate the particular sparse-window hypotheses used for its conditional upper bounds. 
Falsification tests


To falsify BLMS itself, one needs a sequence of composite nj​→∞ with
ω(Fnj​​)/lognj​→0.
Individual small ratios do not suffice.


To falsify a proposed present-paper route, test it first on prime-square and semiprime indices. Any argument whose lower bound collapses to τ(n)−O(1) has not approached BLMS.


A literature hit proving only an almost-all bound, or a result for indices with many divisors, would not settle the stated uniform composite-index conjecture.



Candidate 4: Cubre–Rouse
Existing machinery that would feed a proof
The paper proves and repeatedly uses
∀d∈/{1,2,6,12}∃q prime such that α(q)=d.
The inverse-ray argument iterates precisely this statement.
But Cubre–Rouse asks for infinitely many primes p satisfying the self-referential equality
α(p)=p+1.
The exact-rank existence theorem gives, for each p+1, some prime q with α(q)=p+1; it gives no reason for q=p. This is the quantifier mismatch
∀d∃q⇒∃∞p[q(d)=p, d=p+1].
Genuinely new ingredient
A proof would require a diagonal prime-producing mechanism, plausibly:


Chebotarev with the extension varying with the candidate prime;


a sieve imposing primality and maximal-order conditions simultaneously;


an Artin-type theorem for the Fibonacci torus with sufficient uniformity.


Cubre and Rouse’s fixed-m density theorem uses a fixed algebraic group and Chebotarev to count m∣α(p); it does not give the diagonal equality α(p)=p+1. arXiv
Reachability verdict: NO. Neither witness covers nor inverse rays couple the output prime to the target rank in the required way.
Falsification tests


A proposed route is unsound if its Chebotarev field, discriminant, or error term depends on p so strongly that the error exceeds the main term before the sieve is applied.


A proof of positive density for each fixed condition m∣α(p) is not meaningful progress toward the diagonal problem unless it comes with uniformity when m is comparable to p.


A prior resolution or an equivalent Artin-type theorem would eliminate priority.



3. Probability × tier-impact ranking
These are subjective research-planning probabilities, not statistical frequencies. I distinguish:


PT​: probability that the stated theorem is true;


PM​: probability that an extension recognizably based on this paper’s machinery proves it;


P↑​: probability that, once proved and integrated, it actually raises the referee’s tier assessment;


effective success Peff​=PT​PM​P↑​;


impact on a 0–10 scale;


expected score =Peff​×impact.


RankCandidatePT​PM​P↑​Peff​ImpactExpected score1Granville/Fibonacci odd primitive multiplicity93%1.5%95%1.33%10.00.1332Exact-fiber normal order (N)45%3.0%90%1.22%8.50.1033BLMS ω(Fn​)≫logn80%0.3%99%0.24%10.00.0244Infinitely many p with α(p)=p+185%0.15%99%0.13%10.00.013
The apparently high PT​ for candidates 1, 3, and 4 should not be confused with accessibility. They are natural conjectural statements, but the present paper has almost none of the mechanism needed for them.
Candidate 2 has the largest connection to the paper’s existing machinery, but its truth probability is materially lower because:


the paper has no positive evidence for the required weighted dispersion;


its sufficient maximum-window hypotheses are predicted to fail under BLMS;


the ladder complement has not been shown negligible;


the manuscript’s sharp extremal result shows that the most readily available cumulative datum cannot settle the issue.


Thus even the most internally natural target is not currently a credible theorem project.
The operational conclusion from this table is not “try candidate 1 because it ranks first.” It is:

None has a success probability high enough to justify representing it as a realistically reachable resubmission addition.

A reasonable threshold for such a recommendation would be PM​ of at least roughly 20%. Every serious tier-raising candidate here is below 3%.

4. Which tier-raising levers apply to the leading theorem
For Theorem GF​:
(a) Settling a named open problem: yes, decisively
The eventual version settles the Fibonacci case of Granville’s explicitly stated conjecture on odd-multiplicity primitive prime divisors. The stronger cutoff n>12 would sharpen it by identifying exactly the classical primitive-divisor exceptional range. Granville explicitly names Fibonacci as an included unresolved odd-b,c case. 蒙特利尔大学数学与统计系
This is the strongest lever.
(b) A theorem about the field’s standard objects: yes
The theorem concerns:


primitive prime divisors of Fn​;


exact-rank primes Πα​(n);


the standard valuations νp​(Fn​);


the standard rank-of-apparition map.


It does not depend on the paper’s witness-cover terminology. Its significance survives unchanged if all of that terminology is removed.
This is a genuine second lever.
(c) Removing a hypothesis from an existing theorem: yes, but sequence-specifically
Granville proves an eventual odd-multiplicity theorem under a parity condition on the recurrence parameters and explicitly excludes the odd-b,c situation from the reach of his symbol calculation. A Fibonacci theorem would remove that parity obstruction for the most prominent excluded sequence. 蒙特利尔大学数学与统计系
It would not remove the hypothesis for all Lucas sequences. Therefore this should be described as resolving the principal Fibonacci case, not as a complete generalization of Granville’s theorem.
(d) Sharpness or matching-bound theorem: no
Odd primitive multiplicity is an existence/parity theorem, not a demonstration that one of the paper’s bounds is optimal. Recasting it as “the primitive part is nonsquare” does not turn it into a sharpness theorem.

5. Strongest remaining higher-tier objection after proving the leading theorem
Hardest plausible objection

“The manuscript now contains a genuinely higher-tier primitive-divisor theorem, but that theorem is methodologically detached from the witness-cover paper. Exact-rank prime existence already supplies a singleton prime generator in Mn​; proving that one such prime has odd valuation does not materially strengthen the witness-cover classification or the weighted-cover enumeration. The result therefore looks bolted onto a separate, substantially more elementary paper.”

This objection would be serious. The present paper itself emphasizes that its inverse-ray application does not use its central machinery; the same structural problem would recur at a much higher level if an odd-multiplicity theorem were proved by an unrelated argument.  
The parity datum hp​mod2 is visible in the prime-power lifting formula, but the witness-cover classification uses the location of the ladder threshold hp​+1, not its parity in a way that affects the existing counts. Therefore mere notational overlap would not answer the objection.
Exact resolution
A successful integrated paper would need all three of the following.
1. A valuation-sensitive fibotomic theorem, not merely an imported parity result
Section 6 would need to be upgraded from radical and size information to an exact statement of the following shape:

Primitive-part factorization theorem.
Determine νp​(Fn​) for every prime p, separate the exact-rank primitive factor
Pn​=α(p)=n∏​pνp​(Fn​)
from all imprimitive correction factors, and prove that Pn​ is not a square for every n>12.

The precise correction formula must be proved in the Fibonacci normalization; I have not independently verified a complete formula of that form from the present manuscript. The manuscript currently proves only
p∈Πα​(n)∏​p∣Fn​,
which is deliberately insufficient to control square classes. 
The new nonsquare proof would need a Fibonacci-specific reciprocity or Jacobi-symbol identity overcoming the exact barrier Granville records. That identity—not the elementary equivalence between nonsquareness and an odd exponent—would be the genuine theorem-level ingredient.
2. Reorganize the paper around that arithmetic theorem
The higher-tier version should not retain the present rhetorical hierarchy. It should:


lead with the primitive-part parity theorem;


place lifting and fibotomic valuation theory before the cover enumeration;


present the witness-cover classification as a structural application of the now valuation-sensitive exact-rank theory;


move inverse rays, low-coordinate classifications, and extensive finite verification out of the main narrative unless they directly support the parity proof.


If the parity proof does not use the witness-cover theory in any essential way, the mathematically honest resolution is to split the work rather than claim a unified higher-tier contribution.
3. Close priority at the theorem-equivalence level
The existing bounded audit is not enough for a theorem of this importance. The required priority package would be:


a citation chase from Granville’s 2012 paper through Rotkiewicz’s Jacobi-symbol work and all subsequent primitive-divisor parity papers;


searches for equivalent formulations involving nonsquare Fibonacci cyclotomic or fibotomic parts, characteristic parts, primitive parts, or odd valuations;


explicit comparison with every theorem covering special index classes;


a statement distinguishing “every n>12” from Granville’s eventual conjecture;


confirmation that no later general Lucas theorem already includes b=c=1.


Without that priority closure, a higher-tier referee could reasonably withhold credit even if the proof were correct.
Final diagnosis
The reconstructed manuscript has reached the natural limit of its current method. It has converted the exact fiber into a precise combinatorial-arithmetic interface and has correctly identified where cumulative primitive-divisor data cease to suffice.  Its concluding questions accurately state that completing the normal-order programme requires simultaneous moving exact-rank control and a bound on the non-rank-pure complement. 
What it does not possess is a mechanism that produces:


parity of primitive valuations;


distribution of a(d) for growing, simultaneous d;


diagonal primes satisfying a relation between the prime and its rank;


many prime factors inside a single or sparsely many fibotomic components.


Those are precisely the mechanisms required by the available one-tier-raising targets. Consequently, the hard conclusion is:

No single theorem realistically reachable from the machinery already in this paper is likely to raise it by one tier. The best external ceiling theorem is the Fibonacci case of Granville’s odd-multiplicity primitive-divisor conjecture, but reaching it would require a new parity-sensitive reciprocity mechanism, not an extension of the witness-cover machinery.