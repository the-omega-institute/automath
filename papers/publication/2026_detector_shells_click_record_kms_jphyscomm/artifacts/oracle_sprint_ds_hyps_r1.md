(a) Experiment equivalence
Body result
Theorem 4.1 (Local equivalence of a stationary renewal window and Palm interarrivals).
The following is the complete statement, with page-break hyphenation and line wrapping normalized but wording unchanged:

Let p0​ be a probability mass function on N+​={1,2,…}, with finite mean
μ0​=d≥1∑​dp0​(d).
For any mass function p on N+​, put
μ(p)=d≥1∑​dp(d),ep​(a)=μ(p)Prp​(D>a)​,a∈N0​,(LE2)
so ep​ is the equilibrium forward-recurrence, or residual-life, distribution. 
For every N, let PN​ be a class of interarrival masses containing p0​. Suppose constants c,C>0, not depending on N, satisfy
Nsup​p∈PN​sup​Ep​ecD≤C,p∈PN​sup​∣μ(p)−μ0​∣≤CN−1/2,(LE3)
and
p∈PN​sup​H2(p,p0​)≤NC​,p∈PN​sup​H2(ep​,ep0​​)≤NC​.(LE4)
Let PN,p​ be the law of the equilibrium renewal indicator
(X0​,…,XN−1​),Xt​=1{t is a renewal epoch}​,(LE5)
on the deterministic lattice window {0,…,N−1}. Fix γ∈(1/2,1), and, for all sufficiently large N, define
mN​=⌊μ0​N​−Nγ⌋,QN,p​=p⊗mN​.(LE6)
For the local experiments
EN​=({0,1}N,{PN,p​:p∈PN​}),FN​=(N+mN​​,{QN,p​:p∈PN​}),
one has
Δ(EN​,FN​)⟶0.(LE7)

The convergence is uniform over p∈PN​. More precisely, if KN​ is the number of complete interarrivals between observed renewal epochs and
rN​=⌈2Nγ⌉,(LE8)
then the kernels constructed in the proof satisfy
δ(EN​,FN​)≤p∈PN​sup​PN,p​{KN​<mN​}=o(1),(LE9)
and
δ(FN​,EN​)≤p∈PN​sup​pPr​{LN​>mN​+rN​}+NC(1+rN​)​​=o(1).(LE10)
Here LN​ is the number of interarrivals after the first renewal needed to cross the right boundary in the equilibrium construction in the proof. The randomizations in (LE9)–(LE10) may use p0​,N,γ, but not the unknown p. 
Consequently, bounded-loss procedures transfer in both directions with uniformly vanishing risk discrepancy, and the experiments have the same local asymptotic minimax risks for bounded losses. For every finite-dimensional uniformly differentiable-in-quadratic-mean submodel through p0​=pθ0​​ whose bounded root-N local arrays lie in PN​, the information per unit calendar time is
Ical​(θ0​)=μ0​1​IPalm​(θ0​).(LE11)
If a pathwise differentiable scalar functional of p has i.i.d. canonical gradient φ∈L02​(p0​), its efficiency bound under N​-normalization of the stationary record is
μ0​Ep0​​{φ(D)2},(LE12)
with μ0​Ep0​​{φ(D)φ(D)⊤} for a vector-valued functional. The equivalence and bounded-loss risk-transfer conclusions remain valid after restriction to a fixed cone or other fixed local subset of PN​. The information matrix remains that of the ambient DQM family, while information and efficiency consequences are interpreted in the corresponding restricted local experiment; at a boundary or in a tangent cone, the relevant efficiency or minimax bound can therefore be a constrained-experiment bound rather than the ordinary unconstrained canonical-gradient variance. No global adaptive equivalence over an unknown compact set of centres is asserted. 

Every hypothesis and inherited restriction


Observation model. The section fixes an exact stationary equilibrium lattice-renewal indicator: renewal epochs themselves are observed on the lattice. It expressly excludes interval counts from a point process in which several arrivals may occur in one bin. 


Positive integer interarrivals. Every interarrival law is a probability mass function on N+​={1,2,…}, not a continuous law, a law allowing zero gaps, a Markov-renewal law, or a generic MAP law.


A fixed centre. A single law p0​ is fixed in advance and has finite mean μ0​. The sample size mN​ is formed using this fixed μ0​, not the unknown μ(p).


Triangular local classes. For each N, there is a class PN​ of interarrival laws, and p0​∈PN​.


Uniform exponential integrability. There are c,C>0, independent of N, such that
Nsup​p∈PN​sup​Ep​ecD≤C.


Root-N mean localization.
p∈PN​sup​∣μ(p)−μ0​∣≤CN−1/2.


Root-N Hellinger localization of the interarrival law.
p∈PN​sup​H2(p,p0​)≤C/N.


A second, separately imposed Hellinger condition on equilibrium residual lives.
p∈PN​sup​H2(ep​,ep0​​)≤C/N.
This is not stated merely for p; the residual-life laws must also satisfy the displayed local bound.


Equilibrium initialization. The finite window has law PN,p​ of the equilibrium renewal indicator, whose forward recurrence has mass ep​. It is not a renewal process started with a renewal at time 0.


Hellinger and deficiency conventions. Immediately before the theorem, the manuscript defines
H2(P,Q)=x∑​(P(x)​−Q(x)​)2
on countable spaces, and Δ as the maximum of the two Le Cam deficiencies. 


Fixed undershoot exponent. The theorem says “Fix γ∈(1/2,1).” Thus it holds separately for each fixed γ; it does not state uniformity over all γ∈(1/2,1), nor permit an arbitrary sequence γN​.


Sufficiently large N. The product size
mN​=⌊N/μ0​−Nγ⌋
is introduced only for sufficiently large N.


Known local centre in the randomizations. The comparison kernels may use p0​, N, and γ, though not the unknown p. Hence this is not adaptive equivalence with an unknown centre.


Additional hypotheses for the decision-theoretic clauses.


Risk transfer and equality of local asymptotic minimax risks are asserted for bounded losses.


The information identity additionally assumes a finite-dimensional uniformly DQM submodel through p0​ and that its bounded root-N local arrays lie in PN​.


The efficiency formula additionally assumes a pathwise differentiable functional with an i.i.d. canonical gradient in L02​(p0​).


The restricted-experiment extension is only to a fixed cone or other fixed local subset.




No global adaptation. The statement expressly disclaims global adaptive equivalence over an unknown compact collection of centres.


Is “general” accurate?
Only in a restricted technical sense. The class PN​ is nonparametric and otherwise arbitrary, but it must satisfy the common exponential-moment condition, root-N mean localization, and simultaneous O(N−1) squared-Hellinger bounds for both the interarrival and residual-life laws. The centre is fixed and usable by the randomizations.
Shortest accurate replacement:

“for uniformly exponentially integrable Hellinger-local classes of equilibrium lattice-renewal laws”


(b) Killed-reset similarity orbit
Body result
There is no numbered theorem matching the advertised sentence. The corresponding numbered body result is:
Proposition 3.1 (Recalled orbit-fibre consequence of minimal realization).
It invokes the immediately preceding unnumbered statement headed “Recalled minimal-realization uniqueness.”
The proposition’s complete statement, with line wrapping normalized, is:

Fix n≥2, put β=en⊤​, and let
Kn​={K∈Rn×n:K≥0, K1≤1, spr(K)<1}.
For K∈Kn​, define the killed-reset D-MAP by
T0​=K,T1​=(I−K)1β
and its Palm survival coordinates by Sk​(K)=βKk1. Call K minimal when both
C(K)=[1,K1,…,Kn−11],O(K)=​ββK⋮βKn−1​​
have rank n. Let
Gn​={M∈GLn​(R):M1=1, βM=β},
and let Pn​⊂Gn​ be the reset-preserving permutation matrices. 
For any declared subclass C⊂Kn​ of minimal kernels, fix the structural equivalence ∼C​ under which identification is requested, and assume that K∼C​L implies equality of visible laws. Examples are reset-preserving hidden-state relabeling and, in a serial rate chart, permutation of the rate coordinates. Define the Markovian orbit fibre
FC​(K)={M−1KM∈C:M∈Gn​}/∼C​.
Then standard minimal-realization uniqueness gives the following exact characterization.
(i) Two minimal kernels K,L∈Kn​ generate the same stationary visible click law if and only if
L=M−1KMfor the unique M∈Gn​
implementing their normalized minimal realizations.
(ii) Equivalently, the declared hidden object is identifiable from the visible law within C, modulo ∼C​, if and only if
#FC​(K)=1for every K∈C.
Pointwise identifiability at K is equivalent to the same condition at that K; if the cardinality exceeds one, its distinct classes are exactly the hidden nonidentifiability fibre. Thus this assertion is the orbit-fibre reformulation of part (i).
Part (ii) is deliberately recorded only as terminology: after the fibre has been defined, singleton fibre and identifiability modulo ∼C​ are the same assertion. Neither part is claimed as a new realization theorem. 

The invoked unnumbered realization result states:

Let (a,A,b) and (a,A,b) be two real scalar realizations of the same dimension n such that
aAkb=aAkb(k≥0).
Assume that both reachability matrices
[b,Ab,…,An−1b],[b,Ab,…,An−1b]
and both observability matrices
​aaA⋮aAn−1​​,​aaA⋮aAn−1​​
have rank n. Then there is a unique M∈GLn​(R) such that
a=aM,A=M−1AM,b=M−1b.


Every hypothesis and inherited restriction


Finite, fixed dimension. The two realizations have the same finite dimension n, with n≥2.


A fixed deterministic reset state. The reset row is specifically
β=en⊤​.
The result is not stated for an arbitrary post-click distribution β, still less for state-dependent post-click laws.


Special rank-one marked kernel. The D-MAP is required to have exactly
T0​=K,T1​=(I−K)1β.
Thus every click resets to the fixed state n, and T1​ is completely determined by K.


Markovian/stability conditions on K.
K≥0,K1≤1,spr(K)<1.
These make K a stable substochastic no-click kernel.


Minimality is essential. Both
[1,K1,…,Kn−11]
and
[β⊤,(βK)⊤,…,(βKn−1)⊤]⊤
must have rank n. For part (i), both K and L are minimal.


Equality is equality of the stationary visible click law. The identified object is the visible law, equivalently in the proof the full scalar sequence
βKk1,k≥0,
not the labelled hidden kernel itself. 


Normalized similarities only. The allowed similarity matrices must lie in
Gn​={M∈GLn​(R):M1=1, βM=β}.
An arbitrary element of GLn​(R) is not admissible.


The underlying realization theorem requires equality for every k≥0. It is not a finite-coordinate result unless further structure is supplied.


The underlying realization theorem requires both realizations to be real scalar realizations and both to satisfy full reachability and observability rank.


A declared Markovian subclass is part of the identifiability claim. For part (ii), one must specify a subclass
C⊂Kn​
consisting of minimal kernels. Valid representatives are those conjugates M−1KM that actually lie in this declared C, not every member of the unrestricted real similarity orbit.


A structural quotient must be fixed in advance. Identification is only modulo a specified equivalence relation ∼C​.


That equivalence relation must be sound for the observation law. The proposition explicitly assumes
K∼C​L⟹K and L have the same visible law.


The full Markovian intersection occurs only when C=Kn​. For a smaller graph-specific or serial subclass, the valid fibre is the orbit’s intersection with that smaller class, followed by the declared quotient.


Nonminimal kernels are excluded. The manuscript later states expressly that when the visible rank is below n, equal laws need not be related by an invertible n×n similarity. 


No interior-positivity assumption is needed for Proposition 3.1. Strictly positive entries and killing deficits are hypotheses of the later local-dimension result, not of this orbit characterization.


Is “general” accurate?
No. The proposition concerns minimal, fixed-dimensional, finite-state kernels with the particular point-reset form
T1​=(I−K)1en⊤​,
and the stochastic representatives are the orbit points lying in a predeclared subclass C⊆Kn​.
Shortest accurate replacement:

“For minimal finite-state kernels with a fixed point-mass reset”

A fully accurate replacement for the complete sentence is:

“For minimal finite-state point-reset kernels, equality of visible laws determines a reset-preserving similarity orbit, while valid stochastic representations are the orbit points lying in the declared Markovian subclass.”
