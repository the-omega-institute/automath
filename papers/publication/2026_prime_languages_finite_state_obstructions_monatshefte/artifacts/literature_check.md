# Literature and Novelty Check

Checked through 2026-08-15.  The arXiv searches below used the public Atom API
endpoint `https://export.arxiv.org/api/query`; DOI metadata was checked against
the Crossref REST API.  The purpose of the search was to delimit the theorem
claims, not to infer novelty from a null keyword search.

## arXiv API queries

The following literal `search_query` values were sent to the API (20 results
maximum per query):

- `all:"context-free" AND all:prime AND all:language`: four returned records,
  none on prime numeration languages.  The only mathematically related record
  was Borchert--Rampersad, *Inverse Star, Borders, and Palstars*,
  arXiv:1008.2440; it does not concern prime recognizability.
- `all:Pisot AND all:numeration AND all:automata`: eight returned records,
  including Carton--Couvreur--Delacourt--Ollinger,
  *Linear Recurrence Sequence Automata and the Addition of Abstract Numeration
  Systems*, arXiv:2406.09868 (conference DOI
  10.1007/978-3-031-97548-6_7); Charlier--Cisternino--Stipulanti,
  *Robustness of Pisot-regular sequences*, arXiv:2006.11126,
  DOI 10.1016/j.aam.2020.102151; Massuir--Peltomaki--Rigo,
  *Automatic sequences based on Parry or Bertrand numeration systems*,
  arXiv:1810.11081, DOI 10.1016/j.aam.2019.03.003; and
  Frougny--Steiner, *Minimal weight expansions in Pisot bases*,
  arXiv:0803.2874, DOI 10.1515/JMC.2008.017.  None of the returned records
  states prime-language REG- or CF-immunity.
- `all:"prime language" AND all:automata`: no returned records.
- `all:"abstract numeration systems" AND all:prime`: no returned records.
- `all:Ogden AND all:"interchange lemma"`: no returned records.  These are
  pre-arXiv classical papers and are cited by DOI below.
- Exact-title queries confirmed Dubbe, *The automaticity of the set of
  primes*, arXiv:2409.04314, DOI 10.1016/j.tcs.2025.115480, and Yuen,
  *Kleene Star of the Primes is not Regular in Any Base*, arXiv:2203.16088.

The arXiv API search is negative evidence only.  In particular, the older
JACM papers settle a stronger fixed-base question than their titles alone
suggest, so the paper does not advertise fixed-base CF-immunity as new.

## Exact classical citations

- William Ogden, "A helpful result for proving inherent ambiguity,"
  *Mathematical Systems Theory* 2 (1968), 191--194,
  DOI 10.1007/BF01694004.  This is the marked-position pumping lemma now
  called Ogden's lemma.
- William Ogden, Rockford J. Ross, and Karl Winklmann, "An 'Interchange
  Lemma' for Context-Free Languages," *SIAM Journal on Computing* 14 (1985),
  410--415, DOI 10.1137/0214031.  The present proof does not claim or reproduce
  their interchange lemma; ordinary context-free pumping suffices after a
  fixed-prefix quotient, while Ogden's lemma gives an alternative way to
  localize pumping beyond an eventual-recurrence transient.
- J. Hartmanis and H. Shank, "On the Recognition of Primes by Automata,"
  *Journal of the ACM* 15 (1968), 382--389,
  DOI 10.1145/321466.321470.
- M. P. Schutzenberger, "A Remark on Acceptable Sets of Numbers,"
  *Journal of the ACM* 15 (1968), 300--303,
  DOI 10.1145/321450.321461.  Contemporary citation records describe the
  Hartmanis--Shank and Schutzenberger conclusion as: no infinite set of
  base-`b` primes is recognized by a finite automaton or a pushdown automaton.
  Thus fixed-base prime CF-immunity is prior art.
- M. Minsky and S. Papert, "Unrecognizable Sets of Numbers,"
  *Journal of the ACM* 13 (1966), 281--286,
  DOI 10.1145/321328.321337.
- D. P. Allen, Jr., "On a characterization of the nonregular set of primes,"
  *Journal of Computer and System Sciences* 2 (1968), 464--467,
  DOI 10.1016/S0022-0000(68)80038-8.

## Pisot and numeration references

- Christiane Frougny, "Representations of numbers and finite automata,"
  *Mathematical Systems Theory* 25 (1992), 37--60,
  DOI 10.1007/BF01368783.  This is the normalization/finite-transducer source
  used for linear numeration systems whose characteristic polynomial has the
  Pisot property.
- Veronique Bruyere and Georges Hansel, "Bertrand numeration systems and
  recognizability," *Theoretical Computer Science* 181 (1997), 17--43,
  DOI 10.1016/S0304-3975(96)00260-5.
- Christiane Frougny and Boris Solomyak, "Finite beta-expansions,"
  *Ergodic Theory and Dynamical Systems* 12 (1992), 713--723,
  DOI 10.1017/S0143385700007057.
- Stephane Fabre, "Substitutions et beta-systemes de numeration,"
  *Theoretical Computer Science* 137 (1995), 219--236,
  DOI 10.1016/0304-3975(95)91132-A.
- P. B. A. Lecomte and M. Rigo, "Numeration Systems on a Regular Language,"
  *Theory of Computing Systems* 34 (2001), 27--44,
  DOI 10.1007/S002240010014.  This is cited to distinguish abstract
  numeration systems from the narrower linear Pisot `U`-systems proved here.

## Novelty boundary used in the manuscript

The following assertions are treated as new only relative to the literature
located above and are stated with their full hypotheses:

1. The two-pump block-action congruence modulo the square of the represented
   value and the resulting coprime-quotient chain for an arbitrary
   context-free sublanguage of canonical Zeckendorf representations.
2. CF-immunity of the Zeckendorf prime language, and the stronger unbounded
   distinct-prime-divisor consequences for context-free Zeckendorf
   sublanguages.
3. Prime REG- and CF-immunity for the explicitly defined class of positional
   linear Pisot `U`-systems: integer weights, finite digit alphabet, injective
   canonical representations ordered by length, and an eventual integral
   recurrence with nonzero trailing coefficient.  The proof uses only the
   recurrence block action; Frougny normalization supplies the standard
   finite-state canonical syntax/normalization interface for Pisot
   `U`-systems.

No claim is made for every object sometimes called a "Pisot numeration
system."  In particular, arbitrary real-base beta-shifts, non-positional
abstract numeration systems, systems without an eventual integral recurrence,
and non-injective redundant representations are explicit open interfaces.
The Pisot-unit hypothesis is needed for the unrestricted deep-quotient and
induced-tree conclusions and for unconditional bounded-omega immunity. For a
nonunit recurrence, primes dividing the trailing coefficient make the
companion action singular modulo some composite values. The local-adic
dichotomy nevertheless gives prime and bounded-Omega MCF-immunity; bounded
distinct-prime support can escape only through unbounded valuation at a prime
dividing the trailing coefficient.

## Multiple-context-free and adic extension (2026-08-03)

The public arXiv Atom endpoint at https://export.arxiv.org/api/query was queried
with the following literal searches (and with a single-record
search_query=id:2509.02117 control):

- all:"multiple context-free" AND all:pumping;
- all:"multiple context-free" AND all:prime;
- all:"adic topology" AND all:integers;
- all:"Cantor-Bendixson" AND all:"prime factors";
- all:"divisibility tree" AND all:language.

Every API request returned HTTP 429 after retries with an identifying user
agent and four-second spacing. These failures are not treated as null search
results. The corresponding arXiv web searches, Crossref bibliographic
searches, DBLP metadata, and exact-source checks located no paper asserting an
MCFL prime-immunity theorem for recurrence numeration, an MCFL-induced local
congruence orbit, or the induced divisibility-tree conclusion.

The following published inputs delimit what is not new:

- H. Seki, T. Matsumura, M. Fujii, and T. Kasami, "On multiple
  context-free grammars," *Theoretical Computer Science* 88 (1991),
  191--229, DOI 10.1016/0304-3975(91)90374-B. Its Lemma 3.2 is the weak
  pumping lemma supplying one synchronized family with 2k pumped factors.
- M. Kanazawa, G. M. Kobele, J. Michaelis, S. Salvati, and R. Yoshinaka,
  "The Failure of the Strong Pumping Lemma for Multiple Context-Free
  Languages," *Theory of Computing Systems* 55 (2014), 250--278,
  DOI 10.1007/S00224-014-9534-Z.
- A. Duncan, M. Elder, L. Frenkel, and M. Lyu, "A substitution lemma for
  multiple context-free languages," *International Journal of Algebra and
  Computation* (2026), DOI 10.1142/S0218196726500463,
  arXiv:2509.02117v4. The direct arXiv PDF was checked. Its Lemma 5.3 quotes
  the exact Seki weak-pumping factorization used in the manuscript, while
  Theorem 4.5 gives an every-sufficiently-marked-word alternative between
  bounded pumping and replacement from one of finitely many switchable-tuple
  families. The latter does not parameterize the replacements as simultaneous
  powers of fixed blocks and therefore does not itself provide the fixed
  affine matrix-power orbit or a return time uniform in the orbit parameter.
- K. A. Broughan, "Adic Topologies for the Rational Integers," *Canadian
  Journal of Mathematics* 55 (2003), 711--723,
  DOI 10.4153/CJM-2003-030-3. The Cambridge primary PDF was checked.
  Theorem 2.4 gives the rational-space classification, Corollary 3.1 gives
  the Cantor completion, and Theorem 4.3 treats full-adic prime-factor
  strata counted with multiplicity.

Accordingly, the manuscript cites the Seki pumping family and Broughan's
topological classifications as inputs. The claims retained as new are the
combination with a fixed recurrence block orbit, the deleted-prime intrinsic
Cantor--Bendixson rank for distinct prime support with bounded local
valuations, the nonunit escape dichotomy and MCF-immunity consequences, and
the unit-system arbitrary-depth quotient and induced-tree constructions.

The arithmetic comparison now also includes Y. Bugeaud and J.-H. Evertse,
"S-parts of terms of integer linear recurrence sequences," *Mathematika* 63
(2017), 840--851, DOI 10.1112/S0025579317000298. It studies the size of the
fixed-\(S\) part of recurrence terms; it does not state a synchronized-language
characterization. The manuscript therefore presents its Evertse--Schur lemma
as a classical arithmetic input organized for the language interface, not as
an independent priority claim.

For the retained supplementary finite-state results, Shen (2022) supplies a
qualitative ordinary-base finite-automaton obstruction. Dubbe (2025) instead
lets the automaton grow with the cutoff and proves that exact prime
recognition below \(x\) requires at least
\(x\exp(-c(\log\log x)^2\log\log\log x)\) states. The supplement fixes one
DFA first and gives lengthwise symmetric-difference and recall/precision
bounds, including a Zeckendorf analogue. It does not improve Dubbe's growing
state-complexity bound, and those ordinary-base results do not supply the
fixed-DFA residue-class error statement or its Zeckendorf version.

## Minimal-reachable recurrence and witness inflation (2026-08-03)

The public arXiv Atom API returned zero records for each of the following
literal queries:

- `all:"reachable recurrence module" AND all:"multiple context-free"`;
- `all:"minimal recurrence" AND all:"multiple context-free language"`;
- `all:"Fibonacci" AND all:"multiple context-free" AND all:"prime factors"`;
- `all:"nonunit Pisot" AND all:"context-free"`;
- `all:"affine block semigroup" AND all:numeration`;
- `all:"prime factor" AND all:"multiple context-free language"`;
- `all:"multiple context-free" AND all:numeration`;
- `all:"multiple context-free" AND all:prime`.

The broader query `all:"Pisot numeration" AND all:prime` returned only
Adrian-Maria Scheerer, "Normality in Pisot Numeration Systems,"
arXiv:1503.08047, published in *Ergodic Theory and Dynamical Systems* 37
(2017), 1872--1886, DOI 10.1017/etds.2015.53. It concerns normality of
prime concatenations and does not address MCFLs, reachable recurrence
lattices, or recurrence-witness inflation. The query
`all:"minimal polynomial" AND all:"numeration system" AND all:recurrence`
returned only Olivier Carton, Jake Sudbery, and Reem Yassawi, "From some
Pisot numerations to topological groups," arXiv:2606.30496. Its abstract
studies Condition F, topological
groups, and torus factors; it does not state the minimal-reachable determinant
lemma or the base-\(p\)/inflated-Fibonacci escape separation.

The cyclic-subspace identities used in the oracle response---equality of the
minimal and characteristic polynomials on a cyclic restriction, and recovery
of the minimal polynomial from the first Krylov dependence---are standard
rational-canonical-form facts; see F. R. Gantmacher, *The Theory of Matrices*,
vol. I, Chelsea, 1959, Chapter VI. They are not retained as new theorem
content.

Crossref bibliographic searches for `multiple context-free Pisot numeration
prime factor`, `minimal recurrence reachable lattice numeration`, `inflated
Fibonacci recurrence nonunit Pisot`, and `affine semigroup p-adic numeration`
returned only standard Pisot tiling, numeration, recurrence, and affine
semigroup papers unrelated to the retained strict separation. These searches are
negative novelty evidence, not a proof that no related result exists.

## Geometric-ray characterization (2026-08-07)

The public arXiv Atom API returned zero records for each of the following
literal queries:

- \`all:"multiple context-free" AND all:"geometric progression"\`;
- \`all:"multiple context-free" AND all:"bounded prime support"\`;
- \`all:"multiple context-free" AND all:"linear recurrence"\`;
- \`all:"multiple context-free" AND all:"S-unit"\`;
- \`all:"Pisot numeration" AND all:"geometric progression"\`;
- \`all:"numeration system" AND all:"bounded prime support"\`;
- \`all:"linear MCFG" AND all:"geometric progression"\`;
- \`all:"semidecidable" AND all:"multiple context-free" AND all:"numeration"\`.

Crossref and OpenAlex searches for the corresponding unquoted combinations
returned general references on MCFGs, geometric-progression-free sets, and
Pisot numeration, but no work combining an MCFL sublanguage, bounded prime
support, and an exact geometric numerical ray. This is negative novelty
evidence only.

Two published inputs delimit the claim. Seki--Matsumura--Fujii--Kasami,
*Theoretical Computer Science* 88 (1991), 191--229, supply the weak
synchronized pumping family. J.-H. Evertse, "On sums of \(S\)-units and
linear recurrences," *Compositio Mathematica* 53 (1984), 225--244,
Theorem 3, proves unbounded prime-ideal support in ratios of terms of a
nondegenerate recurrence with at least two characteristic roots. The latter
excludes a fixed-\(S\)-unit nondegenerate subsequence; Schur's polynomial
prime-divisor theorem handles the remaining one-root polynomial factor.
Neither published input states the manuscript's equivalence with the
existence of a finite-fan-out synchronized MCFG ray, nor the resulting
positive-semidecidability statement.

## Refreshed prior-art and decision-target audit (2026-08-08)

The two referee-critical classical records were rechecked against their
publisher metadata and indexed abstracts, rather than inferred from their
titles. Crossref gives DOI 10.1145/321466.321470 for Hartmanis--Shank and DOI
10.1145/321450.321461 for Schutzenberger. The Hartmanis--Shank abstract states
that neither the primes nor any infinite subset of the primes, in fixed-base
notation, is accepted by a pushdown or finite automaton. The Schutzenberger
abstract states that the two negative results on acceptable sets are extended
to arbitrary context-free languages. CORE's Cornell record reproduces the
Hartmanis--Shank abstract; Semantic Scholar and Unpaywall confirm the records
and publisher copies. The manuscript already cites both papers where it calls
fixed-base prime CF-immunity classical and explicitly says that their proofs
are not reproduced as new.

The reference lists supplied by Crossref were also inspected. They lead to
the already cited Minsky--Papert paper on unrecognizable sets, the classical
context-free-language sources, and the contemporary finite-automata work.
No item in those lists concerns Zeckendorf or Pisot numeration, MCFLs, a
recurrence block action, or the geometric-ray criterion.

A live arXiv API query for `all:"multiple context-free" AND all:prime`
returned zero records. Google Scholar searches for `"primes" "multiple
context-free" language`, `"Pisot numeration" prime language automata`, and
`"S-unit" "linear recurrence" geometric progression` returned the standard
MCFG pumping literature, general numeration references, and recurrence/S-unit
sources, but no prime-language result in Pisot numeration. Crossref searches
confirmed the two 1968 JACM papers and their citation trails. A zbMATH API
keyword search for `multiple context-free prime numeration` returned no
record. OpenAlex exhausted its anonymous daily query budget during the audit,
and the first Semantic Scholar search was rate-limited; these failures are
recorded as failures, not as negative results.

The proposed decision target does not define a new problem for the class
proved in the manuscript. Theorem~3.18 proves that the prime representation
language of every system satisfying (U1), (U2), and (U4) is MCF-immune, and
Euclid's
theorem plus canonical representation makes that language infinite.
Consequently it is never an MCFL. For effectively presented regular canonical
linear Pisot U-systems, the requested terminating algorithm is therefore the
constant algorithm returning `NO`; this is an immediate corollary, not a
tier-raising decision theorem.

The genuinely nontrivial nearby decision problem is whether the bounded-
outside-support condition in Theorem~3.14 holds, equivalently whether a
geometric synchronized scheme exists. Corollary~3.15 gives only positive
semidecidability. A full decision procedure would require an effective finite
bound on the number and lengths of synchronized pumped blocks, or an
equivalent negative certificate for the absence of exact geometric identities
among recurrence sequences generated by finite transition and affine-matrix
semigroups. No such bound follows from the cited pumping or recurrence
theorems; general zero/equality questions for linear recurrences already meet
Skolem-type barriers. The present tools therefore do not justify promoting
that semidecision procedure to a decision theorem.

## Deep exploration: bounded-support classification (2026-08-08)

Six theorem candidates were compared on a five-point scale (reach, novelty,
value).

1. General decidability of geometric synchronized schemes: (2, 5, 5).
   Corollary 3.15 checks any guessed scheme, but no finite bound on fan-out or
   block length is available. The nearest decision literature is the Skolem
   problem for linear recurrences, including Min Sha,
   "Effective results on the Skolem Problem for linear recurrence sequences,"
   J. Number Theory 201 (2019), DOI 10.1016/j.jnt.2018.08.012.
2. Classification for standard linear Pisot systems: (5, 4, 5). Greedy length
   thresholds and Pisot asymptotics force a geometric ratio to equal a power
   of the dominant root. The nearest numeration work is Frougny's finite
   normalization theory and Sadahiro's "Multiple points of tilings associated
   with Pisot numeration systems," DOI 10.1016/j.tcs.2006.02.017; neither
   concerns bounded prime support or MCFLs.
3. Prime support of every geometric ratio is contained in the minimal tail
   constant: (5, 4, 4). This follows from the manuscript's local return
   congruence. Evertse's 1984 S-unit recurrence theorem is the nearest
   arithmetic input, but it does not give this numeration-specific local
   restriction.
4. Remove the valuation-only escape alternative for nonintegral Pisot bases:
   (5, 4, 5). This is the universal negative half of candidate 2. The nearest
   prior work is again Pisot normalization/recognizability, not prime-support
   behavior of MCFL sublanguages.
5. Compute the local Cantor--Bendixson behavior with unbounded bad-prime
   valuations: (5, 3, 3). Broughan, "Adic Topologies for the Rational
   Integers," DOI 10.4153/CJM-2003-030-3, is nearest; the claim would mainly
   sharpen why the manuscript's bounded local valuations are necessary.
6. Extend the quantitative density theorem to bounded-ambiguity automata:
   (2, 2, 3). The deterministic stochastic decomposition does not control
   multiplicities or cancellation. Nearby ambiguity work includes Christian
   Herzog, "Pushdown automata with bounded nondeterminism and bounded
   ambiguity," DOI 10.1016/S0304-3975(96)00267-8, but it supplies no required
   prime-slice asymptotics.

Live API checks used the arXiv Atom API, Crossref, Semantic Scholar, and
zbMATH. Exact arXiv queries combining "multiple context-free" or "Pisot
numeration" with "geometric progression" or "bounded prime support" returned
zero entries. Crossref returned separate Pisot numeration, recurrence
prime-divisor, adic-topology, and ambiguity papers, with no combined result.
Semantic Scholar's broad search endpoint returned HTTP 429, so DOI lookups
were used to confirm Sadahiro (2006), Broughan (2003), and the classical
second-order recurrence prime-divisor record. Exact combined zbMATH searches
returned no entries; broader searches found 120 Pisot-numeration records and
105 multiple-context-free-language records, but no overlap matching the new
classification. These are negative search results, not a priority proof.

Candidates 2--4 were proved together. In a geometric synchronized scheme,
the finite-group block return modulo \(p^{v_p(c)+1}\) excludes every
\(p\mid b\) with \(p\nmid c_0\). For a linear Pisot greedy system, a scheme
of word lengths \(L+Dt\) satisfies
\[
U_{L+Dt-1}\le cb^t<U_{L+Dt},
\]
so \(b=\beta^D\). A nonintegral Pisot number cannot have a positive integral
power: every conjugate would then have modulus \(\beta>1\). Conversely, an
integer root \(B\) supplies the canonical ray \(0^{J+t}1\) of values
\(U_JB^t\). Thus the bounded-outside-support property is decidable on the
standard linear Pisot class and is positive exactly in degree one.

## Tier-up decision audit and refreshed prior art (2026-08-10)

The arXiv Atom API, Crossref, Semantic Scholar, and zbMATH Open APIs were
searched before the new proof audit. Exact arXiv combinations of `multiple
context-free` with `geometric progression` returned no record; searches for
effective linear-recurrence decision problems returned Min Sha's arXiv
1505.07147 and the current Skolem literature. Crossref confirmed the metadata
for Sha (DOI 10.1016/j.jnt.2018.08.012), Tarasov--Vyalyi (DOI
10.1007/978-3-642-20712-9_24), Ouaknine--Worrell (DOI
10.1007/978-3-642-33512-9_3), and Bell--Halava--Harju--Karhumaki--Potapov
(DOI 10.1142/S0218196708004925). Semantic Scholar's DOI lookup for Sha
succeeded and exposed the surrounding orbit/Skolem citation graph; later
broad searches were rate-limited and are not treated as negative evidence.
zbMATH returned the Skolem decision survey and Tarasov--Vyalyi's regular-
language/orbit work, while the exact MCFL/numeration/geometric query returned
no record.

The nearest mechanism remains the pair of classical inputs already used:
Seki--Matsumura--Fujii--Kasami's weak synchronized pumping lemma and
Evertse's Theorem 3 on unbounded prime-ideal support in quotients of a
nondegenerate recurrence. The nearest algorithmic boundary is
Tarasov--Vyalyi's equivalence between an orbit-hitting problem and a regular-
language intersection problem, together with the still-open general Skolem
problem surveyed by Ouaknine--Worrell. Bell et al. prove undecidability for
unrestricted multiplicative matrix equations, but their matrices do not
preserve the companion-form digit action or canonical conditions (U1), (U2),
and (U4),
so this is not an undecidability result for the manuscript's promise class.

The attempted full decision procedure stops at witness compression. For a
fixed synchronized scheme, DFA acceptance and the identity `N(t)=c b^t` are
decidable. To decide negative instances one needs a computable bound, from
the DFA and minimal tail recurrence, on fan-out and total block length of a
smallest positive witness. Ordinary DFA cycle deletion does not supply it:
two words with the same DFA endpoints can have different affine recurrence
matrices, and replacing one by the other can destroy `N(t+1)=b N(t)`. No
located result provides this bound, and no promise-preserving reduction was
obtained. General decidability, undecidability, and hardness therefore remain
open; only the existing positive semidecision and the weak-Perron algebraic
classification are integrated.

## Weak-Perron and length-order extension audit (2026-08-15)

Crossref metadata confirmed D. A. Lind, "The entropies of topological
Markov shifts and a related class of algebraic integers," Ergodic Theory
and Dynamical Systems 4 (1984), 283--300,
doi:10.1017/S0143385700002443. The standard weak-Perron characterization
used in the revised article is the spectral-radius characterization for
nonnegative integral matrices; Perron--Frobenius periodicity then implies
that a positive power coalesces all conjugates of maximal modulus.
Crossref metadata also confirmed H. Brunotte, "Algebraic properties of weak
Perron numbers," Tatra Mountains Mathematical Publications 56 (2013),
27--33, doi:10.2478/tmmp-2013-0023, which directly treats the algebraic
power characterization used in the residue proof.

The complete 51-page arXiv v1 of E. Charlier and S. Kreczman, "Numeration
systems without a dominant root and regularity," arXiv:2512.13180v1,
15 December 2025, was read for this audit. It removes Hollander's
dominant-root restriction by associating periodic alternate real bases to
positional systems and gives a full characterization of regularity through
the graph of greedy and quasi-greedy expansions of 1 in shifted alternate
bases. Its general procedure is a semidecision because Parry periodicity is
not decidable in general; it becomes a decision procedure when the
associated alternate base is known to be Parry. Proposition 10 derives
residue-class consecutive-quotient limits for a positional system whose
whole numeration language is regular. Remark 12 is closer to the present
weak-Perron proof: for an arbitrary linear recurrence, if its dominating
eigenvalues have equal p-th powers, then eventual increase of the term
moduli gives convergence of U_n/U_{n-p} to that common power.

In the manuscript's irreducible weak-Perron setting, separability makes all
peripheral multiplicities equal, weak-Perron periodicity makes their h-th
powers equal, and strict increase gives the eventual-increase hypothesis.
Thus Charlier--Kreczman already contain the asymptotic root-growth mechanism
needed for the greedy length squeeze, in essentially equivalent
quotient-limit form. The overlap is substantial at that step and the
mechanism is not claimed as new. Their paper does not discuss MCFLs, bounded
prime support, synchronized geometric schemes, Evertse's quotient theorem,
or the five-way radical/scalar-periodicity classification. The remaining
novel claim is therefore the interface from bounded outside-prime support on
an infinite finite-fan-out MCFL to a geometric synchronized ray, and the
classification of that phenomenon under the weak-Perron greedy hypotheses.
Conversely, the manuscript does not reproduce Charlier--Kreczman's global
regularity characterization.

The revised classification is not a claim of general decidability. It proves
the five-way equivalence between bounded outside support, a geometric
synchronized scheme, an integral positive power of the weak Perron number,
divisibility of a binomial by the minimal tail polynomial, and eventual
scalar periodicity. The alternating-radix family with successive radices
\(p,q\ge2\) and nonsquare \(pq\) provides regular nonintegral members with
minimal polynomial \(X^2-pq\).

Crossref metadata also confirmed D. Caucal and M. Le Gonidec,
"Context-Free Sequences," ICTAC 2014, Lecture Notes in Computer Science
8687, pp. 259--276, doi:10.1007/978-3-319-10882-7_16. The revised article
names the nearby degeneracy/Cobham-extension problem only as an open
interface. Its one-orbit existential conclusion does not compare the global
structure of one set in two multiplicatively independent representations.

## Slender-context-free Cobham priority audit (2026-08-15)

This audit was performed before adding the two-system theorem. Literal and
title searches covered `slender context-free numeration Cobham`, `thin
context-free language numeration`, `bounded context-free language numeration
system`, `context-free automatic sequences Cobham`, `abstract numeration
systems context-free`, `alternate numeration systems Cobham`, `linear
numeration systems slender language`, and `pushdown automatic sequences
degeneracy`. Exact-title and DOI searches were also run for the paired-loop
classification and the recurrence common-value theorem. Sources and metadata
were checked through Crossref, Semantic Scholar, the arXiv API, the Elsevier
article API, and publisher or repository copies when available. Google Scholar
subsequently rate-limited the shared address; no priority inference is made
from that failure or from any null query.

The closest language-theoretic source located was L. Ilie, G. Rozenberg, and
A. Salomaa, "A characterization of poly-slender context-free languages,"
RAIRO Theoretical Informatics and Applications 34 (2000), 77--86,
doi:10.1051/ita:2000100. Its Theorem 7 states that a context-free language is
0-poly-slender if and only if it is a finite union of 1-Dyck loops, i.e. sets
of the form `{u v^n w x^n y : n >= 0}`. The paper attributes the original
paired-loop characterization to M. Latteux and G. Thierrin, "Semidiscrete
context-free languages," International Journal of Computer Mathematics 14
(1983), 3--18, and an independent proof to L. Ilie, "On a conjecture about
slender context-free languages," Theoretical Computer Science 132 (1994),
427--434, doi:10.1016/0304-3975(94)00042-5. The same 2000 paper proves that a
context-free language is poly-slender if and only if it is bounded and
classifies the higher polynomial-growth cases by finite unions of higher
Dyck loops. Those results do not themselves compare values in two numeration
systems.

The closest arithmetic source located was M. Mignotte, "Intersection des
images de certaines suites recurrentes lineaires," Theoretical Computer
Science 7 (1978), 117--121, doi:10.1016/0304-3975(78)90043-9. Publisher and
Crossref metadata identify it as the common-value theorem for integer linear
recurrences with multiplicatively independent dominating roots. P. Kiss,
"On common terms of linear recurrences," Acta Mathematica Academiae
Scientiarum Hungaricae 40 (1982), 119--123, states the same finiteness result
after explicitly setting up integer recurrences with unique dominant roots.
Schlickewei--Schmidt's later intersection theorem supplies a substantially
broader qualitative classification, but it is not the historical source of
this dominant-root finiteness input.

The numeration search also returned the established slender-regular and
abstract/alternate-numeration literature, including J. Shallit, "Numeration
systems, linear recurrences, and regular sets," Information and Computation
113 (1994), 331--347, and the Cobham-extension/context-free-sequence problem
of Caucal--Le Gonidec already cited in the article. None of the located source
titles, abstracts, theorem statements, or citation trails states the exact
claim that one fixed set with slender context-free representation languages
in two multiplicatively independent weak-Perron greedy linear numeration
systems must be finite.

Priority verdict: the exact target survives the completed search, but only as
an unlocated statement, not as a novelty claim. Its proof must be presented as
a different project built from the classical finite paired-loop cover and
classical common-value finiteness. The negative search does not justify a
claim of first proof, and the poly-slender/bounded setting remains outside the
one-parameter argument.

## Submission consistency check (2026-08-15)

The article's present priority narrative is consistent with this audit. It
treats the Seki weak pumping lemma, Broughan's adic classifications,
Evertse's quotient theorem, Charlier--Kreczman's residue-growth mechanism,
the fixed-base Hartmanis--Shank and Schutzenberger results, the
Latteux--Thierrin--Ilie paired-loop classification, and Mignotte's
common-value theorem as prior inputs. The retained claims are limited to the recurrence-language
combination stated with its canonical-presentation hypotheses, the
deleted-prime local rank calculation, the nonunit escape dichotomy, the
geometric-ray characterization, and the stated unit and weak-Perron
classification consequences, together with the separately proved
slender-context-free two-system theorem. The separately submitted finite-state results
remain in Supplementary Information and are compared explicitly with Shen
and Dubbe. No broader priority claim is made for fixed-base prime CF-immunity,
for arbitrary objects called Pisot numeration systems, or for the
equal-peripheral-modulus quotient/root-growth mechanism.

## Bibliographic integrity audit (2026-08-15)

### Scope, counts, and method

The bibliography contains 78 distinct entries. Before synchronization, those
entries occurred 374 times across five physical representations: 78 in
`references.tex`, 78 in `submission_bundle/references.tex`, 78 in
`submission_bundle/source.zip`, 70 in the stale top-level
`submission_bundle.zip`, and the same 70 in the `source.zip` nested in that
top-level archive. The 70 archived keys were a strict subset of the current 78;
they introduced no additional distinct work. After this audit, all five
representations contain the same 78 entries (390 physical occurrences).

For each DOI entry, `CR-DOI` below means a direct Crossref REST request to
`https://api.crossref.org/works/{DOI}` followed by comparison of the returned
title and first author with the bibliography. For each entry without a DOI,
`CR-T/A` means a Crossref request with the entry's exact title in
`query.title` and lead author in `query.author`. Fuzzy top hits were never
accepted as confirmation. `DBLP-T/A`, `zbMATH-T/A`, and `S2-T/A` mean exact
title/author searches in those indexes. `arXiv-ID` means the official arXiv
Atom record for the cited identifier. Publisher or archive checks name the
official source explicitly. A DOI discovered for an entry that did not claim
one was used as verification evidence; omission of an otherwise optional DOI
was not treated as incorrect metadata.

### Per-entry verification table

| Key | Identifier or exact search and returned record | Classification |
|---|---|---|
| `AkshayBazilleGenestVahanwala2024` | CR-DOI `10.46298/lmcs-20(2:11)2024` returned *On Robustness for the Skolem, Positivity and Ultimate Positivity Problems*, S. Akshay. | Confirmed |
| `Allen1968` | CR-DOI `10.1016/S0022-0000(68)80038-8` returned *On a characterization of the nonregular set of primes*, Dennis Allen. | Confirmed |
| `AlloucheShallit2003` | CR-DOI `10.1017/CBO9780511546563` returned *Automatic Sequences*, Jean-Paul Allouche. | Confirmed |
| `ArtinMazur1965` | CR-T/A `On periodic points` + `M. Artin` returned the same title and M. Artin, DOI `10.2307/1970384`. | Confirmed |
| `Bell2020UpperDensity` | CR-T/A `The upper density of an automatic set is rational` + `J. P. Bell` returned the same title and Jason P. Bell, DOI `10.5802/jtnb.1135`. | Confirmed |
| `BellEtAl2008MatrixEquations` | CR-DOI `10.1142/S0218196708004925` returned *Matrix Equations and Hilbert's Tenth Problem*, Paul Bell. | Confirmed |
| `Berstel1973` | DBLP-T/A returned the exact title and Jean Berstel, pp. 345-358, ICALP 1972; OpenLibrary ISBN `0720420741` confirmed North-Holland publication in 1973. | Confirmed |
| `BerstelReutenauer2011` | CR-T/A `Noncommutative Rational Series with Applications` + `J. Berstel` returned the same book and Jean Berstel, DOI `10.1017/CBO9780511760860`. | Confirmed |
| `BertheGouletPerrin2025` | S2-T/A and DBLP-T/A returned the exact title and Valerie Berthe; the Dagstuhl record confirmed LIPIcs 334, article 143, DOI `10.4230/LIPIcs.ICALP.2025.143`. | Confirmed |
| `BodirskyGaertnerVonOertzenSchwinghammer2004` | CR-T/A returned the exact title and Manuel Bodirsky, pp. 262-270, DOI `10.1007/978-3-540-24698-5_30`. | Confirmed |
| `BowenLanford1970` | CR-T/A returned the exact title and R. Bowen, DOI `10.1090/pspum/014/9985`; Crossref gives pp. 43-49. | Confirmed after metadata correction |
| `Bourgain2013PrescribedDigits` | CR-T/A returned the exact title and Jean Bourgain, Israel J. Math. 194, pp. 935-955, DOI `10.1007/s11856-012-0104-2`. | Confirmed |
| `Bourgain2015PrescribedDigitsII` | CR-T/A returned the exact title and Jean Bourgain, Israel J. Math. 206, pp. 165-182, DOI `10.1007/s11856-014-1129-5`. | Confirmed |
| `BruyereHansel1997` | CR-DOI `10.1016/S0304-3975(96)00260-5` returned *Bertrand numeration systems and recognizability*, Veronique Bruyere. | Confirmed |
| `Broughan2003` | CR-DOI `10.4153/CJM-2003-030-3` returned *Adic Topologies for the Rational Integers*, Kevin A. Broughan. | Confirmed |
| `Brunotte2013` | CR-DOI `10.2478/tmmp-2013-0023` returned *Algebraic Properties of Weak Perron Numbers*, Horst Brunotte. | Confirmed |
| `BugeaudEvertse2017` | CR-DOI `10.1112/S0025579317000298` returned *S-parts of terms of integer linear recurrence sequences*, Yann Bugeaud. | Confirmed |
| `BustosKellendonkYassawi2025` | CR-DOI `10.1007/s00605-024-02053-y` returned *Almost automorphic and bijective factors of substitution shifts*, Alvaro Bustos-Gajardo. | Confirmed |
| `BhowmikSuzuki2024` | arXiv-ID `2406.13334` returned the exact title and Gautami Bhowmik, with Yuta Suzuki, published 2024-06-19. | Confirmed |
| `Buchi1960` | CR-T/A `Weak second-order arithmetic and finite automata` + `J. R. Buchi` returned the same title and J. Richard Buchi, DOI `10.1002/malq.19600060105`. | Confirmed |
| `Carlson1921` | CR-T/A `Uber Potenzreihen mit ganzzahligen Koeffizienten` + `F. Carlson` returned the same title and Fritz Carlson, DOI `10.1007/BF01378331`. | Confirmed |
| `CaucalLeGonidec2014` | CR-DOI `10.1007/978-3-319-10882-7_16` returned *Context-Free Sequences*, Didier Caucal. | Confirmed |
| `CharlierRampersad2011` | CR-T/A `The growth function of S-recognizable sets` + `E. Charlier` returned the same title and Emilie Charlier, DOI `10.1016/j.tcs.2011.05.057`. | Confirmed |
| `CharlierCisternino2021` | CR-DOI `10.1007/s00605-021-01598-6` returned *Expansions in Cantor real bases*, Emilie Charlier. | Confirmed |
| `CharlierKreczman2025` | arXiv-ID `2512.13180` returned the exact title and Emilie Charlier, with Savinien Kreczman, published 2025-12-15. | Confirmed |
| `CharlierRampersadRigoWaxweiler2010` | DBLP-T/A returned the exact title, Emilie Charlier as lead author, all four claimed authors, Integers 11B (2011), article A4. | Confirmed |
| `Cobham1969` | CR-DOI `10.1007/BF01746527` returned *On the base-dependence of sets of numbers recognizable by finite automata*, Alan Cobham. | Confirmed |
| `DrmotaMauduitRivat2009` | CR-T/A returned the exact title and Michael Drmota, Compos. Math. 145, pp. 271-292, DOI `10.1112/S0010437X08003898`. | Confirmed |
| `DrmotaMuellnerSpiegelhofer2021` | CR-DOI `10.1090/memo/1537` returned *Primes as Sums of Fibonacci Numbers*, Michael Drmota; the record confirms the 2025 Memoirs publication cited alongside the 2021 arXiv version. | Confirmed |
| `Dubbe2024` | CR-DOI `10.1016/j.tcs.2025.115480` returned *The automaticity of the set of primes*, Thomas Dubbe. | Confirmed |
| `DuncanElderFrenkelLiu2026` | CR-DOI `10.1142/S0218196726500463` returned the exact title and Andrew Duncan; the full author list is Duncan, Murray Elder, Lisa Frenkel, and Mengfan Lyu. | Confirmed |
| `Dusart2018` | CR-DOI `10.1007/s11139-016-9839-4` returned *Explicit estimates of some functions over primes*, Pierre Dusart, Ramanujan J. 45, pp. 227-251. | Confirmed |
| `Estermann1928` | CR-T/A returned the exact title and T. Estermann, Proc. LMS s2-27, pp. 435-448, DOI `10.1112/PLMS/S2-27.1.435`. | Confirmed |
| `Evertse1984` | zbMATH-T/A and the Numdam journal scan returned the exact title and Jan-Hendrik Evertse, Compos. Math. 53 (1984), pp. 225-244. | Confirmed |
| `EismanRavikumar2005` | DBLP-T/A returned the exact title, Gerry Eisman and Bala Ravikumar, ACSC 2005, pp. 219-228. | Confirmed |
| `Fabre1995` | CR-DOI `10.1016/0304-3975(95)91132-A` returned *Substitutions et beta-systemes de numeration*, Stephane Fabre. | Confirmed |
| `FlajoletSedgewick2009` | CR-T/A `Analytic Combinatorics` + `P. Flajolet` returned the same book and Philippe Flajolet, DOI `10.1017/CBO9780511801655`. | Confirmed |
| `Frougny1992` | CR-DOI `10.1007/BF01368783` returned *Representations of numbers and finite automata*, Christiane Frougny. | Confirmed |
| `FrougnySolomyak1992` | CR-DOI `10.1017/S0143385700007057` returned *Finite beta-expansions*, Christiane Frougny. | Confirmed |
| `HanselPerrin1989` | CR-T/A returned the exact title and G. Hansel, TCS 65, pp. 171-188, DOI `10.1016/0304-3975(89)90042-X`. | Confirmed |
| `HardyWright2008` | OpenLibrary ISBN `9780199219865` returned the exact title, G. H. Hardy and Edward M. Wright, Oxford University Press, 2008. | Confirmed |
| `HartmanisShank1968` | CR-DOI `10.1145/321466.321470` returned *On the Recognition of Primes by Automata*, J. Hartmanis. | Confirmed |
| `KanazawaKobeleMichaelisSalvatiYoshinaka2014` | CR-DOI `10.1007/S00224-014-9534-Z` returned *The Failure of the Strong Pumping Lemma for Multiple Context-Free Languages*, Makoto Kanazawa. | Confirmed |
| `Kitchens1998` | Crossref book DOI `10.1007/978-3-642-58822-8` returned *Symbolic Dynamics*, Bruce P. Kitchens, Springer, 1998; the subtitle matches the cited edition. | Confirmed |
| `Koga2019Density` | CR-T/A returned the exact title and Toshihiro Koga, Fundamenta Informaticae 168, pp. 45-49, DOI `10.3233/FI-2019-1823`. | Confirmed |
| `Kozik2005Conditional` | CR-T/A returned the exact title and Jakub Kozik, ENTCS 140, pp. 67-79, DOI `10.1016/j.entcs.2005.06.023`. | Confirmed |
| `LecomteRigo2001` | CR-DOI `10.1007/S002240010014` returned *Numeration Systems on a Regular Language*, P. B. A. Lecomte; volume 34 and pp. 27-44 match. | Confirmed |
| `Lekkerkerker1952` | Exact title search in Crossref returned no match; OpenAlex returned HTTP 429. zbMATH author/title search `au:lekkerkerker & ti:fibonacci` returned C. G. Lekkerkerker, Simon Stevin 29 (1952), pp. 190-195, matching the cited Dutch original. | Confirmed |
| `MaesRigo2002` | S2-T/A returned the exact title and the JALC DOI `10.25596/jalc-2002-351`; the official JALC page gives Michel Rigo first and Arnaud Maes second. | Confirmed after metadata correction |
| `Lind1984` | CR-DOI `10.1017/S0143385700002443` returned the exact title and D. A. Lind. | Confirmed |
| `LindMarcus1995` | CR-T/A returned the exact book title and Douglas Lind, DOI `10.1017/CBO9780511626302`. | Confirmed |
| `MinskyPapert1966` | CR-DOI `10.1145/321328.321337` returned *Unrecognizable Sets of Numbers*, Marvin Minsky. | Confirmed |
| `MauduitRivat2010` | CR-T/A returned the exact title and Christian Mauduit, Ann. of Math. 171, pp. 1591-1646, DOI `10.4007/ANNALS.2010.171.1591`. | Confirmed |
| `Maynard2019` | CR-T/A returned the exact title and James Maynard, Invent. Math. 217, pp. 127-218, DOI `10.1007/S00222-019-00865-6`. | Confirmed |
| `Montoya2025Relative` | CR-T/A returned the exact title and J. Andres Montoya, pp. 166-179, DOI `10.1007/978-3-031-97100-6_12`. | Confirmed |
| `Ogden1968` | CR-DOI `10.1007/BF01694004` returned *A helpful result for proving inherent ambiguity*, William Ogden. | Confirmed |
| `OgdenRossWinklmann1985` | CR-DOI `10.1137/0214031` returned *An Interchange Lemma for Context-Free Languages*, William Ogden. | Confirmed |
| `Muellner2017` | CR-T/A returned the exact title and Clemens Mullner, Duke Math. J. 166, DOI `10.1215/00127094-2017-0024`. | Confirmed |
| `Ilie1994` | CR-DOI `10.1016/0304-3975(94)00042-5` returned the exact title and Lucian Ilie; Crossref gives combined issue 1-2. | Confirmed after metadata correction |
| `IlieRozenbergSalomaa2000` | CR-DOI `10.1051/ita:2000100` returned the exact title and Lucian Ilie. | Confirmed |
| `LatteuxThierrin1983` | CR-T/A returned *Semi-discrete context-free languages*, M. Latteux, Int. J. Comput. Math. 14, pp. 3-18, DOI `10.1080/00207168308803373`. | Confirmed after metadata correction |
| `Mignotte1978Intersection` | CR-DOI `10.1016/0304-3975(78)90043-9` returned the exact title and M. Mignotte. | Confirmed |
| `PerrinPin2004` | OpenLibrary ISBN `9780125321112` returned *Infinite Words*, Dominique Perrin and Jean-Eric Pin, Elsevier, 2004, matching the full cited subtitle. | Confirmed |
| `Polya1923` | CR-T/A returned the exact title and G. Polya, Proc. LMS s2-21, pp. 22-38, DOI `10.1112/PLMS/S2-21.1.22`. | Confirmed |
| `OuaknineWorrell2012` | CR-DOI `10.1007/978-3-642-33512-9_3` returned *Decision Problems for Linear Recurrence Sequences*, Joel Ouaknine. | Confirmed |
| `RosserSchoenfeld1962` | CR-T/A returned the exact title and J. Barkley Rosser, Illinois J. Math. 6, DOI `10.1215/IJM/1255631807`. | Confirmed |
| `Rigo2014Vol1` | CR-T/A returned *Formal Languages, Automata and Numeration Systems 1*, Michel Rigo, DOI `10.1002/9781119008200`; the cited subtitle identifies volume 1. | Confirmed |
| `Rigo2014Vol2` | CR-T/A returned *Formal Languages, Automata and Numeration Systems 2*, Michel Rigo, DOI `10.1002/9781119042853`; the cited subtitle identifies volume 2. | Confirmed |
| `SalomaaSoittola1978` | CR-T/A returned the exact title and Arto Salomaa, DOI `10.1007/978-1-4612-6264-0`. | Confirmed |
| `Schutzenberger1968` | CR-DOI `10.1145/321450.321461` returned *A Remark on Acceptable Sets of Numbers*, Marcel Paul Schutzenberger. | Confirmed |
| `SekiEtAl1991` | CR-DOI `10.1016/0304-3975(91)90374-B` returned *On multiple context-free grammars*, Hiroyuki Seki. | Confirmed |
| `Shallit1996` | CR-T/A returned the exact title and Jeffrey Shallit, J. Theor. Nombres Bordeaux 8, pp. 347-367, DOI `10.5802/JTNB.173`. | Confirmed |
| `Shen2022` | CR-DOI `10.1016/j.tcs.2022.04.027` returned *Prime automata do not exist*, Zhao Shen. | Confirmed |
| `Sinya2021` | S2-T/A and CR-DOI `10.1007/978-3-030-67731-2_6` returned the exact title and Ryoma Sin'ya, SOFSEM 2021, pp. 74-88. | Confirmed |
| `Swaenepoel2020PreassignedDigits` | CR-T/A returned the exact title and Cathy Swaenepoel, Proc. LMS 121, pp. 83-151, DOI `10.1112/PLMS.12314`. | Confirmed |
| `TarasovVyalyi2011` | CR-DOI `10.1007/978-3-642-20712-9_24` returned *Orbits of Linear Maps and Regular Languages*, Sergey Tarasov. | Confirmed |
| `Yuen2022` | arXiv-ID `2203.16088` returned the exact title and Jason Yuen, published 2022-03-30. | Confirmed |
| `Zeckendorf1972` | Exact title search in Crossref returned no match and OpenAlex returned HTTP 429; zbMATH-T/A returned the exact French title, E. Zeckendorf, Bull. Soc. R. Sci. Liege 41 (1972), pp. 179-182. | Confirmed |

### Corrections and citation decisions

Four metadata values were corrected in every source/package copy:

- `BowenLanford1970`: pages `43--50` -> `43--49` (Crossref DOI
  `10.1090/pspum/014/9985`).
- `Ilie1994`: issue `no. 2` -> `no. 1--2` (Crossref DOI
  `10.1016/0304-3975(94)00042-5`).
- `MaesRigo2002`: author order `A. Maes and M. Rigo` ->
  `M. Rigo and A. Maes` (official JALC record and DOI
  `10.25596/jalc-2002-351`).
- `LatteuxThierrin1983`: title `Semidiscrete context-free languages` ->
  `Semi-discrete context-free languages` (publisher/Crossref DOI
  `10.1080/00207168308803373`).

No intellectual claim, theorem, citation key, or citing sentence changed.
No entry was deleted: every entry has a matching index, publisher, arXiv, or
journal-archive record, so there are no deletion-related citation decisions.
No entry remains unverified.

### Audit limitations and service failures

- Crossref direct DOI resolution succeeded for all 34 DOI-bearing entries.
  Those entries were checked against Crossref as the primary index; because
  none was unavailable or empty, the protocol's OpenAlex/Semantic Scholar
  fallback was not triggered. Accordingly, cross-source redundancy was not
  achieved for every DOI-bearing entry, although title and lead-author
  identity was checked for every DOI.
- OpenAlex returned HTTP 429 for every attempted non-DOI exact-title query.
  It supplied no usable evidence for any of the 44 non-DOI entries. Each such
  entry was therefore checked using Crossref plus an official/index source
  where available, rather than Crossref plus OpenAlex.
- Semantic Scholar was also rate-limited. It succeeded only for
  `BertheGouletPerrin2025`, `MaesRigo2002`, and `Sinya2021`; it returned HTTP
  429 for `Berstel1973`, `BhowmikSuzuki2024`, `CharlierKreczman2025`,
  `CharlierRampersadRigoWaxweiler2010`, `Evertse1984`,
  `EismanRavikumar2005`, `Kitchens1998`, `Lekkerkerker1952`, `PerrinPin2004`,
  `Rigo2014Vol1`, `Yuen2022`, and `Zeckendorf1972`.
- Crossref rate-limited several later fuzzy follow-up requests after the
  direct DOI pass. The affected entries were `BhowmikSuzuki2024`,
  `CharlierKreczman2025`, `PerrinPin2004`, and `Zeckendorf1972`; their official
  arXiv, book, or zbMATH records supplied the verification instead. Service
  failures were not treated as negative evidence.
- Exact-title normalization across TeX accents, mathematical markup, and
  publisher capitalization was assessed manually. Online-first years in
  Crossref were not substituted for the cited print-volume years (notably
  Bourgain 2013/2015, Dusart 2018, and Swaenepoel 2020).

## Incremental Cobham-positioning audit (2026-08-15)

This audit was made before adding the three comparison citations used in the
revised introduction and Remark 3.3. The cited papers themselves, rather than
secondary summaries, were checked for the hypotheses and conclusions below.

| Citation key | Required metadata check | Result |
|---|---|---|
| `AlbayrakBell2023` | The official arXiv record for `2304.09223v1` returned the exact title *Quantitative estimates for the size of an intersection of sparse automatic sets* and lead author Seda Albayrak. Crossref DOI `10.1016/j.tcs.2023.114144` returned the same title and lead author, with Jason P. Bell second, *Theoretical Computer Science* 977 (2023), article 114144. | Confirmed |
| `Durand2011CobhamSubstitutions` | The official arXiv record for `1010.4009v1` returned the exact title *Cobham's theorem for substitutions* and lead/sole author Fabien Durand. Crossref DOI `10.4171/JEMS/294` returned the same title and author, JEMS 13 (2011), no. 6, pp. 1799-1814. | Confirmed |
| `CharlierLeroyRigo2013CobhamANS` | Semantic Scholar record `1d76992ac15cc5c8f483d124d2459bd647d1a4dd` returned the exact title *Cobham's theorem for abstract numeration systems* and identified Charlier as lead author. The ORBilu author-preprint record `10993/11668` supplied the full author order Emilie Charlier, Julien Leroy, Michel Rigo and the 2013 date. | Confirmed |

The full 14-page Albayrak--Bell arXiv paper was read. Its Theorem 1.1 says that
if \(k\) and \(\ell\) are multiplicatively independent integers and \(X\) is a
sparse \(k\)-automatic subset of \(\mathbb N^d\) while \(Y\) is a sparse
\(\ell\)-automatic subset, then \(X\cap Y\) is finite with an effectively
computable bound from the bases, dimension, and minimal automata. Theorem 4.1
gives a closed explicit state-count bound. Taking \(X=Y\) yields simultaneous
sparse automatic finiteness. Since a slender regular integer-base
representation language is sparse, this contains the regular integer-base
specialization of Theorem 3.2 and is strictly stronger on that specialization:
it permits general sparse regular languages and supplies a quantitative bound,
whereas Theorem 3.2 supplies finiteness only.

The full Durand paper was read from arXiv `1010.4009v1` and checked against the
published metadata. Its Theorem 1 assumes that the same finite-alphabet
sequence is both \(\alpha\)-substitutive and \(\beta\)-substitutive, where
\(\alpha\) and \(\beta\) are multiplicatively independent Perron numbers, and
concludes that the sequence is ultimately periodic. This conclusion is
stronger than finiteness after a sparsity hypothesis, but its recognition
interface is a substitutive characteristic sequence. A genuinely nonregular
slender context-free representation language does not supply that hypothesis.

The complete 2013 Charlier--Leroy--Rigo author preprint was checked at ORBilu.
Definitions 33 and 34 require an abstract numeration system to be built from an
infinite regular language ordered genealogically and require the represented
subset to have a regular representation language. Definition 47 makes two
exponential systems independent when their dominant language-growth
eigenvalues are multiplicatively independent. Theorem 49 concludes that a set
recognized in two independent abstract numeration systems is a finite union of
arithmetic progressions; Theorem 52 is the two-exponential-system case. The
authors' peer-reviewed 2015 paper *An analogue of Cobham's theorem for graph
directed iterated function systems* (DOI `10.1016/j.aim.2015.04.008`) was also
checked and is a different result about recognizable real sets, self-similarity,
and graph-directed iterated function systems. The abstract-numeration theorem
is therefore cited to the 2013 preprint, not to the 2015 paper.

The statement-by-statement boundary is as follows. Albayrak--Bell subsume the
regular integer-base shadow and improve it quantitatively. Durand and
Charlier--Leroy--Rigo cover the Perron-substitutive and regular
abstract-numeration shadows, with ultimate-periodicity conclusions. None of
the three accepts a full representation language that is slender context-free
but nonregular, and an arbitrary weak-Perron positional system need not provide
the regular canonical/genealogical interface used by the older recognition
theorems. The novelty retained by Theorem 3.2 is thus the nonregular passage,
implemented by Lemma 3.1: paired word loops are transferred to numerical
recurrences with unique positive dominant roots despite peripheral collisions,
Jordan factors, and cancellation. No quantitative bound is claimed.

The Semantic Scholar Graph API returned HTTP 429 during a direct JSON follow-up
for the Charlier--Leroy--Rigo record; the indexed Semantic Scholar result and
the ORBilu full-text record were available. OpenAlex had exhausted its daily
budget. These service failures were not treated as negative evidence.

## Published-register and multidimensional follow-up (2026-08-15)

Crossref DOI `10.1016/j.tcs.2023.114144` was checked again before the final
positioning pass. It returns Seda Albayrak and Jason P. Bell, the exact title
*Quantitative estimates for the size of an intersection of sparse automatic
sets*, *Theoretical Computer Science* 977 (2023), article 114144. The
bibliography already cited this published article as the primary reference;
it did not cite the arXiv preprint alone, so no bibliographic-entry change was
needed.

The claimed journal register required one correction. Mignotte's 1978
*Intersection des images de certaines suites recurrentes lineaires* and
Ilie's 1994 *On a conjecture about slender context-free languages* are both
published in *Theoretical Computer Science*, as recorded by Crossref and by
the manuscript. Latteux--Thierrin's 1983 *Semi-discrete context-free
languages* is not: Crossref DOI `10.1080/00207168308803373` places it in
*International Journal of Computer Mathematics* 14, no. 1, pp. 3--18, which
matches `references.tex`. The revised comparison therefore treats
Albayrak--Bell as the natural published sparse-language benchmark without
making the inaccurate claim that all three older inputs appeared in TCS.

The full Albayrak--Bell paper was re-read for its multidimensional scope.
Theorem 1.1 applies to sparse automatic subsets of \(\mathbb N^d\) for every
positive integer \(d\), and Theorem 4.1 gives the explicit automaton-state
bound. Section 1 defines a \(d\)-dimensional automatic set through a finite
automaton over the synchronous padded alphabet \((\Sigma_k)^d\). Section 2
defines sparsity by requiring the corresponding tuple language to be sparse
regular; Proposition 2.1 allows general polynomial-growth bounded regular
languages, not only slender ones. Thus the result is broader than a
one-dimensional reading: besides the exact regular integer-base overlap with
Theorem 3.2, it covers regular sparse, including regular poly-slender,
integer-base tuple settings and does so quantitatively.

This extra dimension does not cover more of the nonregular content of
Theorem 3.2. A product or coordinate recoding is an Albayrak--Bell input only
if its padded synchronous tuple language is itself sparse regular, and their
coordinate evaluation remains ordinary integer-base valuation. A genuinely
nonregular paired-loop representation language therefore does not become an
automatic set merely by being described with several coordinates; recovering
the original concatenated positional value would additionally require a map
outside the coordinatewise valuation in their theorem. Their result likewise
does not settle nonregular poly-slender context-free representation
languages. The revised introduction and Remark 3.3 state both the broader
regular scope and this remaining interface boundary, while retaining the
absence of a quantitative bound as a limitation of Theorem 3.2.
