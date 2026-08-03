# Literature and Novelty Check

Checked on 2026-08-02.  The arXiv searches below used the public Atom API
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
- A. Duncan, M. Elder, L. Frenkel, and M. Liu, "A substitution lemma for
  multiple context-free languages," *International Journal of Algebra and
  Computation* (2026), DOI 10.1142/S0218196726500463,
  arXiv:2509.02117. The direct arXiv PDF was checked; its Lemma 5.3 quotes
  the exact Seki weak-pumping factorization used in the manuscript.
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
