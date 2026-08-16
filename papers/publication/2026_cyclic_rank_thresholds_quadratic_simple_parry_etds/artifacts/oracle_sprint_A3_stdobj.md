Object-level verdict
The manuscript has one genuine bridge to a standard object: bounded representations of zero in Pisot linear numeration systems and their finite-state recognition. The adjacent-window contraction is not intrinsically tied to the constructed sliding code once the rank congruences have been produced. Corollary 2.4 already exposes that bridge, although only for the canonical difference alphabet attached to the code. 
It does not presently bridge to numerical β-normalization, the β-transformation, carry propagation for normalization or successor, general right-closing maps, general synchronized transductions, or a recognized broad class of sliding block codes. The decisive mismatch is not merely terminology: the local equality is an equality of integer language ranks modulo um​, whereas numerical normalization concerns equality of values in Z[β] or equality of represented real numbers. The manuscript states this distinction correctly and supplies an explicit counterexample to any silent identification. 
A symbolic-dynamics referee would recognize that the manuscript computes standard invariants—injectivity, inverse anticipation, pair-graph survival, Fischer covers, Markov order, degree, and exceptional fibers—for a particular family of codes. But the aperture-linear theorem is not yet a theorem about sliding block codes as a standard class. Its proof exploits an arithmetic architecture that generic sliding block codes do not have:
recurrence coefficients uj​+modulus exactly um​+successive windows shifted by one+Pisot conjugate contraction.
The strongest plausible field-facing extension is therefore a quantitative theorem about bounded U-representations of zero, not about β-normalization or general symbolic codes.

1. Corrections to the object inventory
A. Items in list (a) that are repackagings of standard notions


The local map after output relabeling.
Once a legal output word is replaced by its canonical rank in Z/um​Z, the local rule is simply
(x0​,…,xm−1​)⟼j=0∑m−1​uj​xj​(modum​).
Thus the canonical-word output layer is only a symbolwise bijective relabeling of a modular weighted sliding block code. What remains nonstandard is the choice of weights, the modulus um​, and the parameterized family as m varies. It is not a standard linear cellular automaton: the input alphabet is generally only the digit subset {0,…,dU​}⊂Z/um​Z, not a finite module on which the local rule acts as a group endomorphism.


“Future-only inverse length.”
This is exactly one plus the least anticipation of an inverse sliding block code constrained to have memory zero. The manuscript says so explicitly. It is a standard invariant under that imposed one-sided convention, but it is not the same as right-closing delay or a general closing constant. 


The obstruction sets.
These are finite-block kernels of a banded Toeplitz operator over Z/um​Z, with the additional condition that the first coordinate be nonzero. “Toeplitz sliding rank-congruence kernel” is an accurate description; the particular coefficients and modulus remain map-specific.


The graphs ΓU,m​ and Γβ,m​.
They are coordinatewise-difference quotients of classical pair or fiber-product graphs. The graph principle, reachable-cycle test, and longest-path interpretation are standard. What is special is that every pair state closes on a single difference state and that the edge condition reduces to one recurrence-weighted congruence. The manuscript proves that quotient without loss by using both the consecutive rank interval and the full raw digit cube. 


“Bounded-zero strips.”
This is not a standard term. Each row
[et​,…,et+m−1​,−kt​]U​=0
is a standard bounded U-representation of zero. The manuscript-specific part is the organization of such words into a one-position overlap chain indexed by t.


The overlap threshold, finite-block onset, and branch locus.
These are ordinary notions—least parameter for injectivity or conjugacy, finite-block injectivity threshold, and exceptional fiber locus—applied to the constructed family. The named functions themselves are not pre-existing field objects.


The “boundary-modified constant-type” metallic model.
It should not be listed as standard Ostrowski numeration. The paper correctly notes that it uses weights qj​+qj−1​, permits a different lowest-digit boundary, and only retains the internal constant-type Ostrowski admissibility rule. 


The terminal words.
These are explicit minimal collision witnesses, analogous to extremal paths or kernel vectors. They are not standard objects beyond being finitely supported recurrence relations.


B. Corrections to list (b)
The following additions are warranted:


Zero automata and Büchi automata for representations of zero. This is the closest established automata-theoretic object. Finite recognition of bounded zero representations is a classical Pisot phenomenon, and modern formulations explicitly use a zero automaton. arXiv+2剑桥解决方案+2


Modular weighted sliding block codes restricted to a digit subshift. This is the closest standard symbolic-coding description after rank relabeling, although it is not a standard linear cellular automaton.


AFT and near-Markov sofic shifts, multiplicity sets, and multiplicity graphs. The critical quadratic image is genuinely classified in these standard terms.


Carry propagation for successor and normalization should be retained only as a nearby comparison object, not as an object already touched. Carry propagation is defined by the digits changed under N↦N+1, which is a different relation and observable from the manuscript’s modular rank carries. arXiv


The following should be downgraded or struck from the “genuinely touched” category:


Numerical β-normalization and addition: comparison only. Frougny’s classical theorem concerns finite-state computation of numerical normalization and addition in Pisot bases; the manuscript’s congruence does not compute that relation. Springer Link


Condition F and zero preservation: comparison only. The manuscript neither assumes nor proves them; their modern equivalence leads to topological-group constructions not present here. arXiv


The β-transformation as a dynamical map: not touched beyond using its greedy language and Parry boundary.


General Ostrowski numeration: not covered by the metallic boundary-modified model.


General Pisot substitutions, Rauzy fractals, central tiles, and geometric realization: too remote. Contracting conjugates alone do not constitute contact with those objects.


General constrained-system encoders: Ashley’s decoder bounds concern encoders relative to a presenting graph and its state count; the natural graph here has exponentially many states in m. IBM Research



2. Corrected standard-object table
standard objectyes / partially / nomachinery that appliesexact missing bridge if partialPisot linear numeration systems and canonical greedy U-representationsPartiallyThe Binet expansion, effective growth bounds, canonical rank interval, and recurrence arithmetic are used directly.The conclusions concern modular rank collisions, not uniqueness, normalization complexity, or arithmetic properties of ordinary U-representations themselves.Parry–Bertrand positional rank and simple-Parry languagesPartiallyConsecutive colexicographic rank and the recurrence for language counts give the exact modular pair-graph quotient. A comparison showing that the modular rank relation encodes a standard operation on β-expansions rather than a new operation on their ranks.Greedy β-shifts and simple-Parry shiftsPartiallyTheir legal languages and Parry words supply the output alphabet and rank weights.The code acts on the full raw digit shift, not on the β-shift itself, and no semiconjugacy with Tβ​, its natural extension, or its orbit coding is constructed.Bounded U-representations of zeroYesEvery collision row is exactly a bounded zero representation; adjacent-window contraction gives a quantitative overlap dichotomy. Corollary 2.4 is already stated entirely in these terms. For a broader theorem, only an extension from the canonical difference alphabet to an arbitrary fixed bounded coefficient alphabet is missing.Zero automata / Büchi recognition of zero representationsPartiallyThe rows lie in the standard zero-representation relation, and classical zero automata could remove unreachable carry values.The manuscript does not identify its m-dependent overlap graph with a higher-block graph or quotient of the standard zero automaton, nor give a quantitative automaton-state invariant.Numerical β-normalizationNoOnly the general Pisot-conjugate bounding style resembles normalization proofs.Rank congruence modulo um​ is not equality of β-values. The example with rank 8 but nonzero value 2+2β blocks the transfer. Finite-state addition in Pisot basesNoNo addition transducer or equal-value relation appears.One would need a map from the rank congruence to equality of two numerical representations and then to the established normalization/addition transducer.Condition F and zero preservationNoThey are deliberately absent from the proof.The contraction of two modular rows neither implies finite expansion of elements of Z[β−1] nor preservation of leading zeros.Carry propagation for successor or numerical normalizationNoThe proof has bounded integers called carries and an adjacent-carry collapse.These carries are quotients by um​, not states of a successor or normalization transducer; there is no represented-number equality or successor operation.Zeckendorf numerationPartiallyThe Fibonacci rank interval and recurrence annihilator give explicit finite-window formulas.The cyclic reduction step is not Zeckendorf normalization. A theorem about ordinary Zeckendorf carries would require equality of Fibonacci values without reduction modulo Fm+2​.Ostrowski numerationNo for the metallic model; partially at the level of analogyThe local constant-type admissibility rule is borrowed.The weights and lower boundary are different from standard Ostrowski representations, as the paper itself records.Sliding block codes, conjugacies, and inverse anticipationPartiallyThe map is a genuine sliding block code, and the least memory-zero anticipation is computed exactly by a pair-graph longest path. A theorem for an independently recognized class of codes. “Codes whose local rule is this recurrence-weighted reduction modulo um​” merely abstracts the manuscript’s construction.Right-closing or left-closing factor maps and closing delayNoInjectivity plus a one-sided inverse is stronger in the successful cases.Right-closing is meaningful for noninjective factor maps and compares asymptotic rays; the manuscript fixes memory zero and exact anticipation. It explicitly declines to identify the two notions. Classical pair graphs, fiber products, bundle graphs, and periodic collision certificatesPartiallyThe standard cycle test applies, and the difference quotient is exact because every bounded digit difference is realizable.A structural theorem for general pair graphs carrying a Pisot cocycle or another recognized class. Without the arithmetic quotient, the generic graph has exponential size.Linear or additive cellular automata over finite groupsPartiallyAfter rank relabeling, the local output is a linear form modulo um​.The domain alphabet is not the full group Z/um​Z, the global map is not a group endomorphism, and the modulus changes with m.SFT and sofic images, code degree, and exceptional fibersPartiallyThe image is presented by a de Bruijn overlap graph; injective cases are conjugate to a full shift, and critical fibers are explicitly classified.These are standard invariants of a newly constructed image, not a theorem about a previously studied shift or a stable class of factor maps.Fischer and Krieger covers, follower sets, synchronizing words, and Markov orderPartiallyUnique decoding of length-m labels proves intrinsic synchronization, follower separation, and identifies the right Fischer cover. A non-map-specific family. The exponential state count is explicitly relative to the chosen output alphabet and disappears under conjugacy to the full shift. AFT / near-Markov sofic shifts and multiplicity graphsYes, but only as a classification of the constructed critical imageThe two-fixed-point quotient is shown to be strictly sofic, near-Markov AFT, bi-resolving, and to have multiplicity graph K2,1​. No missing bridge for that particular classification; what is missing is any broader result about AFT shifts.Rational relations, subsequential transducers, and synchronized relationsPartiallyThe finite pair graph gives a rational relation, and finite inverse anticipation supplies bounded lag for the inverse relation.An explicit transducer-equivalence theorem and a bound on its lag that is stated for a recognized class of rational relations rather than this local rule. Existing synchronization theory starts from a relation already known to have bounded delay.Finite-state constrained-system encoders and decoder look-aheadNoThe output graph is a finite presentation and the inverse is a decoder.The construction is not an encoder obtained from a fixed constrained presentation in the Ashley setting, and a bound linear in the natural state count would still be exponential in m.The β-transformation, β-integers, central tiles, and Pisot substitution dynamicsNoOnly the greedy language and contracting conjugates are shared background.No orbit map, arithmetic embedding of β-integers, geometric realization, substitution, or tile boundary relation is constructed.
The strongest “yes” is therefore the bounded-zero row. The AFT classification is genuinely expressed in standard symbolic terminology, but it remains a classification of an image manufactured by the paper and offers no route to a broader theorem.

3. What confines the main theorem to the constructed code?
The roles of the special ingredients are different.
Essential for identifying graph paths with actual code collisions
The following three ingredients are indispensable:


The consecutive rank bijection
XU,m​⟶{0,…,um​−1}.
It makes output equality exactly equivalent to equality of ranks modulo um​.


Cyclic reduction by exactly um​.
This produces the recurrence-aligned modulus. A different modulus would destroy equation (2.15) or leave an uncontrolled extra term.


The full raw digit cube.
It realizes every ej​∈[−dU​,dU​] as a difference of two input digits. Without that realization, the difference graph could contain algebraic paths that are not collisions of the original code. The proof identifies this point explicitly. 


Essential for the linear contraction once congruences are available
Only the following are needed:


the recurrence-aligned modulus um​;


two adjacent sliding congruences;


bounded coefficients and bounded quotient carries;


Pisot contraction and finite algebraic separation.


The exact adjacent identity is
βm(et+m​+kt​−βkt+1​)=βAt+1,0​−At,0​+et​.
The bounded right side and finite separation force kt+1​=0 and et+m​=−kt​. 
Consequently, the rank bijection and full-cube realization confine the result as a theorem about code collisions, but they do not confine the contraction as a theorem about bounded zero relations. The irreducible core is:
Pisot recurrence+modulus um​+adjacent windows.​
That core does not extend to generic sliding block codes. Nor does it extend to numerical normalization, because numerical normalization supplies equality in Z[β], not divisibility of an integer rank by a recurrence term.

4. Strongest plausible theorem stated without manuscript vocabulary
The only credible target is a quantitative theorem about the standard zero-representation relation.
Theorem — linear transient bound for bounded zero representations in a fixed Pisot numeration system
Let U=(un​)n≥0​ be a strictly increasing sequence of positive integers with u0​=1, satisfying the integral recurrence whose characteristic polynomial is the minimal polynomial of a nonintegral Pisot number β. Fix an integer D≥1.
For m≥2, let Gm​(U,D) be the directed graph with vertex set
([−D,D]∩Z)m−1.
There is an edge
(e0​,…,em−2​)⟶(e1​,…,em−2​,em−1​)
if and only if there exists an integer c such that
e0​u0​+e1​u1​+⋯+em−1​um−1​+cum​=0.
Then there is an effectively computable constant C=C(U,D)<∞ such that, for every m≥2, if no directed cycle of Gm​(U,D) is reachable from a vertex whose first coordinate is nonzero, every directed path beginning at such a vertex has fewer than Cm edges.
Equivalently, for every m, either there is an ultimately periodic infinite chain of one-position overlaps of bounded U-representations of zero containing a nonzero exposed digit, or every such nonzero chain terminates after fewer than Cm overlaps.
The linear order cannot be improved uniformly over fixed Pisot numeration systems and fixed bounded coefficient alphabets: there is a fixed cubic Pisot numeration system for which, with coefficient alphabet {−1,0,1}, the maximum finite path length is at least m−O(1).
Why this passes the vocabulary test
The subject is the standard relation “bounded representations of zero in a Pisot numeration system.” Zero representations and their finite automata are independently studied in numeration theory; existing results concern finite or Büchi recognizability and the finiteness of zero automata. arXiv+2剑桥解决方案+2
The statement contains:


no canonical language rank;


no reduction map from raw words to legal words;


no output shift introduced by the manuscript;


no inverse-length notation;


no manuscript-specific obstruction set or graph;


no special terminal words.


It asks a quantitative question about the transient length of overlap paths in the standard bounded-zero relation. The genuinely new extension beyond Corollary 2.4 is that D is arbitrary and independent of the canonical greedy digit set.
I would not claim that this is already a major established problem in the zero-automaton literature. It is, however, the strongest theorem whose object is standard and whose proof remains recognizably the present proof rather than a new normalization project.

5. Feasibility audit
5.1 Machinery reused
The proof would use primarily items (iii) and (iv), together with the elementary path/cycle part of (ii).
The reused components are:


Effective growth bounds
bU​βn≤un​≤AU​βn.


Uniform quotient-carry bound.
If
j=0∑m−1​uj​et+j​=kt​um​,∣ej​∣≤D,
then
∣kt​∣≤KU,D​:=⌈bU​(β−1)DAU​​⌉.


Finite algebraic separation
δU,D​=min{∣a+k−βl∣:∣a∣≤D, ∣k∣,∣l∣≤KU,D​, a+k−βl=0}>0.


Contracting-embedding bound for
At,i​=j=0∑m−1​et+j​βij​−kt​βim​.


The exact adjacent relation
βm(et+m​+kt​−βkt+1​)=βAt+1,0​−At,0​+et​.


Finite small-m patching by exact directed-graph longest-path searches.


The existing manuscript already emphasizes that the large-m proof uses contraction rather than the exponential number of difference states. 
5.2 First genuinely missing lemma
Lemma — adjacent collapse for an arbitrary bounded coefficient alphabet
Let U and β be as in the theorem and fix D≥1. There is an effectively computable m0​=m0​(U,D) such that the following holds.
Suppose m≥m0​, et​,…,et+m​∈[−D,D]∩Z, and kt​,kt+1​∈Z satisfy
j=0∑m−1​uj​et+j​=kt​um​,j=0∑m−1​uj​et+1+j​=kt+1​um​.
Then
kt+1​=0,et+m​=−kt​.
This is Lemma 2.2 with dU​ replaced everywhere by the independent coefficient bound D. The proof appears to survive unchanged.
5.3 Why the lemma reaches the standard object
Its hypotheses mention only:


a fixed Pisot recurrence;


bounded integer coefficients;


two finite representations whose U-values are integer multiples of um​;


equivalently, two bounded U-representations of zero after appending the quotient coefficients.


It does not presuppose that the coefficients arise as differences of raw digits. It does not use a legal representation language, a consecutive rank interval, a local output alphabet, or a factor code. Thus it is genuinely a lemma about bounded zero relations.
5.4 Proof chain after the lemma


Construct the standard overlap graph.
A length-m coefficient word is an edge precisely when it extends by one bounded quotient coefficient to a U-representation of zero.


Bound all quotient coefficients.
The growth estimates give KU,D​, uniformly in m.


Apply the adjacent-collapse lemma.
Along any path of at least two edges and for m≥m0​,
k1​=k2​=⋯=0,em​=−k0​,em+1​=em+2​=⋯=0.


Force the path into the zero vertex.
A path of m+1 edges therefore reaches the all-zero state. Since that state has a loop, such a path would make a directed cycle reachable from the initial state.


Use the no-reachable-cycle hypothesis.
Hence every path from a first-coordinate-nonzero state has at most m edges for all m≥m0​.


Patch finitely many smaller m.
Their graphs are finite and exact. Taking the maximum normalized path length yields C(U,D).


Sharpness.
The fixed cubic example already supplies {−1,0,1}-coefficient paths of length m−O(1), independently of interpreting them as collisions of two raw words.


Which manuscript-specific inputs disappear?
They disappear immediately:


the canonical rank bijection;


the legal-word alphabet;


cyclic reduction as a defined map;


positive/negative realization of every coefficient;


the image shift and inverse decoder.


Which special inputs remain indispensable?
They remain throughout:


the modulus um​;


the same recurrence weights u0​,…,um−1​;


one-position translation between adjacent relations;


fixed-system constants from the Pisot conjugates.


Changing um​ to an unrelated modulus is the point at which the proof fails. The subtraction identity would acquire an uncontrolled modulus term, and the finite separation would no longer isolate et+m​+kt​−βkt+1​.
5.5 Extension or different project?
Difficult extension of the present proof, at the low end of that category—not a different research project.
The mathematics of the key lemma is local: replace the canonical digit bound dU​ by D, recompute the carry and separation constants, and repeat the contraction. The more demanding work would be:


checking all degree-one and boundary conventions;


stating the overlap graph in a form consistent with standard zero-automaton language;


proving effectivity cleanly for arbitrary D;


auditing whether the claimed theorem is genuinely absent from the zero-representation literature;


explaining its relation, or nonrelation, to the standard zero automaton.


By contrast, a theorem about numerical normalization would be a different project because it first requires a comparison relation that the present argument does not supply.
5.6 Success probability
0.90​
This is my probability that the theorem as stated is true and provable by the indicated extension. The main uncertainty is not the large-m contraction; that appears robust. The uncertainty is whether an overlooked boundary case for an arbitrary coefficient bound D, especially with nonstandard initial values, requires an additional finite family of exceptions or a slightly modified starting-state condition.
5.7 Fast falsification test
Use the non-Condition-F Pisot root of
x3−3x2+2x−1
with a strictly increasing associated recurrence beginning at u0​=1, and take D=2 or D=3.
For each m just beyond the explicitly computed contraction threshold:


enumerate all bounded solutions of two adjacent congruences;


compute their quotient coefficients kt​,kt+1​;


search for a solution with
kt+1​=0oret+m​=−kt​.


One such solution falsifies the missing lemma immediately. If the lemma survives, enumerate the reachable subgraph for moderate m and test whether every acyclic path from a first-coordinate-nonzero state has length O(m). This example is preferable to Fibonacci because it tests that the extension really remains independent of Condition F, rather than succeeding through an unacknowledged finiteness property.

6. Why I do not select a normalization or general coding theorem
A proposed theorem such as

“Injective Pisot normalization transducers have inverse anticipation O(m)”

would currently be unsupported for three independent reasons.
First, normalization transducers recognize equal numerical values, while the paper recognizes equal integer ranks modulo um​. Frougny’s theorem establishes finite-state numerical normalization in Pisot bases, but it does not identify that transducer with the modular rank map. Springer Link
Second, the full-cube realization is crucial to the exact collision graph. A normalization transducer generally has a redundant or signed input alphabet constrained by equality of values; its difference sequences are not obtained merely by taking positive and negative parts coordinatewise.
Third, the modulus um​ is what converts the recurrence into the boundary identity. Numerical equality gives a zero sum, not a multiple of a length-dependent recurrence term in precisely the required position.
Likewise, a theorem for general right-closing or injective sliding block codes is not plausible. Generic pair graphs have no scalar carry, no contracting algebraic embeddings, and no recurrence identity cancelling all interior coordinates. Calling the current quotient a pair graph does not transport the contraction to pair graphs generally.

7. Residual objection after proving the proposed theorem
The strongest fair objection would be:

The paper has successfully detached its contraction theorem from the specially named sliding code and restated it as a quantitative result about bounded zero representations. Nevertheless, the measured quantity is still the transient length of an m-dependent overlap graph in which the first m coefficients are tested against the distinguished terminal weight um​. This is not yet a standard invariant of the zero automaton, numerical normalization, the β-transformation, or a recognized class of factor codes. The theorem therefore broadens the coefficient alphabet but preserves the same recurrence-aligned moving-window architecture that generated the original map. Its significance may remain that of a sharp structural theorem about one specially arranged use of zero representations, rather than a theorem resolving a central question in Pisot numeration or symbolic dynamics.

That is a mathematical limitation, not a presentation or venue objection.
Even after the extension:


it would not quantify the number of states of the classical zero automaton;


it would not bound synchronization delay for numerical normalization;


it would not describe carry propagation under addition or successor;


it would not say anything about Tβ​-orbits, β-integers, central tiles, or substitution dynamics;


it would not apply to general sliding block codes with large pair graphs;


it would remain tied to the distinguished recurrence term um​ and consecutive translates of the same coefficient vector.


The proposed theorem is therefore a real crossing into a standard object, but a narrow one. The manuscript’s machinery does not currently support a stronger honest claim about the better-known standard objects of numerical β-normalization or general symbolic coding.
