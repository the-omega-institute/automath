Overall conclusion
There is a qualifying theorem about a standard object that appears plausibly reachable, but it does not come from pushing the weak MCFL pumping lemma harder. The credible route is to replace existential one-orbit pumping by a standard global structure theorem for slender context-free languages and then combine the manuscript’s affine/Kronecker machinery with the classical theory of common values of linear recurrence sequences.
The strongest target I regard as realistic is:

A slender-context-free Cobham theorem for two multiplicatively independent weak-Perron linear numeration systems: if the representations of the same set of integers form slender context-free languages in both systems, then the set is finite.

That theorem passes the vocabulary test: its statement uses only standard notions. It is not a prime-support result, does not mention a synchronized family, and quantifies over the entire represented set in two numeration systems.
For general context-free languages or MCFLs, however, the honest ceiling remains negative. The manuscript itself correctly records that its extraction gives one pairwise-distinct orbit but no control of every long word, the whole language, or the same values in two representations.  The same obstruction is restated precisely at the Cobham interface: two representations of one set may furnish unrelated extracted families having no common values. 
Priority qualification
The Charlier–Kreczman qualification must remain explicit. Their Proposition 10 obtains residue-class consecutive-quotient limits for regular positional numeration languages, and their Remark 12 gives the converse p-step quotient-limit mechanism for an arbitrary linear recurrence when the dominating eigenvalues have a common p-th power and the term moduli are eventually increasing. arXiv+1
Accordingly, neither the manuscript’s residue asymptotics nor the growth limit used in the greedy length squeeze should be presented as the priority-bearing step. The manuscript now states the boundary correctly: its contribution is the prime-support/MCFL interface and the resulting classifications, not the quotient-limit mechanism.  The proposed theorem below may use that asymptotic input, but only with the same attribution.
I have not downgraded the manuscript’s present conclusions in reaching this assessment. In particular:


the general extracted value sequence is pairwise distinct without any assumed value monotonicity; 


prime and bounded-Ω representation languages are MCF-immune without a unit hypothesis; 


bounded outside-prime support is treated using the intrinsic least eventual annihilator, not an inflated recurrence witness; 


the weak-Perron classification includes genuinely nonintegral cases such as alternating radices with growth parameter B​. 


I. Corrections to the list of standard objects
Additions
1. Positional numeration systems with regular language but without a dominant root, together with their associated periodic alternate real bases.
This deserves a separate entry rather than being subsumed under ordinary weak-Perron or β-numeration. Charlier–Kreczman treat precisely this class and show that regular positional systems naturally lead to alternate real bases; their framework is broader than dominant-root Rényi systems. arXiv+1
2. Normalization relations and finite-state addition in Pisot and related numeration systems.
These are standard, central automata-theoretic objects close to the manuscript’s canonical-language assumptions. Frougny’s theorem that normalization and addition in a Pisot base can be carried out by finite automata is representative. The present machinery assumes an accepted canonical representation language; it does not construct or analyze the normalization relation itself. Springer Link
3. Dumont–Thomas numeration systems.
These are substitution-derived standard numeration systems. Their positionality is a live structural question: not every abstract numeration system is positional, and recent work gives conditions under which a Dumont–Thomas system admits a positional interpretation. arXiv
4. Slender context-free languages and poly-slender—or equivalently, for context-free languages, bounded—languages.
These are especially important here because they possess global structure absent from the weak MCFL pumping lemma. Every slender context-free language is a finite union of paired loops
{uvnwxny:n≥0},
while poly-slender context-free languages admit finite decompositions into higher-dimensional Dyck-loop forms. 科学直通车+1
5. The common-value problem for linear recurrence sequences.
This is the appropriate arithmetic object for any two-numeration theorem. Laurent characterized when two linear recurrences have infinitely many common values under broad hypotheses, while Mignotte proved finiteness, with effective bounds, when the two recurrences have multiplicatively independent dominating roots. 数学出版+1
Corrections and deletions
“Substitution dynamical systems associated with Pisot numbers” is too broad and should be struck in that form. The machinery has no output concerning orbit closures, invariant measures, spectral type, maximal equicontinuous factors, or tilings. The genuinely adjacent standard objects are Dumont–Thomas numeration systems and substitutive or generalized automatic sequences, where words are tied to integer representations. Dumont–Thomas positionality itself already requires a nontrivial transfer from substitution data to positional weights. arXiv+1
“Primitive-divisor phenomena” should be struck as a target. The manuscript proves escape of prime support, fixed-support rigidity, and quotient congruences. It does not identify a prime that is primitive for a recurrence term, control its rank of apparition, or prove a Zsigmondy-type conclusion. The close standard arithmetic topic is therefore S-unit and S-part behavior of recurrence terms, not primitive divisors. The manuscript itself accurately characterizes its Evertse input in those terms. 
The adic entry should be narrowed. Broughan’s adic topologies, completions, and ambient prime-factor strata are standard. The deleted-prime sets XK,E​, the particular intrinsic derivative used on them, and the “local prime-factor rank” are manuscript-specific packaging. The paper expressly describes Proposition 2.10 as a local refinement rather than a new classification of the ambient adic space. 
Prime-recognition languages should be separated from regular approximation, density, and state-complexity questions. The former are directly engaged by the main orbit machinery. The latter use different finite-automaton and analytic methods and, as the manuscript explains, reside in the supplementary material rather than the recurrent-MCFL theorem chain. 
II. Inventory of standard objects
Standard objectStandard formulation or representative sourceYES, PARTIALLY, or NOApplicable machinery item(s)Exact missing hypothesis, transfer, quantifier change, or estimateGreedy positional linear U-numeration systemsIncreasing integer place values with bounded quotients and greedy representations; Charlier–Kreczman’s definition is representative. arXivYES1–7— Theorems 2.22, 2.23 and 2.25 are directly about this standard class, under their stated recurrence hypotheses. Bertrand numeration systemsBruyère–Hansel; Parry-associated Bertrand systems are standard regular positional systems. Charlier–Kreczman distinguish them from the larger positional class. arXivPARTIALLY1–4, 7The Bertrand property alone does not supply every hypothesis used here. One still needs an eventual integral recurrence; the exact weak-Perron classification further needs the least recurrence polynomial to be the minimal polynomial of a weak Perron number.Pisot linear numeration systemsPositional linear systems governed by a Pisot recurrence; finite-state normalization is classical. Springer LinkYES1–7— For the usual linear U-system meaning, the manuscript’s standard greedy specialization applies directly. Normalization transducers and finite-state addition in Pisot basesFrougny, “Representations of numbers and finite automata.” Springer LinkNO—The affine matrices evaluate already canonical words. They neither recognize equality of two noncanonical expansions nor construct the normalization or addition relation.Regular positional systems without a dominant root and their alternate real basesCharlier–Kreczman’s regularity characterization and associated alternate bases. arXiv+1PARTIALLY1, 4, 7Item 7 covers the irreducible weak-Perron/common-power regime. What is missing is a transfer from the general alternate-base data—possibly with unequal residue growth factors or eigenvalue multiplicities—to the arithmetic MCFL conclusions.Rényi β-expansions, β-shifts, Parry languages, and β-integersThe β-shift is generated by x↦βxmod1; its language reflects the dynamics. Springer Link+1NO—The manuscript needs an integer-valued positional map with a stationary integral recurrence action. A real β-shift does not generally give a bijection from finite words to N, nor an integral block action invertible modulo rational integers.Cantor real bases and periodic alternate basesAlternate bases are standard Cantor real bases; Parry alternate bases are governed by ultimately periodic expansions of 1. ORBi+1NO—Their place weights are nonstationary products of real bases. The fixed companion matrix, integer congruences, and prime-support valuation arguments do not transfer.Abstract numeration systemsAn infinite regular language ordered genealogically/radix-wise; the n-th word represents n. ORBilu+1NO—Rank in a regular language is not generally a fixed digit-linear functional ∑aj​Uj​. Hence there is no compatible affine recurrence matrix or modular return theorem.Dumont–Thomas numeration systemsSubstitution-derived numeration systems; positionality is conditional rather than automatic. arXivPARTIALLY1–4, if positionalOne needs a theorem converting the substitution system into a unique positional integer system with eventually recurrent weights. Without positionality, the manuscript’s value matrices have no defined counterpart.U-recognizable or S-recognizable sets and generalized automatic sequencesRecognizability by automata reading representations in a numeration system; generalized automatic sequences extend base-k automaticity. arXivPARTIALLY1–3, 6–7The machinery proves nonrecognizability or stronger immunity for particular arithmetic sets. It does not characterize all recognizable sets or all generalized automatic sequences, and gives no logical closure theorem.Cobham-type recognizability in two multiplicatively independent systemsCobham’s theorem and its abstract-numeration/substitution extensions compare one set in two systems. SciSpace+1PARTIALLY1, 4, 7The missing quantifier change is simultaneous control of the same values in two representations. Independent weak-pumping applications yield unrelated one-parameter families.Context-free or pushdown-automatic sequences and the degeneracy problemCaucal–Le Gonidec ask which context-free or pushdown-automatic sequences are automatic, in analogy with Cobham-type degeneration. IGM+1NO—These are global characteristic-sequence questions. One infinite sublanguage and one extracted orbit give no control of the complete support or the entire output sequence.Slender context-free languagesExactly finite unions of paired loops {uvnwxny:n≥0}. 科学直通车+1PARTIALLY1, 4, 7The manuscript does not invoke this global decomposition. Once imported, one still needs to prove that every paired loop has, after residue restriction, a unique dominating recurrence root dictated by the numeration growth.Poly-slender or bounded context-free languagesPoly-slender CFLs are precisely bounded CFLs and finite unions of Dyck-loop configurations. Numdam+1PARTIALLY1, 4Their global decomposition has several independent parameters. A multivariate exponential-polynomial/common-value theorem would be needed; the one-parameter Kronecker lift is insufficient by itself.Multiple context-free languages of finite fan-outSeki–Matsumura–Fujii–Kasami; the weak pumping lemma extracts one synchronized family, while strong pumping fails in general. YES1–6, and 7 in the greedy weak-Perron subclass— The manuscript already gives arithmetic restrictions on every infinite MCFL sublanguage of the relevant standard numeration languages. “YES” does not mean a structural classification of MCFLs.Integer linear recurrence sequences and exponential polynomialsClassical Binet/exponential-polynomial theory; Evertse-type quotient results.YES4, 5, 7— The Kronecker lift produces a recurrence, and Lemma 2.15 is a direct statement about pairwise-distinct positive integer recurrences with finite prime support. Common values of two linear recurrence sequencesLaurent’s general characterization; Mignotte’s finiteness theorem for multiplicatively independent dominating roots. 数学出版+1PARTIALLY4, 7The manuscript constructs only one recurrence at a time. It lacks a reason that two recurrences obtained from representations of the same set have infinitely many common terms and suitable unique dominating roots.Skolem, Positivity, Ultimate Positivity, and linear orbit-hitting problemsStandard decision problems for recurrence sequences and matrix orbits.NO4 only supplies a finite identity testChecking whether an explicitly given recurrence is identically zero is not Skolem, Positivity, Ultimate Positivity, or general orbit hitting. The manuscript correctly claims no reduction in either direction. S-units and S-parts of recurrence termsEvertse; Bugeaud–Evertse.PARTIALLY5The manuscript handles the extreme case where every term is supported on one fixed finite prime set. It supplies neither quantitative S-part bounds for arbitrary terms nor density or height estimates. Fixed-base and Fibonacci/Zeckendorf prime-representation languagesHartmanis–Shank and Schützenberger for fixed bases; standard Zeckendorf representations.YES1–3; paired Ogden pumping in the Zeckendorf case— The manuscript proves MCF-immunity in general recurrent systems and a stronger iterative context-free obstruction in Zeckendorf representation. Regular approximation, density, and state complexity for arithmetic languagesWork on density and finite-state approximation of prime or other nonregular languages.NO for the main machinery—These require counting, spectral analysis of automata, approximation error, or automaton-size lower bounds. The affine orbit argument supplies none of those estimates.Perron, weak Perron, and Pisot numbers as algebraic or dynamical objectsStandard algebraic growth classes; weak Perron numbers have a positive power that is Perron.PARTIALLY7The manuscript classifies a language phenomenon for greedy systems whose recurrence has such a root. It proves no new intrinsic theorem about weak Perron numbers, conjugate distributions, or associated dynamical systems.Adic topologies, profinite completions, and prime-factor Cantor–Bendixson strataBroughan’s adic topologies and classifications.PARTIALLY3, 6Broughan supplies the standard ambient classifications. The manuscript’s new derivative calculation is for its specially defined deleted-prime subspaces, not a general theorem about arbitrary adic or profinite subsets. 
The honest ceiling for the present one-orbit machinery
The existential one-orbit output is indeed the decisive confinement for the main named global problems.
The weak MCFL pumping lemma says:
∃ one fixed synchronized family inside L,
whereas Cobham-type and context-free-sequence questions require statements of one of the following forms:
∀ sufficiently long words in L,
the whole representation language of X,
the same set X in two representations,
or
∀n in a recurrence or characteristic sequence.
The newer substitution lemma mentioned by the manuscript has a more global quantifier but admits a switchable-tuple alternative, so it does not yield fixed powers of fixed affine matrices.  Therefore it does not, in its present form, repair the simultaneous-value problem.
The important exception is slender CFLs: their known finite paired-loop decomposition changes the quantifier from “there exists one pumped family” to “the entire language is a finite union of such families.” That is why the theorem below is plausible while a general context-free or MCFL Cobham theorem is not.
III. Strongest plausible theorem about a standard object
Proposed theorem
Theorem — Slender context-free Cobham theorem for weak-Perron linear numeration systems
Let U=(Un​)n≥0​ and V=(Vn​)n≥0​ be strictly increasing sequences of positive integers such that
U0​=V0​=1,nsup​Un​Un+1​​<∞,nsup​Vn​Vn+1​​<∞.
Assume that each sequence satisfies an integral linear recurrence from some index onward.
Let PU​∈Q[X] be the monic polynomial of least degree such that
PU​(E)Un​=0
for all sufficiently large n, where E is the forward shift. Define PV​ analogously. Assume that


PU​ is the minimal polynomial of a weak Perron number α>1;


PV​ is the minimal polynomial of a weak Perron number β>1; and


α and β are multiplicatively independent, meaning that
αr=βsfor all integers r,s≥1.


For n∈N, let repU​(n) and repV​(n) denote the usual most-significant-digit-first greedy representations of n, without leading zeroes.
Let X⊆N. If both languages
{repU​(n):n∈X}and{repV​(n):n∈X}
are slender context-free languages, then X is finite.
Here “slender” has its standard formal-language meaning: there exists C such that the language contains at most C words of each length.
Why this passes the vocabulary test
The statement uses only established notions:


positional greedy numeration;


eventual linear recurrence;


weak Perron number;


multiplicative independence;


context-free language;


slender language.


It does not mention any recurrence witness, synchronized scheme, canonical eventually recurrent system, local-congruence orbit, deleted-prime topology, or representation slice introduced by the manuscript.
More importantly, it does not merely describe the same one-parameter object in classical language. It quantifies over:


one entire set X;


all of its greedy representations in each system;


two multiplicatively independent systems simultaneously.


Why it is not Theorem 2.25 renamed
Theorem 2.25 is a one-system existential classification. It asks whether one greedy language contains some infinite finite-fan-out MCFL with bounded prime support and shows that this is equivalent to an integral positive power of the weak Perron growth parameter. 
The proposed theorem is different in all of its governing quantifiers:
Current Theorem 2.25Proposed theoremone numeration systemtwo numeration systemsexistence of an infinite MCFL sublanguagethe full representation languages of one fixed setbounded prime supportno prime-support conditionconclusion about a power of one growth parameterconclusion that the represented set is finiteone extracted family is enoughinfinitely many common values must be controlled
The theorem belongs externally to the intersection of three established literatures:


Cobham theorems for sets represented in two multiplicatively independent systems; SciSpace+1


the context-free-sequence degeneracy or Cobham-extension problem; IGM+1


the paired-loop classification of slender CFLs and the common-value theory of linear recurrences. 科学直通车+1


I did not locate this exact weak-Perron/slender-CFL statement in the sources checked. That is not a proof of novelty: the thin and slender language literature has a long history, and a dedicated priority search through paired-loop numeration results would still be required before claiming the theorem as new.
IV. Feasibility
1. Exact manuscript inputs
A. Affine block action — Lemma 2.6
For each digit ε,
Dε​=(10​εe1T​C​),
and concatenation is represented by multiplication of these matrices. 
For the proposed theorem, the determinant and finite-group invertibility are not the main point. What matters is that a word family
uvnwxny
has a value expressible as a fixed linear functional of a product containing the two powers Mvn​ and Mxn​.
B. Kronecker/Cayley–Hamilton lift
The proof of Theorem 2.16 forms a tensor product of the powered block matrices and expresses the value sequence as a fixed linear functional of its n-th power. Consequently the values satisfy an integer linear recurrence. 
For one paired loop there are two repeated blocks, so the same construction gives an order bound
R≤(d+1)2,
where d is the order of the least eventual recurrence for the place-value sequence.
C. Greedy length interval
A greedy word of length m represents a value in
[Um−1​,Um​).
This supplies a two-sided growth bound depending only on word length. 
For a paired loop, the length is
L+Dn,D=∣v∣+∣x∣>0,
so its value sequence is squeezed between UL+Dn−1​ and UL+Dn​.
D. Weak-Perron residue asymptotics
After choosing h such that ρ=αh is Perron, the manuscript proves
Uhn+r​=Cr​ρn+O(θn),Cr​>0,0<θ<ρ,
for every residue class rmodh.  The Fourier–Vandermonde argument and strict increase establish positivity of every Cr​. 
This is precisely the step whose underlying quotient-limit mechanism must be credited to Charlier–Kreczman. arXiv
E. Root squeeze
The manuscript already uses the greedy interval and the global root limit to compare a value growing as bt with a word whose length grows as L+Dt, obtaining b=βD. 
The proposed theorem needs a related but stronger statement: not merely the exponential growth rate of the paired-loop value sequence, but the existence—after restricting the parameter to residue classes—of a unique dominating characteristic root equal to a positive power of α.
2. Shortest plausible proof route
Step 1: Decompose both languages globally
By the standard slender-CFL theorem, write
{repU​(n):n∈X}=FU​∪i=1⋃r​{ui​vin​wi​xin​yi​:n≥0},
and similarly
{repV​(n):n∈X}=FV​∪j=1⋃s​{aj​bjm​cj​djm​ej​:m≥0},
where FU​,FV​ are finite and any infinite paired-loop component has positive pumped length. This is a global equality, not a pumping extraction. 科学直通车+1
Step 2: Turn every paired loop into a linear recurrence
For each U-loop define
Ai​(n)=valU​(ui​vin​wi​xin​yi​).
Reverse the words if necessary to use the manuscript’s LSD-first matrices. Lemma 2.6 and the two-block Kronecker product show that Ai​(n) is an integer linear recurrence sequence. Define Bj​(m) analogously for the V-loops.
No pumping lemma is used here.
Step 3: Prove the paired-loop dominant-root lemma
Let
Di​=∣vi​∣+∣xi​∣>0.
The greedy interval gives
ULi​+Di​n−1​≤Ai​(n)<ULi​+Di​n​.
Choose hU​ such that αhU​ is Perron, and restrict n to each residue class modulo hU​. The residue asymptotics imply
Ai​(r+hU​t)≍αDi​hU​t.
The block-matrix description shows that every characteristic root of this subsequence is a product of powers of conjugates of α, together with possible factors 1. Every root having maximal modulus therefore has quotient a root of unity with every other maximal-modulus root; after the hU​-restriction those peripheral roots coalesce to
αDi​hU​.
The two-sided greedy bound rules out a positive-degree polynomial factor multiplying that root: a term such as teαDi​hU​t, e>0, would contradict the uniform comparison with the neighboring place values. Positivity rules out cancellation of the remaining constant coefficient.
Thus each nonzero residue subsequence has the unique dominating root
αDi​hU​.
Do the same for the V-loops, obtaining dominating roots
βEj​hV​.
This is the principal new lemma.
Step 4: Pigeonhole an infinite common-value pair
If X were infinite, the two finite paired-loop decompositions would imply that some Ai​-loop and some Bj​-loop have infinitely many common represented values. Splitting both parameter sets into their finitely many residue classes preserves infinitude for at least one residue-class pair. Hence there would be infinitely many pairs (t,z) such that
Ai​(r+hU​t)=Bj​(q+hV​z).
Step 5: Apply Mignotte’s common-value theorem
The two recurrences in Step 4 have unique dominating roots
αDi​hU​andβEj​hV​.
These remain multiplicatively independent: an equality between positive powers of them would give a positive-power equality between α and β.
Mignotte’s theorem therefore says that the two recurrences have only finitely many common values. 数学出版 This contradicts Step 4 and proves that X is finite.
3. Precise missing ingredient
The missing ingredient is not a stronger pumping lemma.
It is the combination of:


the already known global paired-loop decomposition of a slender CFL;


a new dominant-root transfer lemma for the numerical values of a canonical paired loop in a weak-Perron linear numeration system; and


simultaneous use of the fact that both full languages represent the same set, allowing an infinite common-value problem for two recurrence sequences.


The new technical statement that must actually be proved is approximately:

Let U be a strictly increasing greedy linear numeration sequence whose least eventual recurrence polynomial is the minimal polynomial of a weak Perron number α. If every word uvnwxny is a valid greedy representation and ∣v∣+∣x∣>0, then, after restricting n to finitely many residue classes, the represented-value recurrence has the unique dominating root αh(∣v∣+∣x∣) for a suitable h.

The manuscript proves the growth squeeze needed for this, but not the full characteristic-root assertion.
4. Extension of the present proof or different project?
This is a different research project built from two central pieces of the present machinery, rather than a routine extension of the prime-support proof.
It would reuse:


the affine block action;


the Kronecker/Cayley–Hamilton recurrence construction;


the weak-Perron residue asymptotics;


the greedy length interval.


It would not materially use:


finite-group return times;


deleted-prime adic topology;


Evertse’s fixed-support quotient theorem;


the geometric-subsequence rigidity lemma;


the divisibility-tree construction.


The proof architecture changes from
one MCFL orbit⟶congruence returns⟶prime-support rigidity
to
global finite paired-loop cover⟶finitely many LRS⟶common-value finiteness.
That difference is precisely why the result would count as a theorem about a standard field object rather than an additional theorem inside the paper’s bespoke orbit package.
5. Success probability
70%.
The two genuinely global external inputs—the paired-loop classification and Mignotte’s common-value theorem—already exist and fit the intended proof closely. The main risk is the dominant-root transfer lemma: peripheral eigenvalue collisions, possible Jordan factors, and cancellation must be audited at the level of the actual affine block matrices, not inferred solely from the root-growth squeeze. A second risk is priority: although I did not locate the exact theorem, thin/slender language results are old enough that a dedicated literature search is indispensable.
V. Why broader targets are not realistically reachable
General context-free Cobham theorem
A statement such as

If one set has context-free representation languages in two multiplicatively independent bases, then it is ultimately periodic,

is not reachable from the present mechanism. General context-free languages have no finite paired-loop cover. Ogden’s lemma supplies a decomposition for each sufficiently long word, but the decomposition varies with the word; weak MCFL pumping supplies one fixed family but does not cover the language.
No step currently forces the two systems to extract families containing even one common value, let alone infinitely many.
General MCFL Cobham theorem
This is farther away. Strong pumping fails for MCFLs, and the substitution lemma’s switchable-tuple alternative does not preserve a fixed product of affine matrix powers. The manuscript’s own comparison of these tools is mathematically accurate. 
A general MCFL result would require a new theorem of roughly this strength:

Every infinite MCFL representation language contains finitely many explicitly controlled recurrence families whose values cover an arithmetically substantial part of the represented set.

Nothing in current MCFL structure theory cited by the manuscript gives that conclusion.
Abstract numeration systems
There is also no plausible direct extension to abstract numeration systems. Their representation map is genealogical rank, not a positional sum. Even if the representation language is regular, shortening or pumping a word changes its rank through global language-growth counts rather than through a fixed companion matrix. The central affine action disappears.
Primitive divisors or quantitative S-parts
The fixed-support rigidity argument cannot simply be strengthened into a primitive-divisor or quantitative S-part theorem. Evertse’s input is used contrapositively to exclude two characteristic roots after the entire extracted subsequence has fixed prime support. It gives no control on which prime first appears in an individual term, its exponent, or the size of the supported part of a general term.
VI. Residual objection after the proposed theorem
The strongest remaining objection would be:

The theorem escapes the one-orbit limitation only by imposing slenderness, a class for which an external theorem already reduces the entire language to finitely many one-parameter paired loops. It therefore does not advance the general context-free or MCFL Cobham-extension problem, and most of the manuscript’s prime-support machinery is irrelevant to its proof.

That objection is technically defensible. The proposed theorem would be a genuine two-system result, but it would not establish a global principle for arbitrary context-free languages. It selects precisely the subclass in which global one-parameterization is already available.
There are three forms of evidence that would answer the objection.


Sharpness evidence: construct, in two independent standard numeration systems, an infinite set whose representation languages lie just beyond slenderness—say poly-slender or bounded context-free—and show that the proposed conclusion fails. That would establish slenderness as a natural boundary rather than an expedient restriction.


A poly-slender extension: prove the analogous finiteness theorem for bounded or poly-slender context-free languages by combining the Dyck-loop decomposition with a multivariate S-unit or exponential-polynomial intersection theorem. This would show that the method is not confined to one parameter.


A genuine global language theorem: obtain a substitution or decomposition result for a wider class of CFLs or MCFLs that produces finitely many recurrence-controlled families covering all sufficiently long representations. That would directly address the manuscript’s current quantifier obstruction.


Until one of those is available, the correct positioning would be:


a substantive theorem at the intersection of slender formal languages, linear numeration, and common values of recurrences;


a restricted Cobham-type result;


not a solution of the context-free-sequence degeneracy problem;


not a general Cobham theorem for context-free languages or MCFLs.


The Charlier–Kreczman priority issue would remain resolved by attribution. After the proposed theorem, the principal residual weakness would no longer be the residue-growth priority; it would be the narrow global-language hypothesis and the fact that the theorem relies on slenderness to replace the absent all-words control.
