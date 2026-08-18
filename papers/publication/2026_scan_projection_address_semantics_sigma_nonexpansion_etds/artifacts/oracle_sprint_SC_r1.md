Recommendation: reject in present form; withdraw and rebuild
The central mathematics appears essentially correct, but the paper does not presently have a result commensurate with 21 pages. I also found one definite, though noncentral, false assertion in Theorem 5.7.
(1) What is the one result?
There is no specialist-level “one result”: Theorem 6.1 expresses the Bayes error as uTBHm−1​bm−1modq​, an identity engineered by defining br​ to be the terminal-state conditional Bayes ambiguity, and its escape-rate conclusion follows by bounding those terminal weights above and below and invoking the standard Perron–Frobenius asymptotic for survivor mass.
That is the honest sentence.
The proof makes the issue unusually clear. After a safe prefix, the Markov property says that the conditional probability depends only on the terminal state and the current residue phase; the corresponding minimum is precisely the previously defined βi,r​. Summing the cylinder masses therefore gives the displayed matrix formula. The lower nondegeneracy assumption was chosen to make every βi,r​ uniformly positive, after which comparison with survivor mass is immediate.   This is correct bookkeeping, but it is not a substantive new theorem about open dynamics.
The paper itself accurately concedes that the escape formula, Perron–Frobenius asymptotics, and Chen–Stein input are standard, while presenting the observable and its ambiguity amplitude as the novelty.  A new choice of observable is not by itself enough when its principal theorem is obtained by writing down its conditional expectation.
Several other statements fall into precisely the categories you warned about:


Lemma 6.3 is a definitional consequence. Its “more general” sufficient condition is the residue nondegeneracy condition itself, repeated verbatim in terms of the same intersections; the proof merely expands the definition of pi,r​. Its first assertion, Di​=Z/qZ⇒ nondegeneracy, is immediate. 


Corollary 6.9 is only an algebraic rearrangement. The manuscript says so explicitly. 


Theorem 6.10 is the standard Perron–Frobenius ratio limit/quasistationary-distribution calculation applied to two terminal weights of the same killed matrix. Finite-state quasistationarity in this form goes back at least to Darroch–Seneta. 剑桥大学出版社


Corollary 6.11 is the standard finite product automaton. Once the phase is adjoined, the lifted matrix is Sq​⊗BH​; rationality and the cyclotomic spectrum follow from the geometric series and the Kronecker-product spectrum. The manuscript’s proof is exactly that calculation. 


Corollary 7.1 is a standard Rényi-entropy-rate spectral-radius formula for a finite Markov source, here applied to the conditioned survivor law. Perron–Frobenius formulas for Rényi rates of finite-alphabet Markov sources substantially predate this paper. IEEE Xplore


Theorem 7.2 is the strongest result in the manuscript, but it is still not enough to carry the present paper. Its proof consists of precise power-sum asymptotics, a strict ℓp-type spectral inequality, and the standard dependency-graph Chen–Stein bound. The manuscript itself calls Section 7 a collection of “secondary consequences” using a standard Chen–Stein estimate.  Generalized birthday Poisson laws and the required dependency-graph approximation are classical. 科学直通车+1 The pressure parametrization and explicit Perron prefactor make this a clean application, not a new limit-theorem mechanism.
So the answer is not “Theorem 6.1.” The answer is: several small finite-state calculations, with Theorem 7.2 the best of them, but no single result currently worth a specialist’s sustained attention.
(2) Quantifier audit
A. The surrounding advertisements are stronger than the body statements
Abstract: escape exponent, amplitude, and genuine pole
The abstract assumes a mixing one-step SFT, a one-step equilibrium Markov measure, and a Markov hole with mixing survivor, and then states the path sum, survivor-mass asymptotics, escape-rate recovery, ambiguity amplitudes, and the genuine dominant pole. It does not state:


q≥2;


∅=R⊊Z/qZ;


most importantly, the condition that for every i∈S and every r∈Z/qZ, attainable first-hit times occur in both R−r and its complement. 


The body theorem explicitly imposes that all-state, all-phase condition before asserting the sandwich, exponent, and pressure identity. 
Verdict: the exact path-sum formula itself is not overstated—it does not actually use nondegeneracy. Formally, however, the advertised escape, amplitude, and pole claims are stated under fewer hypotheses than Theorems 6.1, 6.10, and Corollary 6.11.
The omissions of q and proper R are minor and largely implicit in “residue event.” The omission of residue nondegeneracy is real.
Introduction, “Problem” paragraph
The introduction says without qualification that the resulting Bayes-error sequence recovers the escape exponent, a residue-dependent quasistationary amplitude, and a resolvent coefficient.  The subsequent “Setting” paragraph specifies the hole and proper residue subset but still does not impose residue nondegeneracy. 
Verdict: formally stronger than the body theorem for the same reason.
“Main results,” items (i)–(iii)
Items (i), (ii), and (iii) advertise, under the preceding setting alone:


the exact formula and escape-rate decay;


the quasistationary amplitude;


the genuine dominant pole.


The missing hypothesis is again the all-i, all-r residue nondegeneracy condition. 
Verdict: all three summaries suppress a stated theorem hypothesis. The exact identity survives the suppression, but the written theorem does not claim the subsequent conclusions without it.
The “Context and comparison” and “Relation to recent work” paragraphs repeat the same unconditional presentation. 
Abstract and “Main results,” collision claim
The abstract advertises “sharp Poisson collision thresholds of every fixed multiplicity, with no additional overlap hypothesis,” and item (iv) similarly advertises the collision thresholds without listing the conditions.  
Theorem 7.2 requires:


all the hypotheses inherited from Corollary 7.1 and hence, formally, Theorem 6.1;


card(S∞​)≥2;


independent survivor prefixes with common law λmH​;


a fixed integer k≥2;


a triangular-array scaling for Nm​, either critical, subcritical, or supercritical. 


Verdict: the omitted card(S∞​)≥2 and independence assumptions are substantive. The manuscript itself contains a one-state mixing survivor example, so the cardinality condition is not automatic.  “Every fixed multiplicity” correctly means each fixed k, rather than a result uniform in growing k, so there is no problem on that clause.
The phrase “no additional overlap hypothesis” is defensible only after the independent-sampling and two-state-or-more assumptions have been supplied.
Survivor Rényi claim
Corollary 7.1 formally says “assume the hypotheses of Theorem 6.1,” thereby importing q, R, and residue nondegeneracy into a statement that does not involve any of them.  The abstract and introductory summary omit those inherited hypotheses.
Verdict: formally, the advertisement is stronger. Substantively, the proof establishes the stronger advertised statement: the residue assumptions are never used in Corollary 7.1. The right repair is to delete the irrelevant inherited hypotheses from Corollary 7.1, not to burden the abstract with them. This is evidence that the Rényi/collision material has been attached to the Bayes-error theorem rather than developed from a clean independent statement.
B. The numbered front-matter statements themselves
Here the manuscript is much better than its prose.


Theorem 1.1 versus Theorem 6.1: faithful. The front theorem explicitly states the all-i, all-r nondegeneracy condition and the same quantifiers and conclusions. 


Theorem 1.2 versus Theorem 6.10: faithful. Both give one limit for each residue subsequence nq+r+1, not a single residue-independent full-sequence constant. 


Remark 1.3: faithful to the finite-state quasistationary interpretation; it introduces no broader quantifier.


Corollary 1.4 versus Corollary 6.11: faithful. It claims pole containment, not detection of the entire spectrum, and singles out only the genuine positive Perron pole. 


Corollary 1.5 versus Corollary 7.1 and Theorem 7.2: faithful. Unlike the abstract and bullet summary, the numbered corollary explicitly includes card(S∞​)≥2, fixed k, independent samples, and the critical scaling. 


Bottom line of the quantifier audit: I found no mismatch between the five numbered front-matter statements and their body versions. Every mismatch is in the abstract or unnumbered introductory advertisement surrounding them.
C. The all-state/all-phase condition is imposed at the wrong level
There is a sharper point than mere omission from the abstract.
For every i∈S∞​, the condition Di​=Z/qZ is already forced by the stated mixing assumptions:


The survivor graph on S∞​ is primitive. 


From a survivor state, ambient mixing and the nonempty hole give an admissible path to the hole; truncate at its first hole symbol so that all preceding states are safe.


Primitivity lets one spend any sufficiently large number of steps inside S∞​ before taking that exit path.


Hence first-hit lengths from i contain every sufficiently large integer up to a fixed shift, and therefore every residue modulo q.


Thus only the transient states T=S∖S∞​ can violate the manuscript’s condition. But the escape exponent, leading amplitude, and genuine Perron pole are governed by the Perron component S∞​, not by positivity of the terminal ambiguity at every transient state and every phase.
The manuscript’s counterexample to nondegeneracy does not answer this point: its safe survivor graph is periodic, and the paper explicitly says it is outside Theorem 6.1. 
The clean theorem should therefore be split as follows:


the exact matrix formula holds for every proper R, with no nondegeneracy condition;


under the existing mixing assumptions, the escape exponent, residue-subsequence amplitude, and genuine Perron pole follow without the all-state condition;


the stronger all-S, all-phase condition is needed only for the finite-depth uniform sandwich
θνϕ​(τH​≥m)≤εm​≤21​νϕ​(τH​≥m)
as stated for every m.


So this is not a fatal vacuity. It is an overengineered hypothesis placed on every intermediate state when only positivity on the dominant survivor component matters.
D. One correctness defect outside the central theorem
The parenthetical assertion in Theorem 5.7 is false as written.
The prefix metric is dpre​(ξ,η)=2−ℓ(ξ,η).  Therefore, if the boundary has upper box dimension δ, its cylinder count is controlled on the scale
Nm​(∂P)≲2(δ+o(1))m,
not
λcyl(δ+o(1))m​
unless λcyl​=2. Moreover, upper box dimension gives a limsup bound, not generally the exact asymptotic equality asserted in the hypothesis. The theorem currently says the latter occurs “for example” whenever the upper box dimension is d. 
The correct general consequence is
m→∞limsup​m1​logεm​≤−logλcyl​+δlog2.
The elementary first inequality in Theorem 5.7 is fine; the box-dimension specialization is not.
I found no comparable correctness failure in Theorems 6.1, 6.10, 6.11, or 7.2.
(3) Venue and odds
Present version
Do not submit this 21-page version. Withdraw it.
At a dynamics journal, the likely report is exactly: correct finite-state calculations, but the escape-rate content is standard, the Bayes observable does not create a substantial theorem, the resolvent statement is routine, and the only meaningful probabilistic result is presented as a secondary corollary.
Rebuilt version
The strongest journal where acceptance becomes genuinely plausible is Stochastics and Dynamics, at roughly 20%, after a genuine rebuild. As submitted, I would put the probability below 5%. The journal’s stated scope—stochastic phenomena analyzed from a dynamical-systems viewpoint—is a close match to the intended finite-state probability/dynamics interface. World Scientific
I would rebuild around Theorem 7.2, at 11–13 pages, not around Theorem 6.1:


state the collision theorem as the main theorem;


isolate a general triangular-array criterion in terms of precise Rényi power-sum asymptotics and strict Rényi gaps;


give the conditioned Markov-survivor law as the principal application;


include an explicit total-variation error bound rather than merely convergence;


remove most of Sections 3–5, Corollary 6.9, most examples, and the cyclotomic-resolvent section.


Mere cutting is not enough. To make the rebuilt theorem worth publishing, it should go beyond the primitive finite-state case—most naturally to Gibbs/Hölder survivor laws for cylinder holes, periodic survivor components, or a joint/multitype collision process. Otherwise it remains an elegant verification of a standard Chen–Stein scheme.
I am not naming Discrete and Continuous Dynamical Systems as the next venue up because that journal expressly seeks important new methods and results and maintains a high innovation threshold. 美国数学科学研究院 This paper introduces no new dynamical method, and its principal open-system exponent is recovered by a terminally weighted version of the usual survivor path sum.
A second, more ambitious route would be to make the proposed Hölder/open-transfer-operator extension into an actual theorem rather than future work. The manuscript presently lists the spectral-gap, forward/backward-spectrum, and regularity steps as unproved.  A successful version of that result, combined with the collision theorem, could justify an 18–22 page dynamics paper. Without either that extension or a substantial strengthening of Theorem 7.2, the project should stop at withdrawal rather than proceed through cosmetic revision.
