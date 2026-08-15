Verdict
The correction is right. I find no convention mismatch, mistranscription, or hidden endpoint convention that restores Dushistova’s printed coefficient. The published proof drops the restriction u>1 when defining the canonical convolution Σ2​; because the empty left context is then included in Σ2​ and the whole convolution is doubled, that endpoint is counted twice rather than once. The resulting excess is exactly Rs​. The correct leading coefficient is
2Rs2​,Rs​=ζ(s)ζ(s−1)​,
not Rs​+2Rs2​.
This is not an error introduced by the English translation: the same split and the same coefficient occur in the Russian original. 数学网+2数学网+2
Proposition 6.4 is also genuinely term-by-term exact. With two minor but important presentational changes described below, I would regard the correction claim as safe to publish.
1. Lemma 6.5: the endpoint correction
Dushistova defines An​ as the canonical positive regular continued-fraction words
(a1​,…,at​),ai​≥1,at​≥2,a1​+⋯+at​=n,
uses the regular continuant as denominator, sets the empty continuant equal to 1, and defines
σβ​(n)=a∈An​∑​K(a)−2β.
Her Theorem 3 then prints the leading coefficient
R+2R2,R=ζ(2β)ζ(2β−1)​.
These conventions and the printed coefficient are explicit in the published paper. 数学网
Let
rm​=v canonical∣v∣1​=m​∑​K(v)−s,ℓm​=u arbitrary positive∣u∣1​=m​∑​K(u)−s.
The manuscript correctly establishes
r0​=ℓ0​=1,r1​=0,ℓ1​=1,ℓm​=2rm​(m>1).
The last identity is exact: every canonical word ending in a≥2 has precisely the two positive representations
(…,a)and(…,a−1,1),
with the same continuant and digit sum. Conversely, every noncanonical positive word ending in 1, except the isolated word (1), is obtained uniquely in this way. The two exceptions are therefore exactly digit sums 0 and 1. 
The cleanest way to expose the published error is at finite cutoff w, before taking any limit. Extend r0​=1 and r1​=0, and put
Aw​:=v≤w∑​rv​.
The original left-context sum has three disjoint cases:
R0​(w)=u=0v≤w∑​rv​​​+u=1v≤w−1∑​rv​​​+u>12u+v≤wu>1​∑​ru​rv​​​.(*)
Dushistova defines
Σ1​(w)=v≤w−1∑​rv​,Σ2​(w)=u+v≤w∑​ru​rv​.
Her text says that, after separating u=1, the u>1 sum is replaced by 2Σ2​, and it consequently writes
R0​=Σ1​+2Σ2​.
But the displayed Σ2​ has no u>1 restriction. It includes u=0; u=1 contributes nothing because r1​=0. This is exactly what appears in both versions of the paper. 数学网+2数学网+2
Consequently,
Σ2​(w)=Aw​+u+v≤wu>1​∑​ru​rv​,
and the exact corrected identity is
R0​(w)=Σ1​(w)+2Σ2​(w)−Aw​.​(**)
The omitted subtraction Aw​ is the entire discrepancy. Letting w→∞,
Aw​⟶Rs​,Σ1​(w)⟶Rs​,Σ2​(w)⟶Rs2​,
so
R0​=Rs​+2Rs2​−Rs​=2Rs2​.
Equivalently, by the manuscript’s three-class calculation,
Rs​+Rs​+2(Rs​−1)Rs​=2Rs2​.
Thus:
Dushistova’s printed Rs​+2Rs2​ is genuinely wrong.​
There is no normalization escape. The empty word, the canonical terminal-digit condition, the denominator, and the exponent are the same. 
As an independent numerical check, for s=6,
2Rs2​=2.077744488…,Rs​+2Rs2​=3.096995313….
Direct exact enumeration gives
n6σ3​(n)=2.13336, 2.12681, 2.12163, 2.11743
at n=22,24,26,28, respectively. This is already close to and moving toward 2Rs2​, while remaining nearly one full unit away from the printed coefficient. The computation is not the proof, but it is a useful adversarial check.
One wording change is strongly advisable
The abstract currently calls this an “endpoint loss.” Since the published coefficient is too large, that wording is liable to confuse a referee. What was lost was the restriction u>1, producing an endpoint overcount.
I recommend replacing “endpoint loss” by something like:

“an endpoint overcount caused by dropping the restriction u>1 in the canonical convolution.”

I would also add the exact finite-cutoff identity (∗∗) to Lemma 6.5. It makes the correction virtually impossible to dispute and is stronger evidentially than comparing only limiting constants.
2. Proposition 6.4 is term-by-term exact
Dushistova’s indexing object is exactly the canonical regular continued fraction
[0;a1​,…,at​],ai​≥1,at​≥2,∣a∣1​=n,
with denominator K(a1​,…,at​) and weight K(a)−2β. 数学网
The manuscript’s b2d+1​(s) is indexed by the same reduced fractions p/q∈(0,1), now represented by their unique negative continued fractions with all digits at least 2. The regular-to-negative conversion preserves the represented reduced fraction and hence preserves its denominator. It also gives
d(p/q)=a1​+⋯+at​−1.
Therefore
c(p/q)=2d(p/q)+1=2d+1
if and only if
a1​+⋯+at​=d+1.
Finally,
q−s=K(a)−s=K(a)−2βwhens=2β.
This proves, term by term,
b2d+1​(s)=σs/2​(d+1).
The manuscript states and proves precisely these correspondences. 
Every possible convention issue checks out:
FeatureDushistovab2d+1​(s)VerdictIndexing setReduced fractions via canonical regular wordsSame reduced fractions via negative wordsExact bijectionTerminal ruleat​≥2Unique negative expansion, digits ≥2CompatibleDigit-sum index(a_1=n)DenominatorRegular continuant K(a)=qNegative continuant D=qSame reduced denominatorExponentK−2βq−ss=2βEmpty wordNot in σβ​(n), n≥2Not in b2d+1​, d≥1No mismatchEmpty contextContinuant 1Continuant 1Same endpoint convention
The first two layers make the shift especially transparent:
b3​(s)=2−s=σs/2​(2),
and
b5​(s)=2⋅3−s=σs/2​(3),
corresponding respectively to the regular words (2), and (3),(1,2).
I also enumerated both representations through d=7: at every level the regular and negative descriptions produce exactly the same set of reduced fractions and the same denominators. Again, this is only a finite check, but it detects none of the likely indexing or terminal-digit failures.
3. Localization and scope
The manuscript’s substantive localization is correct, but one sentence should be made more exact.
The first false step is indeed in Lemma 7, where the condition u>1 disappears in the displayed definition of Σ2​. That wrong C0​ is then inherited by Lemma 8, Lemma 9, Lemma 10, and the leading term of Theorem 3. The published paper itself says that Lemma 9 supplies the leading term of Theorem 3 and is also used in its complete proof. 数学网+1
Thus the most precise scope statement is:

The bookkeeping error originates in Lemma 7 and changes the explicit constant C0​, hence the occurrences of C0​ in Lemmas 8–10 and the leading coefficient of Theorem 3.

That is slightly broader than saying only “Theorem 3 contains an error,” although it is the same underlying error.
I do not see a forced error in the lower coefficients Ck′​ of Theorem 3. Those coefficients are introduced through separate unrestricted context sums; the erroneous canonical replacement is used to evaluate C0​. Nevertheless, this audit has not independently reconstructed every lower coefficient, so the manuscript is right not to certify or correct them.
Theorem 2 requires a more nuanced statement. Dushistova says that the leading auxiliary asymptotic from Theorem 3 is used in its proof, so the corrected C0​ must formally be substituted in the intermediate arguments. But Theorem 2 does not print C0​ as its leading coefficient: its leading term is the different n−β term, and its lower coefficients are left as unspecified positive constants. The correction does not contradict that theorem’s displayed form, and the estimates that use C0​ remain valid with the corrected positive finite value. 数学网+1
I would therefore replace language of the form

“the correction concerns the leading coefficient of Theorem 3, not the other results of the paper”

by the more defensible formulation

“We correct the explicit constant C0​ in Lemma 7 and consequently the leading coefficient in Theorem 3. We do not reassess the remaining coefficients or the other theorems of the paper.”

That states exactly what has been proved without implicitly vouching for every other calculation.
4. The reframed novelty claim
The new contribution boundary is accurate and appropriately narrow.
The manuscript now acknowledges that:


Dushistova already studied the identical fixed-digit-sum continuant sum;


its polynomial order is not new;


her result provides a fuller claimed expansion;


the present contribution is the exact reconciliation, correction of the leading coefficient, an independent and shorter proof of that corrected leading term, and the downstream critical renewal/Fibonacci consequences. 


That is the correct priority description.
The “simplified proof” claim is justified. The proof of Theorem 6.3 does not merely modify one line of Dushistova’s argument. It reconstructs the leading asymptotic through:


a unique large partial quotient;


an absolutely convergent left–right context sum;


a separate two-large-digit estimate;


a greedy bound for the all-moderate regime.


This independently proves that the entire leading term is 2Rs2​d−s, rather than merely diagnosing why the published coefficient looks suspicious. 
The downstream consequences are also genuinely different in kind from Dushistova’s local expansion. At criticality Rσ0​​=2, so the corrected coefficient is
bC​=2Rσ0​2​=8,
and the manuscript transfers it to the exact cost-tail constant, the m3−σ0​ renewal corrections, and the spectrally positive stable domain of attraction. 
Accordingly, the manuscript should continue to avoid formulations such as “we obtain a new fixed-digit-sum asymptotic.” The accurate formulation is:

corrected leading coefficient and independent leading-term proof, followed by new critical renewal/Fibonacci consequences.

The current introduction and contribution boundary now substantially follow that formulation. 
5. Priority and venue
Priority
My previous priority objection lifts.
The earlier objection was that the manuscript was presenting as new a local continuant asymptotic already treated by Dushistova. That is no longer what the paper claims. It now:


identifies the two sums exactly;


locates a genuine printed error;


supplies a self-contained proof of the corrected coefficient;


uses that corrected arithmetic input to obtain further renewal and Fibonacci-partition results.


This is a legitimate correction-and-extension theorem, not a rediscovery with an added citation.
I am sufficiently confident in the endpoint calculation that I would not recommend withdrawing the correction. On the contrary, retaining Dushistova’s coefficient would now be the mathematically incorrect choice.
Transactions of the American Mathematical Society
Submission to Transactions is defensible and not mis-targeted, but it remains ambitious rather than safe.
The correction by itself would probably not carry a long Transactions paper. The case for that venue is the combined package:


correction of an explicit theorem-level constant in the literature;


an independent arithmetic proof;


exact critical renewal constants;


noninteger finite-size corrections;


the stable-law consequence;


the one-layer and finite-window large-deviation results;


the exact finite correspondences that tie the different parts together.


That package has enough mathematical substance for a serious Transactions submission. The main editorial risk is no longer priority or the correctness of the correction. It is whether an editor regards the paper as one coherent central advance or as a long aggregation of transfers, normalizations, and consequences around several imported theories.
My recommendation is therefore:
Submit to Transactions after strengthening the correction paragraph.​
I would make two changes first:


replace “endpoint loss” by “loss of the restriction u>1, causing an endpoint overcount”;


display the exact finite identity
R0​(w)=Σ1​(w)+2Σ2​(w)−v≤w∑​σβ​(v).


Those changes turn the most serious claim in the paper from a persuasive reconstruction into an immediately checkable algebraic correction.
Should Transactions decline on breadth or significance, rather than correctness, Journal of Number Theory or Ergodic Theory and Dynamical Systems would be natural alternatives. But I would not preemptively move the manuscript down solely because it corrects prior literature. The correction is real, the reconciliation is exact, and the new downstream theorem is the part that makes the higher submission credible.