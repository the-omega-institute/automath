Bottom line
Theorem 5.2 is correct, and the proposed length-2m−2 family really does collide. The conjugacy result in Section 5 now has a valid proof.
But the revision is not ready to resubmit for two separate reasons:


The claimed exact inverse memory m−1 is wrong. The exact zero-anticipation memory is 2, independently of m.


More seriously, the old one-rewrite-versus-cascade mistake still survives in Lemma 4.4 and Appendix B. Theorem 5.2 is repaired, but Section 4 is not presently proved.


1. The new separation theorem
The theorem states that Wm,L​ is injective for L≥2m−1, with a collision at 2m−2. 
The congruence criterion is valid
For a length-m binary word,
N≤k=1∑m​Fk+1​=Fm+3​−2=Fm+2​+Fm+1​−2.
Writing M=Fm+2​, this is less than 2M, so a normalized expansion can have at most one digit outside the window, namely the digit of weight M at position m+1.
If that digit occurs, the remaining value is at most Fm+1​−2<Fm+1​. It therefore cannot use position m, so it is compatible with the high digit and is exactly the Zeckendorf expansion of N−M. Consequently
Foldm​(w)=Z(N(w)modM),
within the visible window. Thus equality of folds is exactly congruence of values modulo M, as claimed. 
There is no missing case here.
The boundary identity is correct
Let
Si​=k=1∑m​di+k−1​Fk+1​.
In Si​−Si+1​−Si+2​, the coefficients are:
digitdi​di+1​di+r​, 2≤r≤m−1di+m​di+m+1​​coefficientF2​=1,F3​−F2​=1,Fr+2​−Fr+1​−Fr​=0,−Fm+1​−Fm​=−Fm+2​=−M,−Fm+1​.​​
Therefore
Si​−Si+1​−Si+2​=di​+di+1​−Mdi+m​−Fm+1​di+m+1​,
exactly as displayed in (5.2). 
There is no dropped boundary coefficient.
The “remainder vanishes” step is valid for m≥4
Because each Si​ is divisible by M, reduction of (5.2) gives
xi​:=di​+di+1​−Fm+1​di+m+1​≡0(modM).
Now
∣xi​∣≤2+Fm+1​<Fm+1​+Fm​=M
because Fm​>2 for m≥4. Hence xi​=0, not merely xi​≡0.
Since Fm+1​>2, the equality
di​+di+1​=Fm+1​di+m+1​
cannot hold with di+m+1​=±1. Thus
di+m+1​=0,di+1​=−di​.
This correctly kills dm+2​,…,d2m−1​ and makes d1​,…,dm−1​ alternate.
The last window is then
Sm​=dm​+2dm+1​.
It is divisible by M, while ∣Sm​∣≤3<M, so it is zero. The only solution to
dm​+2dm+1​=0,dm​,dm+1​∈{−1,0,1},
is dm​=dm+1​=0.
Finally,
S1​=d1​j=1∑m−1​(−1)j−1Fj+1​=d1​(−1)m−2Fm−1​.
This is divisible by M=Fm+2​ and has magnitude below M, so d1​=0. The alternating relations then give d=0. 
That part of the proof is airtight.
The m=3 case is complete
Here M=5, and the bound becomes non-strict:
2+F4​=5=M,
so the separate treatment is genuinely necessary.
The congruence is
d1​+d2​−3d5​≡0(mod5).
There are exactly three cases:


If d5​=0, then d1​+d2​=0. The last window gives d3​+2d4​=0, whose only allowed solution is d3​=d4​=0. The first window is then −d1​, hence d1​=d2​=0.


If d5​=1, then d1​+d2​−3∈[−5,−1] is divisible by 5, so it equals −5. Thus d1​=d2​=−1. The first window is
−1−2+3d3​=−3+3d3​,
and divisibility by 5 forces d3​=1. But then the last window is
1+2d4​+3=4+2d4​∈{2,4,6},
never divisible by 5.


The case d5​=−1 is exactly the negation of the preceding case.


Those cases exhaust d5​∈{−1,0,1}. The argument is complete. 
Reduction to L=2m−1
This is legitimate, although the manuscript could spell it out more explicitly.
If u,v∈{0,1}L, L>2m−1, have the same folded-window sequence and differ at coordinate j, choose any contiguous length-2m−1 interval containing j. The two restricted blocks still differ, and their m folded windows form a contiguous subsequence of the common global label sequence. They would therefore contradict injectivity at length 2m−1.
So there is no boundary oversight in that reduction.
Verdict on Question 1: Theorem 5.2 is correct.
2. The sharpness family
Yes, it collides.
Let um+1​=1, let vm−1​=vm​=1, and set every other coordinate to zero in blocks of length 2m−2. 
In the first window, the u-word has value 0, while the v-word has value
Fm​+Fm+1​=Fm+2​=M.
Their values are congruent modulo M, so their folds agree—in fact both visible folds are zero.
For a later window beginning at i≥2, all three exceptional coordinates lie inside the window. Their relative weights are three consecutive Fibonacci numbers, so the value difference is
Fm−i+3​−Fm−i+2​−Fm−i+1​=0.
Thus every later pair of raw window values is exactly equal, not merely congruent.
Verdict on Question 2: the family is valid and proves sharpness at 2m−2.
The claimed exact decoder memory is nevertheless wrong
The manuscript constructs a decoder from m consecutive labels and then says that the dependence on m is essential.  That conclusion does not follow from the sharp full-block ambiguity.
The distinction is:


m labels are necessary to recover the entire length-2m−1 lift uniquely.


They are not necessary to recover the single current digit required by the inverse sliding block code.


In fact, three consecutive labels always determine the current digit.
Take two length-m+2 lifts of the same three consecutive labels and write their difference as d. Equation (5.2), used only for i=1, gives
d1​+d2​−Fm+1​dm+2​≡0(modM).
For m≥4, its absolute value is at most Fm+1​+2<M, so it is zero. Since Fm+1​>2, this forces
dm+2​=0.
Thus the last digit of the lift is uniquely determined by the three labels, even though the rest of the lift need not be unique.
For m=3, the manuscript’s separate analysis already shows that three labels—corresponding to a length-five block—determine the entire lift.
Therefore there is a decoder
ψ​m​:B3​(Ym​)⟶{0,1},ηt​=ψ​m​(yt−2​,yt−1​,yt​)
for every m≥3.
Two labels do not suffice. Use the same Fibonacci-recurrence family, but truncate it to length m+1:
um+1​=1,vm−1​=vm​=1.
Its two folded windows agree, while its terminal digits are 1 and 0.
Hence the exact causal coding parameters are:
memory 2,anticipation 0​
for every m≥3.
So:


Theorem 5.3 is true as an upper-bound construction.


Theorem 5.5 is true.


“Exact memory m−1” is false for every m≥4.


Remark 5.4’s assertion that the decoder’s dependence on m is essential is false.


The sharp 2m−1 theorem is a sharp whole-block reconstruction theorem, not a sharp local-decoder theorem.


This also means the separation theorem is not actually needed to obtain the optimal local conjugacy: a three-label tail-separation lemma suffices.
A more serious surviving problem: the cascade error is still present
The manuscript defines a span-r local normalizer by requiring that later rewrites can intersect a processed prefix only in its final r−1 positions. Lemma 4.4 claims that Zeckendorf normalization satisfies this for r=3, merely because each individual rewrite has support three. 
That is the same one-step-versus-cascade mistake as before.
In most-significant-digit-first order, take the stable prefix 010 and append 11. Including the mandatory leading zero,
001011⟶001100⟶010000.
The first rewrite touches only the end of the prefix, but it creates a new 011 farther to the left. The second rewrite changes the first coordinate of the original prefix 010, which lies outside its final two coordinates.
The propagation is unbounded: prefixes of the form
(01)k0
followed by 11 generate a carry cascade all the way to the first symbol.
Appendix B repeats the false assertion that once a pair symbol has been emitted, later lower-weight digits cannot alter it.  There is a literal counterexample to Lemma B.2:


00000101 is already normalized. After four initial 00 pair symbols, the next raw block is 0101, and the next four pair symbols are
00∣11∣00∣11.


000001011 normalizes visibly to 000010000. It has the same four initial 00 pair symbols and the same next raw block 0101, but its next four pair symbols are
01∣10∣00∣10.


So those pair symbols do depend on the following lower-weight digit.
Corollary 4.6 explicitly derives the four-state presentation from Lemma 4.4 and Theorem 4.5.  That derivation fails. The four-state graph may still be correct, but it needs an actual carry-state or transducer proof. At present, the graph presentation—and therefore all downstream finite-state statistics that rely on it—is not established by the manuscript.
This alone is enough to risk another correctness rejection.
3. Significance and ETDS
No. The significance verdict stands. Do not resubmit this to ETDS.
The sharp separation theorem is a genuine result. It is not a routine enumeration, and it materially improves the paper. It changes my assessment from “the central conjugacy assertion is unsupported” to “Section 5 contains a correct and worthwhile system-specific theorem.”
It does not change the journal level.
The paper remains an extensive analysis of one explicit Fibonacci normalizer. Once the pair graph is supplied, the discrepancy laws, rotation polygon, covariance formulas, transfer matrix, large deviations, and thermodynamic statements are mostly finite-state consequences—the manuscript itself presents several of them that way.   The new arithmetic theorem is elegant but short, elementary, and confined to this one recurrence and this one coding map.
ETDS describes itself as a forum for major contributions and central problems in dynamical systems and its interactions with other fields. 剑桥大学出版社 This paper, even fully corrected, does not reach that threshold. It gives exact invariants and coding bounds for a well-chosen example; it does not establish a general phenomenon across a substantial class of numeration systems, sofic codes, or normalization transducers.
The correction from alleged memory m−1 to exact causal memory 2 makes the result cleaner, but it does not broaden it. Indeed, it partly weakens the manuscript’s current narrative: the long block-separation threshold and the local conjugacy radius are different questions, and the conjugacy has a much shorter proof than the paper claims.
Dynamical Systems remains the right-sized target, provided the paper is substantially repaired and cut. Its remit includes theoretical dynamical systems, and it has published specialized work on symbolic conjugacy and subshifts. 泰尔与方在线+1
My plain submission advice is:
Do not send this version to ETDS. First replace the decoder-memory claim by the exact memory-2 statement, separate whole-block reconstruction from local decoding, and reprove the four-state presentation without the false bounded-cascade argument. After that, the previous recommendation—Dynamical Systems, after substantial cutting—still stands.
