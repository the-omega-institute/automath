Determination
Zn​(s)∼2(ζ(s)ζ(s−1)​)2n−s​(s>2).
Thus
C=2Rs2​​.
At the arithmetic critical point Rσ0​​=2,
C=8​,
not 10.
The manuscript’s correction is right. Dushistova’s printed coefficient Rs​+2Rs2​ is wrong. I am confident in this determination.
Method: isolate the unique macroscopic digit
Let C be the set of canonical words, including the empty word, and let P be the set of all finite positive words, again including the empty word. Write ∣A∣ for digit sum and set K(∅)=1.
The two total context masses are
R∈C∑​K(R)−s=Rs​
and
L∈P∑​K(L)−s=1+1+2A∈CA=∅​∑​K(A)−s=1+1+2(Rs​−1)=2Rs​.
Here the first 1 is the empty word and the second is the exceptional positive word (1). Every positive word of digit sum greater than 1 is one of the two expansions
(a1​,…,ar​),(a1​,…,ar​−1,1)
of a unique canonical word.
Choose
h=h(n)=nα,2s−2s​<α<1.
Consider first the words in Qn​ having a digit X>n−h. Since h<n/2 eventually, this digit is unique. Every such word has a unique decomposition
(L,X,R),
where L∈P, R∈C, and
X=n−∣L∣−∣R∣.
Conversely, every pair L∈P, R∈C with ∣L∣+∣R∣<h gives such a word for sufficiently large n.
The continuant asymptotic is uniform
Let L− denote L with its last digit removed and let R+ denote R with its first digit removed. The concatenation identity for continuants gives exactly
K(L,X,R)=XK(L)K(R)+K(L−)K(R)+K(L)K(R+).
Consequently,
K(L,X,R)=K(L)K(R)(X+λL​+ρR​),
where
0≤λL​=K(L)K(L−)​≤1,0≤ρR​=K(R)K(R+)​≤1,
with the corresponding ratio set to zero for an empty context.
Put m=∣L∣+∣R∣<h. Then X=n−m, and uniformly over all these contexts,
K(L,X,R)sns​=K(L)sK(R)s1​(n−m+λL​+ρR​n​)s=K(L)sK(R)s1+O(h/n)​.
Hence the large-digit contribution Gn,h​ satisfies
nsGn,h​=(1+O(h/n))L∈P, R∈C∣L∣+∣R∣<h​∑​K(L)sK(R)s1​.
Since the context sums converge absolutely for s>2, letting n→∞, and therefore h→∞, gives
nsGn,h​⟶(L∈P∑​K(L)−s)(R∈C∑​K(R)−s)=(2Rs​)Rs​=2Rs2​.
It remains only to show that words without a digit exceeding n−h contribute o(n−s).
The no-large-digit sector is negligible
Let q=K(a1​,…,at​). Fix
r>s−2s​.
Large denominators
For the Stern–Brocot denominator layer one has the exact partition identity
a∈Qn​∑​(qq−​1​+qq+​1​)=1,
where q−​,q+​≤q are the two neighboring denominators. In particular,
a∈Qn​∑​q−2≤1.
Therefore
a∈Qn​q≥nr​∑​q−s≤n−r(s−2)a∈Qn​∑​q−2≤n−r(s−2)=o(n−s).
This exact denominator identity is also stated in Dushistova’s preliminary lemmas. arXiv
Small denominators and no macroscopic digit
Suppose now that q<nr. Since the all-ones continuant is Fibonacci-sized,
q≥Ft+1​,
so
t≤Cr​logn.
If every digit is at most n−h, choose a largest digit ai​. Then
ai​≥tn​≥Cr​lognh​,
and the remaining digits have total at least h, so some distinct digit aj​ satisfies
aj​≥Cr​lognh​.
Thus the word contains two distinct digits at least
y=Cr​lognh​.
Splitting the word around these two digits as
(U,A,V,B,W),
with U,V arbitrary positive contexts and W canonical, positivity of continuants gives
K(U,A,V,B,W)≥ABK(U)K(V)K(W).
After overcounting all possible choices of the two distinguished digits and dropping the digit-sum constraint,
a∈Qn​q<nrmaxai​≤n−h​∑​K(a)−s​≤(U∈P∑​K(U)−s)2(W∈C∑​K(W)−s)​d≥y∑​d−s​2≪y2−2s≪n−α(2s−2)(logn)2s−2.​
Because α>s/(2s−2), this too is o(n−s).
Combining the two cases proves that the complement of the unique-large-digit sector is o(n−s). Therefore
Zn​(s)=Gn,h​+o(n−s)∼2Rs2​n−s.
Where Dushistova’s extra Rs​ enters
In Dushistova’s notation s=2β. The paper’s Theorem 3 and Lemma 7 print
C0​=ζ(2β)ζ(2β−1)​+2(ζ(2β)ζ(2β−1)​)2=Rs​+2Rs2​.
That is indeed the published coefficient under discussion. arXiv+1
Let
cv​=R∈C∣R∣=v​∑​K(R)−s,c0​=1,c1​=0.
The correct truncated context decomposition is
R0​(h)=u=0v≤h∑​cv​​​+u=1v≤h−1∑​cv​​​+u>12u>1u+v≤h​∑​cu​cv​​​.​
The three pieces are:


u=0: the genuinely empty left context;


u=1: the unique left word (1);


u>1: two positive expansions for each canonical left context.


Their limits are respectively
Rs​,Rs​,2(Rs​−1)Rs​.
Thus
Rs​+Rs​+2(Rs​−1)Rs​=2Rs2​.
Dushistova’s proof says that it separates the u=1 term and replaces the u>1 part by twice a canonical convolution. But the displayed definition of that convolution is summed over all u+v≤h, with no u>1 restriction. It consequently includes u=0, the empty canonical left context. Because the convolution is multiplied by 2, that empty context contributes twice. Meanwhile the genuinely required u=0 endpoint was not separately displayed. The net effect is therefore:
2Rs​−Rs​=Rs​
too much. This is visible directly in the transition from the prose restriction u>1 to the unrestricted displayed definition of Σ2​. arXiv+1
So the manuscript’s diagnosis is essentially exact. The most precise wording is:

The proof omits the separate u=0 endpoint and then reintroduces it inside the doubled canonical convolution, thereby assigning it multiplicity 2 rather than multiplicity 1. The resulting excess is exactly one full right-context mass, namely Rs​.

Therefore the final adjudication is
manuscript correct;Dushistova coefficient too large by Rs​.​
