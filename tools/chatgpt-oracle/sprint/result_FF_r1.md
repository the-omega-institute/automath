I checked the object defined in Appendix B: for a finite raw word ω, compute its full Zeckendorf normalization, retain the visible digits to form RM​(ω), and read the raw/normalized pairs from high weight to low weight. The bi-infinite process is the factor language/local bulk limit of those reversed words—not the terminal digit process of finite windows. 
(i) P has only the four stated state forms
Verdict: verified. The paper has a preserved invariant, not merely an experimentally observed list.
Write the states as
ABCD​:P=0, y−=0,:P=−Fk+1​,:P=−Fk​, y−=0,:P=0, y−=1.​
Here B deliberately suppresses y−. These are exactly the four states listed in Appendix B. 
The clean invariant is obtained as follows. At the cut before Fk​, after reading the current pair (x,y), put
P+=P+(x−y)Fk​.
Let R<k​ and Z<k​ be the values of the still-unread raw and normalized tails, using weights F2​,…,Fk−1​. Equality of the total raw and normalized values gives
P+=Z<k​−R<k​.
The two tails satisfy
0≤R<k​≤j=2∑k−1​Fj​=Fk+1​−2,0≤Z<k​≤Fk​−1,
the second bound being the maximum value of a no-adjacent-ones word below weight Fk​. Therefore every completable scan satisfies
−(Fk+1​−2)≤P+≤Fk​−1.(1)
Using (1), together with the prohibition on adjacent normalized 1s, closes the four states under every actual scan step:
stateABCD​possible transition00→A,01→B,11→D,10→C,10→A,00→B,11→B,00→A.​​
For example:


From A or D, label 10 would give P+=Fk​>Fk​−1, contradicting (1).


From B, every label except 10 leaves P+≤−Fk+1​<−(Fk+1​−2).


From C, label 01 gives P+=−2Fk​, and 2Fk​>Fk+1​−2.


In D, labels with normalized digit 1 are excluded by adjacency.


The recurrence then gives the stated next states; for instance,
−Fk+1​+Fk​=−Fk−1​,
which is state C at the next cut. High-side zero padding supplies the base state A, so induction proves the invariant along every scan. This is substantially what Proposition B.2 does: it uses tail-capacity inequalities to exclude every other label and then closes the displayed states under the recurrence. 
Two qualifications:


Numerically, P is not bounded independently of k; −Fk​ and −Fk+1​ grow. The finite-state assertion is that P has only these three k-relative forms.


The word “exactly” in Proposition B.2 is slightly too literal if applied at the last few low-weight boundary sites. For example, A01​B cannot occur at the cut before F3​, because the remaining raw weight F2​ cannot compensate F3​. The eight edges are exactly the interior transition types, and each is realizable arbitrarily far from the boundary. This does not affect the bulk graph.


(ii) (P,y−) is sufficient
Verdict: verified for the intended interior/bulk follower language. No unbounded hidden carry remains.
The essential arithmetic fact is:

A finite binary pair (x,y) is a genuine raw/full-normalized pair once the two strings have equal Fibonacci value and y has no adjacent 1s.

The second condition makes y the unique Zeckendorf expansion of the first coordinate’s value. Consequently, no information about the rewrite history is needed beyond:


the unresolved value imbalance P, and


the single preceding output bit needed to enforce the no-11 condition.


The merger in state B is also legitimate. Although y− can be either 0 or 1 there, the only possible next label is 10, whose normalized component is 0. After that transition the system is in C, where y−=0 is again known.
A direct follower-set argument is available. Let two valid high-padded scan prefixes end in the same state s, and let q be any finite graph path beginning at s. From the endpoint of q, use strong connectivity to append a path back to A, followed by as many A00​A loops as needed. For either original prefix, the concatenated state path:


starts with imbalance 0;


ends with imbalance 0;


has a normalized coordinate with no adjacent 1s, including across the concatenation point.


Hence the concatenated raw and normalized strings have equal Fibonacci value, and the second is the full Zeckendorf normalization of the first. Thus the same q is a valid continuation after either prefix. Conversely, every actual continuation must follow the transition table by part (i). The two prefixes therefore have identical interior follower languages.
This is precisely the mechanism behind Proposition B.3: close a path to state A on both sides, use zero loops to move it into the interior, and conclude from zero terminal imbalance plus Zeckendorf legality that the path is genuinely normalized. 
The manuscript does not spell out the “attach the same continuation to each prefix” argument in those words, but its proof contains everything needed. I do not see a logical gap.
There is one necessary scope qualification: state alone does not encode the number of sites remaining before the low boundary. Thus, if “future language” meant exact finite-volume completions at a boundary-sensitive cut, one would also retain the remaining length. For the manuscript’s interior reversed shift, this information disappears, and (P,y−) is sufficient.
(iii) Right-resolving, synchronized, and the full interior language
Verdict: verified. Both language inclusions are proved correctly.
Right-resolving
From every state, the outgoing pair labels are distinct:


A: 00,01,11;


B: 10;


C: 00,10,11;


D: 00.


So the graph is right-resolving.
Synchronized
The one-symbol pair word 01 occurs on exactly one edge,
A01​B.
Therefore every path carrying 01 ends in the same state B. It is a synchronizing word. Equivalently, the two-symbol word 0000, whenever readable, ends in A.
The two inclusions
Let Lpair​ be the interior reversed pair language and L(G) the graph path language.


Lpair​⊆L(G).
Append two high-order raw zeros so that the full normalization is visible and the scan begins in A. The invariant and exclusions in Proposition B.2 then force every actual raw/normalized factor to follow the eight graph transitions. High-side padding does not change the original visible normalized digits. 


L(G)⊆Lpair​.
This is the important converse. Given any graph path, connect A to its initial state and its terminal state back to A, then add arbitrarily many 00-loops at A on both sides. Assign consecutive Fibonacci weights. The path starts and ends with imbalance zero, so its raw and normalized coordinates have equal total value; the transition table guarantees that the normalized coordinate has no adjacent 1s. Zeckendorf uniqueness therefore makes it the actual normalization of the raw coordinate. The original path occurs arbitrarily far from both boundaries. 


Thus the graph does not merely contain all real pair factors as a proper sublanguage, nor does it generate spurious bulk factors. The manuscript’s stated equivalence between interior factors and graph paths is correct. 
As an independent nonproof check, I exhaustively enumerated every binary raw word of length M≤18, computed its full Zeckendorf expansion, padded the raw word by two high-order zeros, and scanned the pairs from high weight to low weight. No state or transition outside the eight listed ones occurred, and all eight occurred. I also compared graph path labels of lengths up to 8 with factors of the manuscript’s reversed words RM​(ω) for M≤14; the languages agreed exactly. This computation did not use the last normalized digit of a finite window.
Final verdicts:
(i) verified; (ii) verified in the intended bulk/interior sense; (iii) verified.
