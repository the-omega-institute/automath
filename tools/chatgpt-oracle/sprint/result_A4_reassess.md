Overall judgment
The theorem is proved in the intended form, and Lemma 3.1 closes the three technical risks that made the project uncertain. I do not see a proof-breaking defect in the new section.
I regard the theorem as defensibly new, but not yet adequately positioned against the nearest regular/sparse Cobham literature. That is now the main weakness.
The addition materially improves the paper: it gives the manuscript a clean theorem about a standard field object that can be cited independently of the prime-support machinery. It does not, in my judgment, move the paper to a higher journal tier. Monatshefte für Mathematik remains the right venue.
My present confidence is approximately:


correctness of Theorem 3.2 and Lemma 3.1: 0.92;


defensible novelty after the literature-positioning repairs below: 0.80–0.85;


justification for abandoning Monatshefte for a stronger venue: low.


The right description is therefore: a real mathematical upgrade within the same venue level, not a tier change.
1. Proof and the dominant-root transfer lemma
The architecture is exactly the one previously proposed. Section 3 discards the one-orbit MCFL pumping mechanism, covers each entire slender context-free representation language by finitely many paired loops, turns each loop image into finitely many recurrence sequences, and then applies common-value finiteness. 
Peripheral collisions
The block calculation is sound. For a block b of length ℓ, the stationary affine action has the form
Mb​=(10​qb​Cℓ​).
Because the minimal polynomial is irreducible in characteristic zero, C is diagonalizable. Consequently Cℓ remains diagonalizable even when two distinct conjugates acquire the same ℓ-th power: the original eigenbasis still diagonalizes the power.
For a nonempty block, every peripheral eigenvalue of Cℓ has modulus αℓ>1, so it is separated from the affine eigenvalue 1. The off-diagonal affine row can therefore change eigenvectors but cannot create a Jordan block at a peripheral eigenvalue. This is the correct way to deal with the collision issue; a growth-rate squeeze alone would not have been enough. 
Jordan factors after vectorization
For the two pumped blocks the actual matrix being powered is
K=MvT​⊗Mx​,
up to the stated one-factor interpretation when one block is empty. This follows from the standard vectorization identity for Mxn​AMvn​.
Its spectral radius is α∣v∣+∣x∣. A product eigenvalue can be peripheral only when each nonempty factor contributes a peripheral eigenvalue. Since those peripheral primary spaces are semisimple, their tensor products are semisimple as well. Choosing the weak-Perron period h makes every peripheral conjugate satisfy γh=αh, so all peripheral eigenvalues of Kh coalesce to
Λ=αh(∣v∣+∣x∣)
on a semisimple eigenspace. Thus coalescence under powering does not create a polynomial factor in t. This closes the second named risk. 
One wording change would improve precision. Equation (10) is not obtained from Cayley–Hamilton alone. Cayley–Hamilton gives the scalar recurrence; the displayed exponential-polynomial expansion, including the absence of a polynomial multiplying Λt, comes from the Jordan or primary decomposition of Kh. I would write:

“Cayley–Hamilton first gives a scalar recurrence. The primary decomposition of Kh, together with semisimplicity at Λ, then gives…”

That is an expository correction, not a change in the argument.
Cancellation
The cancellation argument is also correct. The greedy length interval puts the loop value between two adjacent place values whose indices are affine functions of t. The earlier residue-class asymptotics give positive leading coefficients in every relevant residue class. Hence
0<t→∞liminf​ΛtZr​(t)​≤t→∞limsup​ΛtZr​(t)​<∞.
All lower-modulus Jordan terms are o(Λt). Therefore the spectral-projection coefficient of the actual value functional at Λ cannot vanish; indeed it is positive. This is enough to prove that Λ, rather than merely some root of that modulus in the matrix recurrence, survives as the unique dominant root of the least scalar recurrence. 
That closes the third risk without silently assuming positivity of a matrix eigenvector or absence of cancellation.
Application of Mignotte
The theorem proof then works. After splitting each paired loop into finitely many residue subsequences and discarding finitely many initial terms, one obtains finite families of integer linear recurrence sequences with unique dominant roots that are positive powers of α or β. Multiplicative independence survives passage to positive powers, and an infinite X forces an infinite common-value set for one pair of sequences. 
The manuscript’s version of the Mignotte input matches an accessible published restatement by Bennett and Pintér: integral recurrence sequences with unique dominant roots strictly larger than one have only finitely many common values unless the dominant roots are multiplicatively dependent, with the constant-leading-coefficient case exactly suited to the present application. 个人数学网站
I would nevertheless make three small bridges explicit:


Say that each “eventual” recurrence is shifted so that Mignotte is applied to an ordinary recurrence indexed from 0.


Add the omitted finite initial loop values to a finite exceptional set before invoking the pigeonhole argument.


State that an infinite intersection of the two finite unions of sequence images supplies infinitely many equality pairs for one selected pair.


None of these exposes a real gap; they prevent a referee from manufacturing one out of compressed prose.
2. Priority
Is the exact theorem defensibly new?
Yes, with a significant qualification.
The classical slender-CFL input is correctly represented. Ilie–Rozenberg–Salomaa explicitly recall that slender context-free languages are finite unions of paired loops
{uvnwxny:n≥0},
with the result traced to Latteux–Thierrin and Ilie. Numdam Mignotte supplies common-value finiteness once one has the required dominant-root structure. Neither of these inputs by itself states the two-numeration theorem.
A slender-language specialist may say that once Lemma 3.1 is available, the proof of Theorem 3.2 is natural and short. That is fair. But the specialist cannot simply cite the paired-loop classification and be done: paired loops are word-theoretic objects, whereas Mignotte requires numerical image sequences with unique dominant roots and constant dominant coefficients. In weak-Perron systems, peripheral phases, collisions under powering, affine Jordan structure, and cancellation are precisely the obstacles between those statements. Lemma 3.1 supplies the missing bridge.
So my classification would be:

a new and useful synthesis with one genuine transfer lemma, rather than a new Cobham theory or a disguised previously published theorem.

That is enough for defensible novelty at Monatshefte level.
The priority paragraph is nevertheless incomplete
Remark 3.3 says that the search covered the relevant areas and that failure to locate the statement is not a priority claim. That is honest, but a list of searched areas is not a substitute for comparing the theorem with the closest actual results. 
At least three neighboring results should be named.
First, in ordinary independent integer bases, the regular sparse case is already known. Albayrak and Bell prove that the intersection of a sparse k-automatic set and a sparse ℓ-automatic set is finite, with an effective bound, when k and ℓ are multiplicatively independent. Taking the two sets equal gives a simultaneous sparse-automatic finiteness theorem. arxiv.org A slender regular representation language is sparse, so this contains the regular integer-base shadow of Theorem 3.2.
Second, Durand’s Cobham theorem for substitutions says that a sequence simultaneously substitutive with respect to two multiplicatively independent Perron eigenvalues is ultimately periodic. EMS Press
Third, Charlier–Leroy–Rigo prove a Cobham theorem for independent abstract numeration systems under finite-automaton recognizability, obtaining finite unions of arithmetic progressions. ORBilu
None of these subsumes Theorem 3.2:


they use regular or substitutive recognition, whereas the present full representation languages may be genuinely nonregular slender CFLs;


the abstract-numeration representation map is genealogical rank, not the positional affine value map used here;


the present weak-Perron systems need not provide the regular canonical interface needed for the standard recognizability theorems;


the new theorem concludes finiteness but does not claim the quantitative bounds available in the sparse automatic case.


But those distinctions need to be made in the manuscript, not left implicit. The appropriate novelty claim is therefore:

The regular integer-base and regular abstract-numeration shadows belong to existing Cobham theory. The new part is the passage from regular recognition to full slender context-free representation languages, together with the dominant-root transfer for paired loops in weak-Perron positional systems.

With that paragraph added, I would regard the novelty claim as defensible. Without it, a knowledgeable referee could reasonably say that the literature audit is not yet complete, even though the exact theorem is probably new.
The inaccessible original Mignotte article is no longer a serious mathematical concern because its needed formulation can be checked in Bennett–Pintér. The clean solution is to cite both Mignotte and Bennett–Pintér’s explicit restatement rather than explain the network-access problem in the article itself. 个人数学网站
3. Venue
Nothing changes: keep the paper at Monatshefte für Mathematik.
The new theorem improves the paper in three ways:


it gives a concise field-recognizable endpoint;


it demonstrates that the affine recurrence machinery has use beyond the paper’s internally developed prime-support objects;


it makes the manuscript easier to remember and cite.


But it does not justify moving upward because Section 3 remains a short synthesis of two classical global inputs plus one technical transfer lemma. It does not establish a poly-slender theorem, a quantitative intersection bound, a general context-free Cobham theorem, an effective construction, or a classification of simultaneous context-free recognizability. The manuscript itself correctly emphasizes that this is a different global argument rather than a strengthening of the main MCFL pumping chain. 
Monatshefte publishes research of general interest across mathematics, and the combination of formal languages, recurrence sequences, numeration, arithmetic, and topology is compatible with that broad remit. Springer Link+1
Were this a fresh submission, Theoretical Computer Science would be the obvious alternative because the slender-language theorem and both major external inputs are squarely in automata and formal-language theory. Its stated scope is mathematical and abstract theoretical computer science. 科学直通车+1 But that would be a lateral fit decision, not an upgrade, and the entire article—not only Section 3—arguably fits Monatshefte’s broad mathematical profile better.
I would not withdraw a paper already at minor revision in order to pursue that lateral alternative. The addition should instead be disclosed as a substantive new section and allowed to undergo whatever additional review the editor considers necessary.
The paper’s standing is now:

stronger and more distinctive at Monatshefte, but still a Monatshefte paper.

4. The strongest likely referee objection
The strongest objection is no longer technical. It is:

“The new result is called a Cobham theorem, but the manuscript does not compare it statement-by-statement with the existing sparse automatic, Perron-substitutive, and abstract-numeration Cobham theorems. Its regular integer-base subcase is already known. Why is the context-free theorem more than a routine repackaging?”

That objection is answerable, but the current Remark 3.3 does not yet answer it. The response must identify Lemma 3.1 as the nonregular weak-Perron bridge and specify exactly which hypotheses of the older theorems fail for a slender but nonregular context-free representation language.
The next objection would be proof presentation:

“The transition from the matrix spectrum to the least scalar recurrence is compressed, and finite initial exceptions are suppressed in the application of Mignotte.”

The repairs described above should dispose of that objection in a few sentences.
After those are fixed, the strongest remaining editorial objection is unity. Section 3 openly announces that it has a different architecture from the rest of the paper.  I do not think it should be split—the affine digit action and weak-Perron residue asymptotics are substantial shared machinery—but the title and introduction should now acknowledge the second theorem. At present:


the title does not mention Cobham or slender languages;


the keywords omit both;


the organization paragraph jumps from Section 2 to Section 4 and does not describe the newly inserted Section 3. 


A title such as

Prime support, multiple-context-free languages, and a slender Cobham theorem in recurrent numeration

would make the new balance visible rather than leaving the strongest externally recognizable theorem buried near the end.
Final verdict
I would not retract the earlier target: the theorem has been built successfully. The dominant-root lemma does the difficult work it was supposed to do, rather than hiding the peripheral problems behind a growth squeeze. The resulting theorem is a genuine contribution and not merely another result in the manuscript’s private vocabulary.
I would recommend acceptance after a further focused revision, principally to:


add the missing Cobham-prior-art comparisons;


cite an accessible exact formulation of Mignotte;


expand the spectral-to-scalar and eventual-recurrence bridges by several sentences;


repair the title, keywords, and organization paragraph.


The addition raises the paper’s mathematical value appreciably, but Monatshefte remains the correct level.
