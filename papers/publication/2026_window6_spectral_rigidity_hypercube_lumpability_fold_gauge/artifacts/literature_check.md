# Priority and citation check — window6, 2026-08-19

Run against Crossref while the codex channel was down. This manuscript had never had a
priority check, which matters now that it is the strongest paper in the sprint.

## First query: control FAILED, no conclusion drawn

`equitable partition hypercube lumpable Markov chain automorphism Zeckendorf fold colour
refinement` returned Markov partitions of toral automorphisms, healthcare appointment
scheduling, OFDMA channel prediction and partition diamonds. Noise from four unrelated fields
means the query never reached the intended literature, so its silence is not evidence. This is
the same failure mode recorded in the zeck_arith check and it is recorded here rather than
quietly dropped.

## Second query: control PASSED

`equitable partitions of the hypercube perfect codes automorphism group binary Hamming graph`
returned Solov'eva on partitions into perfect codes (three papers), Avgustinovich-Solov'eva on
perfect binary codes with trivial automorphism group, Vasil'eva on local distributions for
eigenfunctions and **perfect colorings of q-ary Hamming graphs**, and Dejter-Phelps. That is
the correct field: perfect colorings of the Hamming graph are precisely equitable partitions of
the hypercube, the general theory in which this manuscript's fold-induced partition sits.

## Priority: no collision

Every construction in those results is code-theoretic - perfect codes, Hamming codes, coverings.
None is induced by a numeration-system fold, and none classifies the equitable partitions
arising from a Zeckendorf prefix map. The sporadic classification at m in {3, 6, 8, 9} is not
anticipated by anything the query surfaced.

## Two problems that are not about priority

**The vocabulary is one-sided.** The manuscript says "equitable partition" in four files but
never "perfect coloring" or "perfect colouring", the name this object carries in the Russian
school (Fon-Der-Flaass, Avgustinovich, Vasil'eva, Solov'eva) that has done most of the work on
equitable partitions of the hypercube specifically. A referee drawn from that community will
search for the term, not find it, and conclude the field was not read.

**The bibliography has five entries.** For a paper asserting a complete classification, five
references is on its own something a referee will remark on, independently of which ones are
missing.

## Action when the codex channel returns

1. Adopt "perfect colouring" as an explicit synonym where the equitable partition is defined,
   and cite the Hamming-graph literature - Vasil'eva (Des. Codes Cryptogr. 87, 2018,
   doi 10.1007/s10623-018-0559-1) is a reasonable entry point, and Fon-Der-Flaass on equitable
   partitions of the hypercube should be located and added.
2. Expand the bibliography generally; five entries will draw comment by itself.
3. Neither item is a priority threat. Both are the same class of defect as the missing Fenwick
   citation in zeck_arith: a small field whose referee pool will notice its own names missing.

---

# Scope audit, 2026-08-19: the title and abstract still describe the rejected paper

This is not a literature finding, but it belongs with the other pre-submission checks and
there is no separate audit file for this paper.

The referee desk-rejected this manuscript for treating one fixed partition of one 64-vertex
graph and asked for an infinite family. The body was subsequently extended: the introduction
now defines Fold_m and the involutions sigma_{i,j}^{(m)} for general m, and
Proposition (Characterisation of involution-admissible dimensions) determines the
involution-admissible dimensions to be exactly {3, 6, 8, 9}, importing the Bugeaud-Cipu-
Mignotte binary-digit theorem. The sentence "The six-dimensional partition belongs to a
sparse dimension-dependent phenomenon" is in the introduction.

The title and the abstract were not updated.

  Title:    "The Unique Minimal Equitable Refinement of a Folded Partition of the 6-Cube"
  Abstract: the six-dimensional hypercube, the 21-cell partition, the 48-cell refinement
            with 32 singletons and 16 pairs, the quotient spectrum with multiplicities
            (1,5,11,14,11,5,1), and the discarded 16-dimensional sector carrying Q_4.

The abstract does not mention general m, the classification, the sporadic set, or the word
family anywhere. An editor who reads only the title and abstract - which is how a desk
decision is made - sees precisely the single-example paper that was already rejected, with no
indication that the objection has been answered.

This is the highest-value editorial defect currently known in this manuscript, and it is
independent of the remaining mathematics. The classification stands on its own: it does not
depend on the unproved D-chain interlacing lemma, because the involution-admissible dimensions
are pinned by the arithmetic of Fibonacci numbers with two binary digits, which is imported and
effective. So the abstract can be rewritten now, without waiting for the two-star lemma.

## Action when the codex channel returns, in priority order

1. Retitle so the classification is the subject rather than the 6-cube.
2. Rewrite the abstract to lead with the classification at m in {3, 6, 8, 9} and the closed
   form 3 * 2^{m-2} for the cell count, keeping the six-dimensional spectral results as the
   worked case rather than the whole content.
3. State plainly in the abstract what is and is not proved: the classification of
   involution-admissible dimensions is complete, while the stronger statement that every
   fibre of the coloured-star signature has at most two elements is verified for
   6 <= m <= 5000 and holds for all sufficiently large m with an ineffective cutoff.
4. Note that the cover letter, if it still frames the paper as the 6-cube study, needs the
   same treatment.

---

# Reproducibility audit, 2026-08-19

The abstract claims "All finite data needed to recompute the claims are supplied in the
accompanying supplement", and section "Final remarks and reproducibility" names six scripts.
Claims of this kind are worth testing rather than trusting, since a named script that no longer
runs is worse than no script at all.

All six were executed. Every one exits 0:

    supplement/verify_window6_streams.py      all assertions passed
    artifacts/verify_hidden_refinement.py     all assertions passed
    artifacts/verify_refinement_family.py     m with a nontrivial refinement: [3, 6, 8, 9]
    artifacts/verify_involution_mechanism.py  16 candidates, F_12=144, F_9=34, F_5=5
    artifacts/verify_admissible_dimensions.py streams candidates through m=22
    artifacts/verify_preservation_criterion.py 49 candidates tested, 0 disagreements

So the reproducibility claim is sound and this is not a submission risk. Two remarks.

First, the prose is honest in the right places: it says the finite checks "corroborate, but do
not replace, either the criterion or the cited Diophantine classification", and separately that
they "do not replace the proofs of the interval lemma or the spectral-carrier argument". That
is the correct register and needs no change.

Second, verify_refinement_family.py independently outputs [3, 6, 8, 9]. That is the paper's own
script, written before any of my auditing, and it confirms from the paper's side the correction
recorded at t442 - where my reconstructed criterion in verify_sporadic_involutions.py used
m <= k-3 and so silently dropped m = 3. The paper was right and its reproducibility apparatus
would have caught my error had I run it earlier.

Note that the roughly nine verification scripts I added to artifacts/ during this sprint are
NOT named in the reproducibility section, and should not be: they audit claims that go beyond
what the manuscript asserts. The paper claims the refinement sweep through m = 16 and the
candidate stream through m = 22; the two-star lemma to m = 5000 and the effective Diophantine
route are mine and are not in the manuscript. If any of that is ever promoted into the paper,
the corresponding scripts must be named here at the same time.
