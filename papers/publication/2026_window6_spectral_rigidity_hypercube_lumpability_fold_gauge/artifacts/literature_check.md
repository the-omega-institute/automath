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
arising from a Zeckendorf prefix map. The sporadic classification at m in {6, 8, 9} is not
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
