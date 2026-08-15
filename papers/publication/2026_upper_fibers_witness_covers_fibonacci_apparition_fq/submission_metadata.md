# Submission Metadata

## Journal

- Target journal: The Fibonacci Quarterly
- Submission status: Resubmission following a reject-and-resubmit decision
- Submission components: main article, supplementary material, cover letter,
  and reproducibility materials

## Manuscript

- Title: Minimal preimages of the Fibonacci rank map: squarefree fibers and
  weighted covers
- Main article: `main.pdf` (33 pages)
- Supplement: `supplement.pdf` (36 pages)
- Supplement title: Supplementary material for Weighted witness covers and
  exact-rank multiplicities in Fibonacci apparition fibers
- 2020 Mathematics Subject Classification: 11B39, 11A07, 11A25

## Authors

1. Haobo Ma
   - Affiliation: AELF PTE LTD., #14-02, Marina Bay Financial Centre Tower 1,
     8 Marina Blvd, Singapore 018981, Singapore
   - Email: auric@aelf.io
2. Wenlin Zhang
   - Affiliation: National University of Singapore, Singapore
   - Email: e1327962@u.nus.edu
   - Corresponding author: yes

## Referee-Facing Submitted Files

1. `main.pdf`: 33-page primary manuscript.
2. `supplement.pdf`: 36-page supplementary material containing connected
   factorizations, support classifications, secondary consequences, finite
   checks, and reproducibility commentary.
3. `cover_letter.txt`: resubmission cover letter.
4. `submission_metadata.md`: this submission manifest.
5. Verification scripts:
   `artifacts/compute_birth_layer_table.py`,
   `artifacts/verify_finite_claims.py`,
   `scripts/verify_deepening_delta.py`, and
   `scripts/verify_squarefree_slice.py`.
6. Unit tests:
   `artifacts/test_verify_finite_claims.py`,
   `scripts/test_verify_deepening_delta.py`, and
   `scripts/test_verify_squarefree_slice.py`.
7. Archived verification outputs and data:
   `artifacts/birth_layer_table_output.txt`,
   `artifacts/finite_verification.txt`,
   `artifacts/deepening_delta_verification.txt`,
   `artifacts/squarefree_slice_verification.txt`,
   `artifacts/fibonacci_factorizations_2_210.tsv`, and
   `artifacts/tab_birth_layer_data.tex`.
8. Literature and named-problem audits:
   `artifacts/literature_check.md` and
   `artifacts/named_problem_audit.md`.
9. Reproduction and integrity files:
   `artifacts/REPRODUCE.md`, `artifacts/SHA256SUMS`, and `.gitattributes`.

## Claims And Priority Boundary

The claimed new contribution is the lowered-label Fibonacci realization of
the witness-cover structure, its unique correspondence with the
divisibility-minimal exact fiber, the canonical squarefree slice, and its
exact arithmetic weights. The article also gives prime inverse rays and uses
them to answer the two FitzGibbons-Javaheri-Miller-Verga problems in the
stronger prime form.

The classical minimal-cover skeleton is imported: Wagner's minimal
multiplicative covers give the prime-atom case, and Hearne-Wagner minimal set
covers give its set-theoretic predecessor. Classical exact-rank prime
existence supplies every prime used in the inverse-ray application, so no new
prime-existence theorem is claimed. The fixed-point classification and orbit
termination used there are also imported, from Marques and Luca-Tron,
respectively. The article records other classical rank, lifting, primitive
divisor, and fibotomic inputs at their points of use.

## Resubmission Record

The article now contains numbered statements for classical prime-power rank
lifting, the prime-ladder alternative, and the ladder-slot formulas used by
the upper bounds. It also contains a numbered proposition delimiting Wagner's
classical condition from the lowered-label generalization. H1 and H2 are
identified only as sufficient maximum-window hypotheses; Corollary 6.9 is
purely conditional, no positive arithmetic evidence for either hypothesis is
claimed, and the Bugeaud-Luca-Mignotte-Siksek conjecture is recorded as
predicting that both fail.
