# Reproducing the finite computations

This directory contains the computational evidence for the article and its
supplement. All integer arithmetic is exact. The stored run records Python
3.10.11, SymPy 1.13.1, and SymPy's `factorint` routine. Factorization cost is
not part of a theorem or complexity claim.

## Submission checks

The reproducibility reports cover only claims retained in the submission:

- direct and structural constructions of `B_n` and `M_n` through `n = 60`;
- exact-rank prime counts and weighted rank-pure products through `n = 210`;
- the squarefree-sector equality and the strict ladder example at `n = 91`;
- the exact criterion for whether the entire minimal fiber is squarefree;
- labelled minimal-cover counts and the fixed-total-weight comparison;
- the finite lower and upper support bounds involving `R(n)`;
- the table values through `n = 30`.

The general theorems are proved in the article. These computations check
finite instances and the supplied factorization archive; they do not replace
any proof or establish distributional control of `R(n)`.

## Files

- `compute_birth_layer_table.py` generates the table for `2 <= n <= 30`.
- `verify_finite_claims.py` runs the main direct/structural comparison and
  the retained rank-pure and support-bound checks.
- `test_verify_finite_claims.py` contains unit tests for its arithmetic
  routines and report contract.
- `../scripts/verify_deepening_delta.py` independently checks the upper-fiber,
  witness, and support-bound computations.
- `../scripts/test_verify_deepening_delta.py` tests that independent route.
- `../scripts/verify_squarefree_slice.py` independently enumerates weighted
  covers and squarefree minimal generators, and compares the squarefree-fiber
  criterion with direct enumeration.
- `../scripts/test_verify_squarefree_slice.py` tests the squarefree equality
  and the sharp fixed-total-weight bound, including a deliberately mutated
  criterion that the verifier must reject.
- `fibonacci_factorizations_2_210.tsv` stores the exact factorizations used.
- `birth_layer_table_output.txt`, `finite_verification.txt`,
  `deepening_delta_verification.txt`, and
  `squarefree_slice_verification.txt` are deterministic stored reports.
- `SHA256SUMS` authenticates the reproducibility sources, archive, reports,
  documentation, and line-ending policy.

The comprehensive verifier retains internal arithmetic regression routines
that supported theorem blocks separated from this submission. They are not
reported as submission claims and are retained rather than deleted because
the artifacts are historical evidence. The separate `named_problem_audit.md`
has the same archival status and is not part of the reproduction manifest.

## Commands

Run from the manuscript directory:

```powershell
python -m unittest discover -s artifacts -p "test_verify_finite_claims.py"
Push-Location scripts; python -m unittest test_verify_squarefree_slice.py test_verify_deepening_delta.py; Pop-Location
python artifacts\compute_birth_layer_table.py
python artifacts\verify_finite_claims.py --exhaustive-max 60 --scalable-max 210 --output artifacts\finite_verification.txt --factorizations-output artifacts\fibonacci_factorizations_2_210.tsv
python scripts\verify_deepening_delta.py --exhaustive-max 60 --scalable-max 210 --output artifacts\deepening_delta_verification.txt --factorizations-output artifacts\fibonacci_factorizations_2_210.tsv
python scripts\verify_squarefree_slice.py --max-index 210 --output artifacts\squarefree_slice_verification.txt
```

The first two verification routes compare the actual sets, not only their
cardinalities. On `2 <= n <= 60`, the expected report lines are:

```text
B_n direct = B_n upper fiber: 59/59 set equalities
M_n direct = M_n witness: 59/59 set equalities
```

For `61 <= n <= 210`, the structural route checks the support bounds and the
rank-pure products. Every layer in this range has at most four prime
coordinates. The squarefree verifier independently enumerates all
irredundant covers for `1 <= k <= 4`, checks the fixed-total-weight bound, and
compares rank-pure products with squarefree minimal generators for every
squarefree `3 <= n <= 210`. It also compares the squarefree-fiber criterion
with direct enumeration on all 208 indices `3 <= n <= 210`.

## Checksums

Paths in `SHA256SUMS` are relative to the `artifacts` directory. Verify them
from the manuscript directory with:

```sh
cd artifacts && sha256sum -c SHA256SUMS
```

The manifest and every covered file use LF line endings. The project-local
`.gitattributes` pins these files to LF, and each verifier writes LF output.
