# Reproducing the finite computations

This directory is the computational supplement for the manuscript. All
integer arithmetic is exact. The verification was run with:

- Python 3.10.11;
- SymPy 1.13.1;
- SymPy's `factorint` integer-factorization routine.

The factorization cost is not part of any theorem or complexity claim. The
archive `fibonacci_factorizations_2_210.tsv` records every exact factorization
of `F_n` used for `2 <= n <= 210`; the verifier checks that every row
multiplies back to the stated Fibonacci number.

## Files

- `compute_birth_layer_table.py`: exhaustive divisor/rank enumeration for
  `2 <= n <= 30` and generation of the TeX table.
- `verify_finite_claims.py`: independent direct and structural computations,
  finite-bound checks, exact minimal-cover and connected-cover enumeration,
  theta-normalized and discrete local-limit checks, rank-pure sector checks,
  exact total and connected support-spectrum checks and the extremal
  atomic-product count,
  rank-window deaggregation and squarefree pigeonhole checks, complete
  weighted rank-pure product membership and the strict ladder example at
  `n=91`, refined
  private-coordinate upper bounds, fibotomic rank-entropy and exact-rank
  radical checks, the finite Jarden consequence, exact-rank prime existence
  through rank 210, a prime inverse-ray prefix, the exceptional path to the
  fixed point 12, environment reporting, and
  factorization-archive generation and validation.
- `test_verify_finite_claims.py`: unit tests for the arithmetic routines,
  finite bounds, archive round trip, and report contents.
- `../scripts/verify_deepening_delta.py`: independent legacy verification
  battery for the finite upper-fiber and growth-law checks.
- `../scripts/test_verify_deepening_delta.py`: unit tests for the independent
  legacy verification battery.
- `deepening_delta_verification.txt`: complete deterministic report from the
  independent legacy verification battery.
- `../scripts/verify_squarefree_slice.py`: independent enumeration of
  weighted minimal covers and rank-pure prime products for the canonical
  squarefree exact-fiber slice.
- `../scripts/test_verify_squarefree_slice.py`: unit tests for the sharp
  fixed-total-weight bound, its unique equality profile for `k >= 3` and
  nonuniqueness at `k = 2`, support incidence, and the squarefree-slice set
  equality.
- `squarefree_slice_verification.txt`: complete report for the new sharpness
  and squarefree-fiber checks.
- `named_problem_audit.md`: primary-source quotations, current-status checks,
  and exact mappings from five printed open problems to the manuscript.
- `fibonacci_factorizations_2_210.tsv`: exact factorization input/archive.
- `tab_birth_layer_data.tex`: generated table included in the manuscript.
- `birth_layer_table_output.txt`: complete stdout from table generation.
- `finite_verification.txt`: complete stdout report from the verification run.
- `../.gitattributes`: LF line-ending policy for the reproducibility files.
- `SHA256SUMS`: SHA-256 digest of the LF-stable reproducibility sources,
  archives, reports, documentation, and line-ending policy named in the
  manifest. The generated TeX table is represented by its generator and
  deterministic text transcript rather than hashed directly.

## Commands

Run these commands from the manuscript directory:

```powershell
python -m unittest discover -s artifacts -p "test_verify_finite_claims.py" -v
Push-Location scripts; python -m unittest -v test_verify_squarefree_slice.py; Pop-Location
python artifacts\compute_birth_layer_table.py
python artifacts\verify_finite_claims.py --exhaustive-max 60 --scalable-max 210 --output artifacts\finite_verification.txt --factorizations-output artifacts\fibonacci_factorizations_2_210.tsv
python scripts\verify_deepening_delta.py --exhaustive-max 60 --scalable-max 210 --output artifacts\deepening_delta_verification.txt --factorizations-output artifacts\fibonacci_factorizations_2_210.tsv
python scripts\verify_squarefree_slice.py --max-index 210 --output artifacts\squarefree_slice_verification.txt
```

The first verification route enumerates every divisor of `F_n`, computes its
rank directly, and minimizes the resulting birth layer. On `2 <= n <= 60`,
the second route constructs the upper fiber from the maximal proper Fibonacci
divisors and constructs the minimal elements from the witness threshold
conditions. The report compares the actual sets, not only their cardinalities:

```text
B_n direct = B_n upper fiber: 59/59 set equalities
M_n direct = M_n witness: 59/59 set equalities
```

For `61 <= n <= 210`, the structural route checks the stated finite upper and
lower bounds. On every layer `3 <= n <= 210`, it also enumerates the rank-pure
sector (all layers in this range have at most four prime coordinates), checks
the exact-rank-prime Mobius formula on every nonempty support, and verifies that
every canonical and weighted rank-pure product belongs to the independently
constructed minimal-generator set. It also confirms that the rank-pure sector
is strict at `n=91`, where `169` is a ladder generator. The exact
Hearne--Wagner and connected-cover counts are
cross-checked against direct cover enumeration for `1 <= k <= 4`. Exact counts
through `k=80` also check convergence to the parity-dependent theta
normalization, the connected-cover ratio, and the central discrete local
limit. On every `3 <= n <= 210` layer the report also checks the pointwise
rank-window deaggregation inequalities and the refined private-coordinate
upper bound; on every squarefree layer it checks the exact-rank partition and
the BLMS pigeonhole inequality. It also reconstructs the fibotomic integer on
every rank in this range, verifies its exact-rank radical divisibility and the
rank-congruence spacing used in the entropy bound, and checks `a(10p) >= 2`
for the five eligible prime values with `10p <= 210`. In addition, it extracts
the positive-coordinate rank hypergraph of every minimal generator, verifies
the total and connected support spectra on all 208 layers, and checks that the
top-support slice has the product cardinality of its singleton diagonal atomic
families. It confirms that the only empty exact-rank prime fibers on
`3 <= d <= 210` are `d=6,12`, verifies
`7 <- 13 <- 233 <- 139801`, and checks `7 -> 8 -> 6 -> 12` by direct modular
rank computation. These finite checks support, but do not prove, the infinite
inverse-ray theorem; infinitude uses the classical exact-rank existence
theorem. These finite checks do not resolve the
asymptotic behavior of `R(n)`, establish (H2) or (BW), or compare the total
connected and disconnected arithmetic sectors without those hypotheses.

The squarefree-slice verifier independently enumerates all irredundant covers
for `1 <= k <= 4`, checks 36 exact full-support equality profiles for the
sharp weighted-cover lower bound, and compares direct rank-pure products with
the squarefree elements of the independently constructed `M_n` for every
squarefree `3 <= n <= 210`. The stored run contains 127 set equalities and 427
squarefree minimal generators. These checks do not show that the abstract
fixed-total extremizer is realizable by Fibonacci exact-rank primes.

## Checksum verification

Paths in `SHA256SUMS` are relative to the `artifacts` directory, including
the `../scripts/...` entries. Run the check from the manuscript directory
with exactly:

```sh
cd artifacts && sha256sum -c SHA256SUMS
```

A successful check prints exactly 15 `OK` lines and no failures. The manifest
and all files it covers use Unix LF line endings. The project-local
`.gitattributes` pins the reproducibility files to LF even when
`core.autocrlf=true`, and each verifier explicitly writes LF output, so a
clean checkout and regenerated reports have the same bytes on Windows,
Linux, and macOS.
