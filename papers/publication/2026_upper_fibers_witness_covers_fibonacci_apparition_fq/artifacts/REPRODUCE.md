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
  rank-window deaggregation and squarefree pigeonhole checks, refined
  private-coordinate upper bounds, fibotomic rank-entropy and exact-rank
  radical checks, the finite Jarden consequence, environment reporting, and
  factorization-archive generation and validation.
- `test_verify_finite_claims.py`: unit tests for the arithmetic routines,
  finite bounds, archive round trip, and report contents.
- `fibonacci_factorizations_2_210.tsv`: exact factorization input/archive.
- `tab_birth_layer_data.tex`: generated table included in the manuscript.
- `birth_layer_table_output.txt`: complete stdout from table generation.
- `finite_verification.txt`: complete stdout report from the verification run.
- `SHA256SUMS`: SHA-256 digest of every reproducibility file listed above.

## Commands

Run these commands from the manuscript directory:

```powershell
python -m unittest discover -s artifacts -p "test_verify_finite_claims.py" -v
python artifacts\compute_birth_layer_table.py
python artifacts\verify_finite_claims.py --exhaustive-max 60 --scalable-max 210 --output artifacts\finite_verification.txt --factorizations-output artifacts\fibonacci_factorizations_2_210.tsv
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
every canonical rank-pure product belongs to the independently constructed
minimal-generator set. The exact Hearne--Wagner and connected-cover counts are
cross-checked against direct cover enumeration for `1 <= k <= 4`. Exact counts
through `k=80` also check convergence to the parity-dependent theta
normalization, the connected-cover ratio, and the central discrete local
limit. On every `3 <= n <= 210` layer the report also checks the pointwise
rank-window deaggregation inequalities and the refined private-coordinate
upper bound; on every squarefree layer it checks the exact-rank partition and
the BLMS pigeonhole inequality. It also reconstructs the fibotomic integer on
every rank in this range, verifies its exact-rank radical divisibility and the
rank-congruence spacing used in the entropy bound, and checks `a(10p) >= 2`
for the five eligible prime values with `10p <= 210`. These finite checks do
not resolve the
asymptotic behavior of `R(n)`, establish (H2) or (BW), or compare the total
connected and disconnected arithmetic sectors without those hypotheses.

To verify the checksums in PowerShell:

```powershell
Get-Content artifacts\SHA256SUMS | ForEach-Object {
    $hash, $name = $_ -split '  ', 2
    if ((Get-FileHash -Algorithm SHA256 (Join-Path artifacts $name)).Hash.ToLower() -ne $hash) {
        throw "checksum mismatch: $name"
    }
}
```
