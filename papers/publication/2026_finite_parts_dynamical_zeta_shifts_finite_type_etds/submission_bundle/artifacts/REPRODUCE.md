# Reproducing the exact checks

Run all commands from the paper directory. The stored run used Python 3.10.11,
SymPy 1.13.1, and mpmath 1.3.0. Install the dependencies with:

```sh
python -m pip install "sympy==1.13.1" "mpmath==1.3.0"
```

## Verification commands

```sh
python artifacts/verify_a5_results.py
python artifacts/verify_linear_collision_claims.py
python artifacts/verify_twisted_determinant_rigidity.py
python artifacts/run_unit_tests.py --output artifacts/unittest_output.txt
python certificates/s3_log_certificates.py --write-cert certificates/s3_log_certificates.cert
python certificates/s3_log_certificates.py --write-cert certificates/s3_log_certificates.run.txt
```

All three verifier reports end with `STATUS: PASS`. The linear-collision
verifier checks 2,496 squarefree certificates, 24 sharp cases, 124 positive
rational collision cases, 12 constructed collision cases, and three exact
odd-prime matrix instances. The test runner executes 44
tests and the archived transcript ends with:

```text
Ran 44 tests

OK
```

The test runner prints the ordinary live transcript, including its elapsed
test time, to stdout. It removes that one wall-clock duration from the archived
transcript while preserving the Python version, command, test names, results,
count, and final status. Both S3 certificate commands end with
`fixed-label windows verified`. All generated reports and certificates use
Unix LF.

## Checksum verification

Paths in `SHA256SUMS` are relative to the `artifacts` directory, including the
`../certificates/...` and `../.gitattributes` entries. From the paper directory,
run exactly:

```sh
cd artifacts && sha256sum -c SHA256SUMS
```

A successful check prints exactly 18 `OK` lines and no failures. The
project-local `.gitattributes` pins every file covered by the manifest to LF.
