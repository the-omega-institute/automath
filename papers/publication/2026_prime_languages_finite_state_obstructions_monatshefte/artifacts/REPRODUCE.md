# Reproducing the finite checks

Run all commands from the paper directory. The stored run used Python 3.10.11.
The verifier and tests use only the Python standard library, exact integer
arithmetic, no network access, and no random seed.

## Verification commands

```sh
python artifacts/verify_pisot_pumping.py --output artifacts/pisot_pumping_output.txt
python artifacts/run_unit_tests.py --output artifacts/unittest_output.txt
```

The verifier report ends with `OVERALL: PASS`. The test runner executes 19
tests and the archived transcript ends with:

```text
Ran 19 tests

OK
```

The test runner prints the ordinary live transcript, including its elapsed
test time, to stdout. It removes that one wall-clock duration from
`unittest_output.txt`, while preserving the Python version, command, test
names, results, count, and final status. Both archived reports use Unix LF.

## Checksum verification

Paths in `SHA256SUMS` are relative to the `artifacts` directory. From the paper
directory, run exactly:

```sh
cd artifacts && sha256sum -c SHA256SUMS
```

A successful check prints exactly 8 `OK` lines and no failures. The
project-local `.gitattributes` pins every file covered by the manifest to LF.
