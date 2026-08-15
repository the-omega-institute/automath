# Reproducing the finite and symbolic checks

Run all commands from the paper directory. The stored run used Python 3.10.11.
The verifier and tests use only the Python standard library.

## Verification commands

```sh
python -m unittest discover -s artifacts -p "test_*.py" -v
python artifacts/verify_A9_r1.py --output artifacts/verify_A9_r1_output.txt
```

The unit suite prints `Ran 5 tests` followed by `OK`. The archived report begins
with `PASS NWW Cechization formula checks` and ends with:

```text
OPEN comparisons intentionally unverified: NWW Problems 8.1(b), 8.2(a), 8.2(b)
```

The verifier exits zero. Its counterexample line is an expected finite check,
not a verification failure. The report uses Unix LF and contains no clock or
date fields. This artifact directory has no separate literature-check file.

## Checksum verification

Paths in `SHA256SUMS` are relative to the `artifacts` directory. From the paper
directory, run exactly:

```sh
cd artifacts && sha256sum -c SHA256SUMS
```

A successful check prints exactly 5 `OK` lines and no failures. The
project-local `.gitattributes` pins every file covered by the manifest to LF.
