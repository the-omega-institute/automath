# Reproducing the finite checks

Run all commands from the paper directory. The stored run used Python 3.10.11.
The verifiers use only the Python standard library, and the computations use
deterministic exact integer arithmetic apart from displayed algebraic-root
approximations.

## Verification commands

```sh
python -m unittest discover -s artifacts -p "test_*.py" -v
python artifacts/verify_metallic_threshold.py --output artifacts/metallic_threshold_verification.txt
python artifacts/verify_quadratic_pisot_threshold.py --output artifacts/quadratic_pisot_threshold_verification.txt
python artifacts/verify_simple_parry_causal.py --output artifacts/simple_parry_causal_verification.txt
```

The unit suite prints `Ran 30 tests` followed by `OK`. The verifier conclusions
are:

```text
SUMMARY: 0 failures / 0 counterexamples
SUMMARY: 0 failures / 0 unexpected collisions
SUMMARY: 0 failures
```

All three verifiers exit zero and write Unix LF reports. The reports contain no
clock or date fields.

## Checksum verification

Paths in `SHA256SUMS` are relative to the `artifacts` directory. From the paper
directory, run exactly:

```sh
cd artifacts && sha256sum -c SHA256SUMS
```

A successful check prints exactly 11 `OK` lines and no failures. The
project-local `.gitattributes` pins every file covered by the manifest to LF.
