# Reproducing the finite-window checks

Run all commands from the paper directory. The stored run used Python 3.10.11,
NumPy 1.26.4, mpmath 1.3.0, Numba 0.64.0, and pytest. Install the dependencies
with:

```sh
python -m pip install "numpy==1.26.4" "mpmath==1.3.0" "numba==0.64.0" pytest
```

## Verification commands

```sh
python -m pytest artifacts -q
python artifacts/verify_deepening_delta.py --output artifacts/deepening_delta_verification.txt
python artifacts/verify_real_tilt_pressure.py
python artifacts/verify_speed_separation.py --output artifacts/speed_separation_verification.txt
```

The test suite prints `20 passed`. The verifier conclusions are:

```text
RESULT: 0 failures / 0 counterexamples
RESULT: 0 numerical failures / full-LDP orbit-padding audit passed
STATUS: PASS
```

The first two verifiers also regenerate `ldp_rate_shape.csv`,
`real_tilt_pressure.csv`, and `real_tilt_rate.csv`. The CSV records and text
reports use Unix LF. Archived path fields contain file names rather than
checkout-specific absolute paths, and no archived file contains clock or date
fields.

## Checksum verification

Paths in `SHA256SUMS` are relative to the `artifacts` directory. From the paper
directory, run exactly:

```sh
cd artifacts && sha256sum -c SHA256SUMS
```

A successful check prints exactly 15 `OK` lines and no failures. The
project-local `.gitattributes` pins every file covered by the manifest to LF.
