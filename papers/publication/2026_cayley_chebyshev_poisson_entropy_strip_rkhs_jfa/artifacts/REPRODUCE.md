# Reproducing the computational checks

Run all commands from the paper directory. The stored run used Python 3.10.11,
NumPy 1.26.4, SciPy 1.12.0, SymPy 1.13.1, and mpmath 1.3.0. Install the
dependencies with:

```sh
python -m pip install "numpy==1.26.4" "scipy==1.12.0" "sympy==1.13.1" "mpmath==1.3.0"
```

## Verification commands

```sh
python -m unittest discover -s artifacts -p "test_*.py" -v
python artifacts/verify_boundary_regular_variation.py --output artifacts/verify_boundary_regular_variation_output.txt
python artifacts/verify_moment_equivalence.py --output artifacts/verify_moment_equivalence_output.txt
python artifacts/verify_oracle_A2.py --output artifacts/verify_oracle_A2_output.txt
```

The unit suite prints `Ran 14 tests` followed by `OK`. The three archived
reports end with, respectively:

```text
RESULT: PASS
RESULT: PASS
RESULT: PASS
```

All three verifiers exit zero. Their `--output` files are written with Unix LF
line endings. The reports contain no clock or date fields.

## Checksum verification

Paths in `SHA256SUMS` are relative to the `artifacts` directory. From the paper
directory, run exactly:

```sh
cd artifacts && sha256sum -c SHA256SUMS
```

A successful check prints exactly 13 `OK` lines and no failures. The
project-local `.gitattributes` pins every file covered by the manifest to LF.
