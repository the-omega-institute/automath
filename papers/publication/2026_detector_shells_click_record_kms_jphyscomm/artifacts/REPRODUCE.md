# Reproducing the numerical checks

Run all commands from the paper directory. The stored run used Python 3.10.11,
NumPy 1.26.4, SciPy 1.12.0, and mpmath 1.3.0. Install the dependencies with:

```sh
python -m pip install "numpy==1.26.4" "scipy==1.12.0" "mpmath==1.3.0"
```

## Verification commands

```sh
python -m unittest discover -s artifacts -p "test_*.py" -v
python artifacts/verify_A8_results.py --output artifacts/verify_A8_results_output.txt
python artifacts/verify_nstate_identifiability.py --output artifacts/verify_nstate_identifiability_output.txt --two-state-output artifacts/verify_two_state_fibre_output.txt
```

The unit suite prints `Ran 58 tests` followed by `OK`. The first report begins
with `A8 sampled-counter verification` and ends with a finite tested
information range. The second begins with
`Sharp killed-reset D-MAP identifiability dichotomy verification` and ends with
the stated exact Markovian orbit-fibre boundary. The two-state option writes the
deterministic two-state diagnostic excerpt. Both verifiers exit zero.

All archived reports use Unix LF and contain no clock or date fields.

## Checksum verification

Paths in `SHA256SUMS` are relative to the `artifacts` directory. From the paper
directory, run exactly:

```sh
cd artifacts && sha256sum -c SHA256SUMS
```

A successful check prints exactly 10 `OK` lines and no failures. The
project-local `.gitattributes` pins every file covered by the manifest to LF.
