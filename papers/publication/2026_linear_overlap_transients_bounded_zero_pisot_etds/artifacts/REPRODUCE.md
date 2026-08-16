# Reproducing the finite checks

Run all commands from the paper directory. The verifiers use only the Python
standard library and deterministic exact arithmetic apart from displayed
algebraic-root approximations.

## Verification commands

```sh
python artifacts/verify_fixed_cubic_audit.py
python artifacts/test_bounded_zero_arbitrary_D.py
```

The first command checks the fixed cubic small-aperture and terminal-word
audit. The second checks the arbitrary-alphabet adjacent-collapse cases and
includes the seven-edge regression for initial values `(1, 2, 4)`, `D=2`,
and `m=2`. Both commands exit zero only when every case passes.

## Checksum verification

Paths in `SHA256SUMS` are relative to the `artifacts` directory. From the
paper directory, run:

```sh
cd artifacts && sha256sum -c SHA256SUMS
```

A successful check prints one `OK` line for every entry and no failures.
