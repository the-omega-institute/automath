# Diagonal covariance certificate replay

This archive certifies only the preselected population point `z_0 = 1/2` used
in the manuscript's pointwise projection example. It does not certify a
parameter interval, a critical value, a finite-record statistic, or coverage.

Files:

- `diagonal_branch_certificate.py`: standard-library interval-arithmetic
  generator and unit tests.
- `diagonal_branch_z_half.json`: stored outward-rounded transcript.

Recorded replay environment:

- Python 3.10.11
- `decimal` 1.70
- `libmpdec` 2.5.1
- third-party dependencies: none

From the manuscript source directory, run:

```text
python certificates/diagonal_branch_certificate.py --test
python certificates/diagonal_branch_certificate.py --environment
python certificates/diagonal_branch_certificate.py --hash
```

The first command regenerates the transcript, compares it with the stored JSON,
checks the displayed covariance entries and determinant directly from the
printed formulas, and runs negative regression fixtures. The `--hash` command
prints the canonical LF-terminated JSON hash and byte length.

Immutable SHA-256 values for the submitted files:

```text
FB3006C0E2F5C44E754C78967BBF52696B241D2845231A1F28C0AA02DDF846A1  diagonal_branch_certificate.py
C469252C9AAD42B5358C2FA25623D96F17DCC19D6760F38ACBC698EB5270FF0B  diagonal_branch_z_half.json
```

Canonical regenerated transcript:

```text
61fa032f034e8aad38ab88b52e98071d89335847ad6fda397ca570bf4a3c7db9  13323 bytes
```

The raw JSON file hash can differ from the canonical regenerated hash if a
checkout changes line endings or adds a byte-order mark. The unit test compares
the parsed data after canonical serialization and therefore detects substantive
changes.
