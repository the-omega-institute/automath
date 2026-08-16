# Reproducing both PDFs and all exact verification artifacts

Run all commands from the manuscript directory.

## Install

- Python 3.10 or later
- SymPy 1.13.1
- MiKTeX or TeX Live with XeLaTeX, BibTeX, and `latexmk`
- Poppler `pdfinfo`, `pdftotext`, and `pdftoppm` for PDF inspection

Create an isolated environment and install the only Python dependency:

```powershell
python -m venv .venv-reproduce
.\.venv-reproduce\Scripts\python -m pip install "sympy==1.13.1"
```

The computations use exact arithmetic and no random seed.

## Clean PDF rebuild

The clean commands remove old `.aux` and other generated LaTeX state first:

```powershell
latexmk -C main.tex
latexmk -C supplement.tex
latexmk -pdfxe -interaction=nonstopmode -halt-on-error main.tex
latexmk -pdfxe -interaction=nonstopmode -halt-on-error supplement.tex
```

All commands must exit with status zero. The final logs must contain no
undefined reference, undefined citation, or multiply-defined-label diagnostic.

## Exact verifiers

```powershell
.\.venv-reproduce\Scripts\python artifacts/verify_a5_results.py
.\.venv-reproduce\Scripts\python artifacts/verify_linear_collision_claims.py
.\.venv-reproduce\Scripts\python artifacts/verify_twisted_determinant_rigidity.py
```

Each program ends with:

```text
STATUS: PASS
```

The reports are `artifacts/verify_a5_results_output.txt`,
`artifacts/verify_linear_collision_claims_output.txt`, and
`artifacts/verify_twisted_determinant_rigidity_output.txt`.

## Unit tests

```powershell
.\.venv-reproduce\Scripts\python artifacts/run_unit_tests.py `
  --output artifacts/unittest_output.txt
```

Expected summary:

```text
Ran 44 tests
OK
```

The full transcript is archived as `artifacts/unittest_output.txt`.

## Exact S3 certificate

```powershell
.\.venv-reproduce\Scripts\python certificates/s3_log_certificates.py `
  --write-cert certificates/s3_log_certificates.cert
.\.venv-reproduce\Scripts\python certificates/s3_log_certificates.py `
  --write-cert certificates/s3_log_certificates.run.txt
```

The second command's standard output is archived as
`certificates/s3_log_certificates.run.txt` and ends with:

```text
fixed-label windows verified
```

## Integrity

Paths in `artifacts/SHA256SUMS` are relative to the `artifacts` directory,
including its `../certificates/...` and `../.gitattributes` entries. From the
paper directory, run exactly:

```sh
cd artifacts && sha256sum -c SHA256SUMS
```

A successful check prints exactly 18 `OK` lines and no failures.

The scripts are independent exact consistency checks. The article and
Supplementary Material do not use finite computation as a substitute for a
proof.
