# Reproducing the article, separate finite-state paper, and finite checks

Run all commands from this directory. The computations use only the Python
standard library, exact integer arithmetic, and no network access.

## Install

- Python 3.10 or later
- MiKTeX or TeX Live with XeLaTeX and `latexmk`
- Poppler `pdfinfo`, `pdftotext`, and `pdftoppm` for PDF inspection

No Python packages are required. Every computation is deterministic and uses
no random seed.

## Clean PDF rebuild

```powershell
latexmk -C main.tex
latexmk -C finite_state_article.tex
latexmk -pdfxe -interaction=nonstopmode -halt-on-error main.tex
latexmk -pdfxe -interaction=nonstopmode -halt-on-error finite_state_article.tex
```

Both commands must exit with status zero. The final logs must contain no
undefined reference, undefined citation, or multiply-defined-label
diagnostic. Only the primary article belongs to the Monatshefte submission;
the finite-state paper is an independent manuscript.

## Finite verifier

```powershell
python artifacts/verify_pisot_pumping.py --output artifacts/pisot_pumping_output.txt
```

Expected conclusion:

```text
systems checked: 6
affine action cases: 2282
weak-Perron radical cases: 18
length-order-free selection cases: 1
congruence failures: 0
OVERALL: PASS
```

## Unit tests

```powershell
python artifacts/run_unit_tests.py --output artifacts/unittest_output.txt
```

Expected summary:

```text
Ran 21 tests
OK
```

## Integrity

`artifacts/SHA256SUMS` covers the verifier, unit tests, archived outputs,
literature record, artifact-local reproduction instructions, and LF policy.
Verify from the paper directory with:

```sh
cd artifacts && sha256sum -c SHA256SUMS
```

A successful check prints exactly 8 `OK` lines and no failures.
