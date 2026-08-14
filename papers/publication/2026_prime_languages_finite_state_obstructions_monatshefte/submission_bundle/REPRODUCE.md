# Reproducing the article, supplement, and finite checks

Run all commands from the manuscript directory. The computations use only the
Python standard library, exact integer arithmetic, and no network access.

## Install

- Python 3.10 or later
- MiKTeX or TeX Live with XeLaTeX and `latexmk`
- Poppler `pdfinfo`, `pdftotext`, and `pdftoppm` for PDF inspection

No Python packages are required. Every computation is deterministic and uses
no random seed.

## Clean PDF rebuild

The clean commands below remove the old auxiliary state, including `.aux`,
before rebuilding.

```powershell
latexmk -C main.tex
latexmk -C supplement.tex
latexmk -pdfxe -interaction=nonstopmode -halt-on-error main.tex
latexmk -pdfxe -interaction=nonstopmode -halt-on-error supplement.tex
```

Each command must exit with status zero. The final `main.log` and
`supplement.log` must contain no undefined reference, undefined citation, or
multiply-defined-label diagnostic.

## Finite verifier

Regenerate the referee-readable report:

```powershell
python artifacts/verify_pisot_pumping.py --output artifacts/pisot_pumping_output.txt
```

Expected conclusion:

```text
systems checked: 6
affine action cases: 2282
congruence failures: 0
OVERALL: PASS
```

The report contains every other expected total and every failure counter. The
verifier exits nonzero if a total drifts.

## Unit tests

Run the artifact-local suite:

```powershell
python -m unittest -v artifacts.test_verify_pisot_pumping
```

Expected summary:

```text
Ran 19 tests
OK
```

The complete transcript is archived as `artifacts/unittest_output.txt`.

## Integrity

`artifacts/SHA256SUMS` covers the verifier, unit tests, archived outputs,
literature audit, reproduction instructions, and submission documents. Verify
it in PowerShell with:

```powershell
Get-Content artifacts/SHA256SUMS | ForEach-Object {
    $hash, $name = $_ -split '  ', 2
    $actual = (Get-FileHash -Algorithm SHA256 $name).Hash.ToLower()
    if ($actual -ne $hash) { throw "checksum mismatch: $name" }
}
```

These finite checks support reproducibility; the mathematical proofs do not
infer universal statements from sampled cases.
