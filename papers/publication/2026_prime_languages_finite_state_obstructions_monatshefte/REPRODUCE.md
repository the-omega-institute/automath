# Reproducing the article, supplement, and finite checks

Run these commands from the manuscript directory. The computations use only
the Python standard library, exact integer arithmetic, and no network access.

## Environment

- Python 3.10 or later
- MiKTeX or TeX Live with XeLaTeX and `latexmk`
- no random seed: every computation is deterministic

## Compile

```powershell
latexmk -pdfxe -interaction=nonstopmode -halt-on-error main.tex
latexmk -pdfxe -interaction=nonstopmode -halt-on-error supplement.tex
```

Both commands must exit with status zero and produce `main.pdf` and
`supplement.pdf`.

## Finite verifier

Generate the archived report with one command:

```powershell
python artifacts/verify_pisot_pumping.py --output artifacts/pisot_pumping_output.txt
```

The report records the script version and SHA-256, Python version, complete
command line, and the fact that no random seed is used. It must end with
`OVERALL: PASS`. Exact expected totals are listed in `README.md` and enforced
inside the verifier; changed totals cause a nonzero exit instead of silently
overwriting a nominally passing archive.

## Unit tests

Run the artifact-local tests, not repository-root `pytest`:

```powershell
python -m unittest -v artifacts.test_verify_pisot_pumping
```

The submission includes the complete output as
`artifacts/unittest_output.txt`; it must report 19 tests and `OK`.

## Integrity

`artifacts/SHA256SUMS` records the digests of the verifier, its unit tests,
both archived outputs, the literature audit, and this reproduction file.
Verify them in PowerShell with:

```powershell
Get-Content artifacts/SHA256SUMS | ForEach-Object {
    $hash, $name = $_ -split '  ', 2
    $actual = (Get-FileHash -Algorithm SHA256 $name).Hash.ToLower()
    if ($actual -ne $hash) { throw "checksum mismatch: $name" }
}
```

These computations are finite consistency checks, not formal proofs. The
proofs in the article and supplement do not infer their universal conclusions
from the sampled cases.
