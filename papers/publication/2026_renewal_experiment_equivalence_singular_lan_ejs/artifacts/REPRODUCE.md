# Reproduction

Run from the article directory with Python 3.10 or later.

## Mathematical sanity checks

```sh
python -m unittest discover -s artifacts -p "test_*.py" -v
python artifacts/verify_claims.py --output artifacts/verify_claims_output.txt
```

The unit suite reports 16 passing tests.  The verifier reports 12 deterministic
checks and exits zero.  These computations are algebraic regression and sanity
checks; proofs are in the article and supplement.

## Documents

The main article and supplement cross-reference one another.  For a clean
build, remove their generated auxiliaries and alternate:

```sh
latexmk -C main.tex
latexmk -C supplementary.tex
latexmk -pdfxe -interaction=nonstopmode -halt-on-error supplementary.tex
latexmk -pdfxe -interaction=nonstopmode -halt-on-error main.tex
latexmk -pdfxe -interaction=nonstopmode -halt-on-error supplementary.tex
latexmk -pdfxe -interaction=nonstopmode -halt-on-error main.tex
latexmk -pdfxe -interaction=nonstopmode -halt-on-error cover_letter.tex
```

Successful final logs contain no undefined reference, undefined citation, or
multiply-defined-label warning.

## Checksums

Paths in `SHA256SUMS` are relative to `artifacts`:

```sh
cd artifacts && sha256sum -c SHA256SUMS
```

