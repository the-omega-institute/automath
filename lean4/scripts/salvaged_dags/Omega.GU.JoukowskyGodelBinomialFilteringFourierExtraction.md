# Omega.GU.JoukowskyGodelBinomialFilteringFourierExtraction

- File: `Omega/GU/JoukowskyGodelBinomialFilteringFourierExtraction.lean`
- Struct: `JoukowskyGodelBinomialFilteringData`
- Paper label: `thm:group-jg-binomial-filtering-fourier-extraction`
- Goal theorem: `paper_group_jg_binomial_filtering_fourier_extraction`

## Structure docstring

Chapter-local package for the pushed-forward moment family, its finite binomial/Laurent
expansion, and the two extremal Fourier-coefficient extractions. The witness fields store the four
paper-facing consequences used by the wrapper theorem.

## Goal

`D.binomialFormula ∧ D.positiveModeExtraction ∧ D.negativeModeExtraction ∧ D.fourierSpectrumDeterminesMeasure`

## Theorem docstring

Paper-facing wrapper for the Joukowsky--Gödel binomial filtering and Fourier extraction
package.
    thm:group-jg-binomial-filtering-fourier-extraction

## DAG

Nodes (Prop fields):
- `binomialFormula` (leaf)
- `positiveModeExtraction` (leaf)
- `negativeModeExtraction` (leaf)
- `fourierSpectrumDeterminesMeasure` (leaf)

Edges:
- (none)

## Imports
- `Mathlib.Tactic`
