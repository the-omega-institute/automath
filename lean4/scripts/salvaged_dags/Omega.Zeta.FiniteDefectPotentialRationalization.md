# Omega.Zeta.FiniteDefectPotentialRationalization

- File: `Omega/Zeta/FiniteDefectPotentialRationalization.lean`
- Struct: `FiniteDefectPotentialRationalizationData`
- Paper label: `prop:xi-limit-defect-potential-rationalization`
- Goal theorem: `paper_xi_limit_defect_potential_rationalization`

## Structure docstring

Chapter-local package for the finite-defect rationalization of the limit defect potential. The
fields record the Cayley-modulus closed form for each kernel, the exponentiation of the finite sum
into a finite product, the rational continuation of that product, the explicit zero/pole
description, and the uniqueness of the defect multiset read off from those zero/pole locations.

## Goal

`D.cayleyModulusClosedForm ∧ D.exponentialFiniteProduct ∧ D.rationalExtension ∧ D.zeroPoleDescription ∧ D.defectMultisetUniqueness`

## Theorem docstring

Paper-facing wrapper for the finite-defect rationalization of the limit defect potential:
expanding each kernel through the Cayley modulus closed form turns the exponentiated finite sum
into a finite product, this product extends to a rational function, and its zeros and poles occur
exactly at the shifted defect locations, so the defect multiset is uniquely recoverable.
    prop:xi-limit-defect-potential-rationalization

## DAG

Nodes (Prop fields):
- `cayleyModulusClosedForm` (leaf)
- `exponentialFiniteProduct` (derived)
- `rationalExtension` (derived)
- `zeroPoleDescription` (derived)
- `defectMultisetUniqueness` (derived)

Edges:
- cayleyModulusClosedForm  →  **exponentialFiniteProduct**
- exponentialFiniteProduct  →  **rationalExtension**
- rationalExtension  →  **zeroPoleDescription**
- rationalExtension + zeroPoleDescription  →  **defectMultisetUniqueness**

## Imports
- `Mathlib.Tactic`
