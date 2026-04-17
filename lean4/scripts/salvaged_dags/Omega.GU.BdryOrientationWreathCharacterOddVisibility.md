# Omega.GU.BdryOrientationWreathCharacterOddVisibility

- File: `Omega/GU/BdryOrientationWreathCharacterOddVisibility.lean`
- Struct: `BdryOrientationWreathCharacterOddVisibilityData`
- Paper label: `thm:bdry-orientation-wreath-character-odd-visibility`
- Goal theorem: `paper_bdry_orientation_wreath_character_odd_visibility`

## Structure docstring

Chapter-local package for the odd-block visibility law in the boundary-orientation wreath
setting. The data record the block-level visibility factorization, the induced global sign
formula, and the equal-block specialization to the wreath-product character law.

## Goal

`D.blockOddVisibility ∧ D.globalCharacterFormula ∧ D.uniformBlockWreathFormula`

## Theorem docstring

Paper-facing wrapper for the odd-block visibility theorem: the block factorization isolates
the odd blocks, this yields the global sign formula, and the equal-block case specializes to the
wreath-product character formula.
    thm:bdry-orientation-wreath-character-odd-visibility

## DAG

Nodes (Prop fields):
- `oddBlockVisibilityFactorization` (leaf)
- `blockOddVisibility` (leaf)
- `globalCharacterFormula` (leaf)
- `uniformBlockWreathFormula` (leaf)

Edges:
- (none)

## Imports
- `Mathlib.Tactic`
