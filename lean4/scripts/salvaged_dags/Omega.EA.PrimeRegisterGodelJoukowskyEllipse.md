# Omega.EA.PrimeRegisterGodelJoukowskyEllipse

- File: `Omega/EA/PrimeRegisterGodelJoukowskyEllipse.lean`
- Struct: `PrimeRegisterGodelJoukowskyEllipseData`
- Paper label: `prop:prime-register-godel-joukowsky-ellipse`
- Goal theorem: `paper_prime_register_godel_joukowsky_ellipse`

## Structure docstring

Chapter-local package for the paper-facing Joukowsky ellipse statement. The fields record the
invariance of the ellipse image under `r ↔ r⁻¹`, identification of the semiaxes and foci from the
explicit parametrization, and the multiplicativity statement showing that the Gödel scale map
respects the ellipse product `E_r ⊙ E_s = E_{rs}`.

## Goal

`D.ellipseInvariantUnderInversion ∧ D.fociAndSemiaxesIdentified ∧ D.godelMapIsMonoidHom`

## Theorem docstring

Paper-facing wrapper for the prime-register Gödel/Joukowsky ellipse package: the ellipse image
depends only on the unordered pair `{r, r⁻¹}`, the explicit parametrization identifies semiaxes
and foci, and multiplicativity of the Gödel scale matches the monoid law
`E_r ⊙ E_s = E_{rs}`.
    prop:prime-register-godel-joukowsky-ellipse

## DAG

Nodes (Prop fields):
- `ellipseInvariantUnderInversion` (leaf)
- `fociAndSemiaxesIdentified` (leaf)
- `godelMapIsMonoidHom` (leaf)

Edges:
- (none)

## Imports
- `Mathlib.Tactic`
- `Omega.EA.JoukowskyEllipse`
