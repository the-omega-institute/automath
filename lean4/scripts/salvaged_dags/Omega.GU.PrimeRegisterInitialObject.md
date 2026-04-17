# Omega.GU.PrimeRegisterInitialObject

- File: `Omega/GU/PrimeRegisterInitialObject.lean`
- Struct: `PrimeRegisterInitialObjectData`
- Paper label: `thm:group-jg-prime-register-initial-object`
- Goal theorem: `paper_group_jg_prime_register_initial_object`

## Structure docstring

Chapter-local package for the prime-register initial-object theorem. The fields isolate the
coordinatewise injectivity of the shifted-prime encoding and the existence/uniqueness of the
homomorphism extending a basis assignment from the shifted prime generators.

## Goal

`D.isEncoder ∧ D.isInitial`

## Theorem docstring

Paper-facing wrapper for the shifted-prime register package: coordinate equality proves the
encoding map is injective, and free commutative-monoid extension from the shifted prime basis
supplies the unique initial morphism.
    thm:group-jg-prime-register-initial-object

## DAG

Nodes (Prop fields):
- `isEncoder` (derived)
- `isInitial` (derived)
- `encodingInjectiveByCoordinates` (leaf)
- `basisExtensionExists` (leaf)
- `basisExtensionUnique` (leaf)

Edges:
- encodingInjectiveByCoordinates  →  **isEncoder**
- basisExtensionExists + basisExtensionUnique  →  **isInitial**

## Imports
- `Mathlib.Tactic`
