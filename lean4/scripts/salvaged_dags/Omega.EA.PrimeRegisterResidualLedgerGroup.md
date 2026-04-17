# Omega.EA.PrimeRegisterResidualLedgerGroup

- File: `Omega/EA/PrimeRegisterResidualLedgerGroup.lean`
- Struct: `FibKernelBasisFiniteDepthData`
- Paper label: `thm:prime-register-residual-ledger-group`
- Goal theorem: `paper_prime_register_residual_ledger_group`

## Structure docstring

Chapter-local wrapper for the finite-depth Fibonacci-kernel basis package. The existing
zero-ledger calculations show that the displayed generators lie in the additive kernel; the
remaining fields package the finite-depth linear-independence statement, the `L - 1` rank count,
and the transport of this additive basis to the multiplicative residual group.

## Goal

`ledgerValZ (residualBasisGenerator 0) = 0 ∧ (∀ k : ℕ, ledgerValZ (residualBasisGenerator (k + 1)) = 0) ∧ (∀ a : DigitCfg, (R a).1 = toIntCfg a - toIntCfg (NF_pr a)) ∧ (∀ a : DigitCfg, ledgerValZ (R a).1 = 0) ∧ Function.Injective Theta`

## Theorem docstring

Paper-facing wrapper for the residual-ledger decomposition:
    the Fibonacci kernel generators lie in the zero-ledger subgroup, every residual factor
    lands in `H`, and `(NF_pr, R)` is injective.
    thm:prime-register-residual-ledger-group

## DAG

Nodes (Prop fields):
- `linearIndependentFiniteDepth` (leaf)
- `kernelRankFiniteDepth` (leaf)
- `multiplicativeResidualGroupFiniteDepth` (leaf)

Edges:
- (none)

## Imports
- `Mathlib.Data.Finsupp.SMul`
- `Mathlib.Tactic`
- `Omega.EA.PrimeRegisterLocalMoves`
- `Omega.EA.PrimeRegisterMultiplicativeNormalizationAdditiveIso`
