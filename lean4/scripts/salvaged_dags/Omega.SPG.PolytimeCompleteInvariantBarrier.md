# Omega.SPG.PolytimeCompleteInvariantBarrier

- File: `Omega/SPG/PolytimeCompleteInvariantBarrier.lean`
- Struct: `PolytimeCompleteInvariantBarrierData`
- Paper label: `thm:spg-polytime-complete-invariant-implies-p-equals-np`
- Goal theorem: `paper_spg_polytime_complete_invariant_implies_p_equals_np`

## Structure docstring

Chapter-local package for the complete-invariant barrier. The data record the polynomial-time
computability of the invariant, the reduction of `UNSAT` to comparison with a fixed unsatisfiable
formula, and the standard complexity-theoretic consequences.

## Goal

`D.unsatReducesToInvariantEquality ∧ D.unsatInP ∧ D.satInP ∧ D.pEqualsNp`

## Theorem docstring

Paper-facing wrapper for the resource-bounded complete-invariant obstruction: comparing the
invariant of a formula with the invariant of a fixed contradiction decides `UNSAT` in polynomial
time, hence also `SAT`, and therefore forces `P = NP`.
    thm:spg-polytime-complete-invariant-implies-p-equals-np

## DAG

Nodes (Prop fields):
- `invariantComputableInPolynomialTime`
- `completeInvariant`
- `fixedUnsatisfiableFormula`
- `unsatReducesToInvariantEquality` (derived)
- `unsatInP` (derived)
- `satInP` (derived)
- `pEqualsNp` (derived)

Edges:
- completeInvariant + fixedUnsatisfiableFormula  →  **unsatReducesToInvariantEquality**
- invariantComputableInPolynomialTime + unsatReducesToInvariantEquality  →  **unsatInP**
- unsatInP  →  **satInP**
- satInP  →  **pEqualsNp**

## Imports
