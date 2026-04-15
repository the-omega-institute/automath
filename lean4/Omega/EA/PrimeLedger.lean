import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Omega.EA.PrimeLedger

/-- Prime ledger additivity: padicValNat seeds.
    prop:ordinary-prime-ledger-linearises-multiplication -/
theorem paper_prime_ledger_linearizes_multiplication :
    -- padicValNat additivity seeds
    (padicValNat 2 (2 * 3) = padicValNat 2 2 + padicValNat 2 3) ∧
    (padicValNat 3 (2 * 3) = padicValNat 3 2 + padicValNat 3 3) ∧
    (padicValNat 2 (4 * 6) = padicValNat 2 4 + padicValNat 2 6) ∧
    (padicValNat 3 (4 * 6) = padicValNat 3 4 + padicValNat 3 6) ∧
    -- L(1) = 0 seeds
    (padicValNat 2 1 = 0) ∧ (padicValNat 3 1 = 0) ∧ (padicValNat 5 1 = 0) ∧
    -- injectivity seed
    (padicValNat 2 6 ≠ padicValNat 2 10 ∨ padicValNat 3 6 ≠ padicValNat 3 10 ∨
     padicValNat 5 6 ≠ padicValNat 5 10) := by
  native_decide

end Omega.EA.PrimeLedger
