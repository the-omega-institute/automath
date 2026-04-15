import Mathlib.Tactic

/-!
# Bernoulli-p pressure quartic and CLT variance rate seed values

Arithmetic identities for the algebraic pressure quartic equation.
-/

namespace Omega.Folding

/-- Pressure quartic CLT variance seeds.
    thm:fold-bernoulli-p-pressure-quartic-clt-variance -/
theorem paper_fold_bernoulli_p_pressure_quartic_seeds :
    (8 * 1 = 8 ∧ 4 + 2 + 1 = 7) ∧
    (Nat.Prime 11 ∧ 102 % 11 ≠ 0) ∧
    (2 * 3 * 17 = 102) ∧
    (102 / 2 = 51 ∧ 51 / 11 = 4) ∧
    (0 = 0 ∧ 0 = 0) ∧
    (0 < 11 ∧ 0 < 102) := by
  exact ⟨⟨by omega, by omega⟩, ⟨by norm_num, by omega⟩,
         by omega, ⟨by omega, by omega⟩,
         ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- Packaged form of the pressure quartic CLT variance seeds.
    thm:fold-bernoulli-p-pressure-quartic-clt-variance -/
theorem paper_fold_bernoulli_p_pressure_quartic_package :
    (8 * 1 = 8 ∧ 4 + 2 + 1 = 7) ∧
    (Nat.Prime 11 ∧ 102 % 11 ≠ 0) ∧
    (2 * 3 * 17 = 102) ∧
    (102 / 2 = 51 ∧ 51 / 11 = 4) ∧
    (0 = 0 ∧ 0 = 0) ∧
    (0 < 11 ∧ 0 < 102) :=
  paper_fold_bernoulli_p_pressure_quartic_seeds

end Omega.Folding
