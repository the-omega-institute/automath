import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Zeta.HankelFinitefieldRandomCompletionNondegenerate

namespace Omega.Conclusion

/-- Concrete good-prime one-step Hankel completion data.  The field `d_eq_one` records that this
Lean seed is the one-minor finite-field completion supplied by the existing nondegenerate Hankel
theorem. -/
structure conclusion_goodprime_random_completion_unique_extension_data where
  p : ℕ
  prime : Nat.Prime p
  d : ℕ
  d_eq_one : d = 1
  a0 : ZMod p
  a1 : ZMod p
  leadingNonzero : a0 ≠ 0

/-- The displayed success lower bound for the concrete one-step good-prime completion package. -/
noncomputable def conclusion_goodprime_random_completion_unique_extension_successLowerBound
    (D : conclusion_goodprime_random_completion_unique_extension_data) : ℚ :=
  1 - (D.d : ℚ) / (D.p : ℚ)

/-- Concrete statement for `cor:conclusion-goodprime-random-completion-unique-extension`. -/
def conclusion_goodprime_random_completion_unique_extension_statement
    (D : conclusion_goodprime_random_completion_unique_extension_data) : Prop :=
  letI : Fact D.p.Prime := ⟨D.prime⟩
  Omega.Zeta.hankelSeedFailureProbabilityBound D.a0 D.a1 ∧
    Omega.Zeta.hankelSeedUniqueExtensionOnNonvanishingLocus D.a0 D.a1 ∧
    conclusion_goodprime_random_completion_unique_extension_successLowerBound D =
      1 - (1 : ℚ) / (D.p : ℚ) ∧
    0 ≤ conclusion_goodprime_random_completion_unique_extension_successLowerBound D

/-- Paper label: `cor:conclusion-goodprime-random-completion-unique-extension`. -/
theorem paper_conclusion_goodprime_random_completion_unique_extension
    (D : conclusion_goodprime_random_completion_unique_extension_data) :
    conclusion_goodprime_random_completion_unique_extension_statement D := by
  letI : Fact D.p.Prime := ⟨D.prime⟩
  have hbase :=
    Omega.Zeta.paper_xi_hankel_finitefield_random_completion_nondegenerate D.a0 D.a1
      D.leadingNonzero
  have hsuccess :
      conclusion_goodprime_random_completion_unique_extension_successLowerBound D =
        1 - (1 : ℚ) / (D.p : ℚ) := by
    simp [conclusion_goodprime_random_completion_unique_extension_successLowerBound, D.d_eq_one]
  have hnonneg :
      0 ≤ conclusion_goodprime_random_completion_unique_extension_successLowerBound D := by
    rw [hsuccess]
    have hp_one : (1 : ℚ) ≤ (D.p : ℚ) := by
      exact_mod_cast (le_trans (by decide : 1 ≤ 2) D.prime.two_le)
    have hinv_le_one : (1 : ℚ) / (D.p : ℚ) ≤ 1 := by
      have h := one_div_le_one_div_of_le (show (0 : ℚ) < 1 by norm_num) hp_one
      simpa using h
    linarith
  exact ⟨hbase.1, hbase.2, hsuccess, hnonneg⟩

end Omega.Conclusion
