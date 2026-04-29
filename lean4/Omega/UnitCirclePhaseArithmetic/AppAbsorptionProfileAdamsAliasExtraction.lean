import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.AbsorptionProfileFourierNewtonIdentifiability

namespace Omega.UnitCirclePhaseArithmetic

open scoped BigOperators

noncomputable section

/-- The base Fourier coefficient of the finite absorption profile. -/
def app_absorption_profile_adams_alias_extraction_base_coeff (roots : List ℂ) (n : ℕ) : ℂ :=
  absorptionProfileFourierCoeff roots n

/-- Finite coefficient extractor for the Adams-rescaled profile `m * Φ(mθ)`. -/
def app_absorption_profile_adams_alias_extraction_rescaled_coeff
    (roots : List ℂ) (m n : ℕ) : ℂ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    if m * k = n then
      (m : ℂ) * app_absorption_profile_adams_alias_extraction_base_coeff roots k
    else
      0

/-- Paper label: `cor:app-absorption-profile-adams-alias-extraction`. The finite coefficient
extractor for `m * Φ(mθ)` has exactly one surviving term when `m ∣ n`, namely the coefficient
with index `n / m`; if `m ∤ n`, every candidate term vanishes. -/
theorem paper_app_absorption_profile_adams_alias_extraction
    (roots : List ℂ) (m n : ℕ) (hm : 0 < m) :
    (m ∣ n →
      app_absorption_profile_adams_alias_extraction_rescaled_coeff roots m n =
        (m : ℂ) * app_absorption_profile_adams_alias_extraction_base_coeff roots (n / m)) ∧
    (¬ m ∣ n → app_absorption_profile_adams_alias_extraction_rescaled_coeff roots m n = 0) := by
  refine ⟨?_, ?_⟩
  · intro hmn
    obtain ⟨q, rfl⟩ := hmn
    have hq_mem : q ∈ Finset.range (m * q + 1) := by
      refine Finset.mem_range.mpr ?_
      have hm1 : 1 ≤ m := Nat.succ_le_of_lt hm
      have hq_le : q ≤ m * q := by
        calc
          q = 1 * q := by simp
          _ ≤ m * q := Nat.mul_le_mul_right q hm1
      exact Nat.lt_succ_of_le hq_le
    unfold app_absorption_profile_adams_alias_extraction_rescaled_coeff
    rw [Finset.sum_eq_single q]
    · have hdiv : (m * q) / m = q := by
        simpa [Nat.mul_comm] using Nat.mul_div_right q hm
      rw [hdiv]
      simp [app_absorption_profile_adams_alias_extraction_base_coeff]
    · intro k hk hkq
      by_cases hmk : m * k = m * q
      · have : k = q := Nat.eq_of_mul_eq_mul_left hm hmk
        exact (hkq this).elim
      · simp [hmk]
    · intro hq
      exact (hq hq_mem).elim
  · intro hmn
    unfold app_absorption_profile_adams_alias_extraction_rescaled_coeff
    refine Finset.sum_eq_zero ?_
    intro k hk
    by_cases hkn : m * k = n
    · exact False.elim (hmn ⟨k, hkn.symm⟩)
    · simp [hkn]

end

end Omega.UnitCirclePhaseArithmetic
