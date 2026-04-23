import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.POM.DerivedMaxNoncontractibleFiberDefectConstants

namespace Omega.DerivedConsequences

/-- The ratio `\widetilde D_m / D_m` stays uniformly between positive constants on both parity
branches, so passing to the noncontractible sector does not change the exponential growth rate.
    cor:derived-max-noncontractible-fiber-no-exponential-penalty -/
theorem paper_derived_max_noncontractible_fiber_no_exponential_penalty :
    ∃ c C : ℚ,
      0 < c ∧
      c ≤ C ∧
      (∀ k : ℕ,
        9 ≤ k →
          c ≤ (Omega.Conclusion.noncontractibleFiberCount (2 * k) : ℚ) /
                Omega.Conclusion.noncontractibleMainFiberCount (2 * k) ∧
            (Omega.Conclusion.noncontractibleFiberCount (2 * k) : ℚ) /
                Omega.Conclusion.noncontractibleMainFiberCount (2 * k) ≤ C) ∧
      (∀ k : ℕ,
        8 ≤ k →
          c ≤ (Omega.Conclusion.noncontractibleFiberCount (2 * k + 1) : ℚ) /
                Omega.Conclusion.noncontractibleMainFiberCount (2 * k + 1) ∧
            (Omega.Conclusion.noncontractibleFiberCount (2 * k + 1) : ℚ) /
                Omega.Conclusion.noncontractibleMainFiberCount (2 * k + 1) ≤ C) ∧
      Real.log (Real.sqrt Real.goldenRatio) = (1 / 2 : ℝ) * Real.log Real.goldenRatio := by
  refine ⟨(1 / 2 : ℚ), 1, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · intro k hk
    rcases Omega.POM.paper_derived_max_noncontractible_fiber_defect_constants with ⟨heven, _⟩
    have hratio := heven k hk
    constructor
    · by_cases hmod : k % 3 = 1
      · rw [hratio, if_pos hmod]
        have hdouble : 2 * Nat.fib (k - 3) ≤ Nat.fib (k + 2) := by
          have hstep₁ : Nat.fib (k - 1) ≤ Nat.fib (k + 2) := Nat.fib_mono (by omega)
          have hstep₂ : 2 * Nat.fib (k - 3) ≤ Nat.fib (k - 1) := by
            have hmono : Nat.fib (k - 3) ≤ Nat.fib (k - 2) := Nat.fib_mono (by omega)
            have hfib : Nat.fib (k - 1) = Nat.fib (k - 3) + Nat.fib (k - 2) := by
              simpa [show k - 3 + 1 = k - 2 by omega, show k - 3 + 2 = k - 1 by omega] using
                (Nat.fib_add_two (n := k - 3))
            calc
              2 * Nat.fib (k - 3) = Nat.fib (k - 3) + Nat.fib (k - 3) := by ring
              _ ≤ Nat.fib (k - 3) + Nat.fib (k - 2) := Nat.add_le_add_left hmono _
              _ = Nat.fib (k - 1) := hfib.symm
          exact le_trans hstep₂ hstep₁
        have hden_pos : 0 < (Nat.fib (k + 2) : ℚ) := by
          exact_mod_cast Nat.fib_pos.mpr (by omega)
        have hdiv : (Nat.fib (k - 3) : ℚ) / Nat.fib (k + 2) ≤ 1 / 2 := by
          apply (div_le_iff₀ hden_pos).2
          have hdouble' : (2 * Nat.fib (k - 3) : ℚ) ≤ Nat.fib (k + 2) := by
            exact_mod_cast hdouble
          linarith
        linarith
      · rw [hratio, if_neg hmod]
        norm_num
    · by_cases hmod : k % 3 = 1
      · rw [hratio, if_pos hmod]
        have hdiv_nonneg : 0 ≤ (Nat.fib (k - 3) : ℚ) / Nat.fib (k + 2) := by positivity
        linarith
      · simp [hratio, if_neg hmod]
  · intro k hk
    rcases Omega.POM.paper_derived_max_noncontractible_fiber_defect_constants with ⟨_, hodd⟩
    have hratio := hodd k hk
    constructor
    · by_cases hmod : k % 3 = 1
      · rw [hratio, if_pos hmod]
        have hsum_le : Nat.fib (k - 8) + Nat.fib (k - 4) ≤ Nat.fib (k + 1) := by
          have hmono₁ : Nat.fib (k - 8) ≤ Nat.fib (k - 4) := Nat.fib_mono (by omega)
          have hdouble : 2 * Nat.fib (k - 4) ≤ Nat.fib (k + 1) := by
            have hstep₁ : Nat.fib (k - 2) ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
            have hstep₂ : 2 * Nat.fib (k - 4) ≤ Nat.fib (k - 2) := by
              have hmono₂ : Nat.fib (k - 4) ≤ Nat.fib (k - 3) := Nat.fib_mono (by omega)
              have hfib : Nat.fib (k - 2) = Nat.fib (k - 4) + Nat.fib (k - 3) := by
                simpa [show k - 4 + 1 = k - 3 by omega, show k - 4 + 2 = k - 2 by omega] using
                  (Nat.fib_add_two (n := k - 4))
              calc
                2 * Nat.fib (k - 4) = Nat.fib (k - 4) + Nat.fib (k - 4) := by ring
                _ ≤ Nat.fib (k - 4) + Nat.fib (k - 3) := Nat.add_le_add_left hmono₂ _
                _ = Nat.fib (k - 2) := hfib.symm
            exact le_trans hstep₂ hstep₁
          calc
            Nat.fib (k - 8) + Nat.fib (k - 4) ≤ Nat.fib (k - 4) + Nat.fib (k - 4) := by
              exact Nat.add_le_add_right hmono₁ _
            _ = 2 * Nat.fib (k - 4) := by ring
            _ ≤ Nat.fib (k + 1) := hdouble
        have hden_pos : 0 < 2 * (Nat.fib (k + 1) : ℚ) := by
          have hfib : 0 < (Nat.fib (k + 1) : ℚ) := by
            exact_mod_cast Nat.fib_pos.mpr (by omega)
          positivity
        have hdiv :
            ((Nat.fib (k - 4) + Nat.fib (k - 8) : ℚ) / (2 * Nat.fib (k + 1))) ≤ 1 / 2 := by
          apply (div_le_iff₀ hden_pos).2
          have hsum_le_nat : Nat.fib (k - 4) + Nat.fib (k - 8) ≤ Nat.fib (k + 1) := by
            simpa [add_comm] using hsum_le
          have hsum_le' : (Nat.fib (k - 4) + Nat.fib (k - 8) : ℚ) ≤ (Nat.fib (k + 1) : ℚ) := by
            exact_mod_cast hsum_le_nat
          norm_num
          linarith
        linarith
      · rw [hratio, if_neg hmod]
        have hmono : Nat.fib (k - 4) ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
        have hden_pos : 0 < 2 * (Nat.fib (k + 1) : ℚ) := by
          have hfib : 0 < (Nat.fib (k + 1) : ℚ) := by
            exact_mod_cast Nat.fib_pos.mpr (by omega)
          positivity
        have hdiv : (Nat.fib (k - 4) : ℚ) / (2 * Nat.fib (k + 1)) ≤ 1 / 2 := by
          apply (div_le_iff₀ hden_pos).2
          have hmono' : (Nat.fib (k - 4) : ℚ) ≤ (Nat.fib (k + 1) : ℚ) := by
            exact_mod_cast hmono
          norm_num
          linarith
        linarith
    · by_cases hmod : k % 3 = 1
      · rw [hratio, if_pos hmod]
        have hdiv_nonneg :
            0 ≤ (Nat.fib (k - 4) + Nat.fib (k - 8) : ℚ) / (2 * Nat.fib (k + 1)) := by
          positivity
        linarith
      · rw [hratio, if_neg hmod]
        have hdiv_nonneg : 0 ≤ (Nat.fib (k - 4) : ℚ) / (2 * Nat.fib (k + 1)) := by positivity
        linarith
  · rw [Real.log_sqrt (le_of_lt Real.goldenRatio_pos)]
    ring

end Omega.DerivedConsequences
