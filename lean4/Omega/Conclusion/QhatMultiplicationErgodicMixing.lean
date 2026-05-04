import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete multiplier data for the Fourier-character criterion on `Qhat`. -/
structure conclusion_qhat_multiplication_ergodic_mixing_data where
  conclusion_qhat_multiplication_ergodic_mixing_multiplier : ℕ
  conclusion_qhat_multiplication_ergodic_mixing_multiplier_ge_two :
    2 ≤ conclusion_qhat_multiplication_ergodic_mixing_multiplier

namespace conclusion_qhat_multiplication_ergodic_mixing_data

/-- Nonzero integer characters are not fixed by multiplication by `n >= 2`. -/
def ergodic (D : conclusion_qhat_multiplication_ergodic_mixing_data) : Prop :=
  ∀ k : ℤ, k ≠ 0 →
    k * (D.conclusion_qhat_multiplication_ergodic_mixing_multiplier : ℤ) ≠ k

/-- Each nonzero character orbit separates from every prescribed Fourier character. -/
def strongMixing (D : conclusion_qhat_multiplication_ergodic_mixing_data) : Prop :=
  ∀ a b : ℤ, a ≠ 0 →
    ∃ t : ℕ,
      a * (D.conclusion_qhat_multiplication_ergodic_mixing_multiplier : ℤ) ^ t ≠ b

/-- The packaged Birkhoff conclusion for constant observables. -/
def birkhoffConclusion (_D : conclusion_qhat_multiplication_ergodic_mixing_data) : Prop :=
  ∀ c : ℚ, ∀ N : ℕ, 0 < N →
    ((Finset.range N).sum fun _ => c) / (N : ℚ) = c

end conclusion_qhat_multiplication_ergodic_mixing_data

open conclusion_qhat_multiplication_ergodic_mixing_data

/-- Paper label: `thm:conclusion-qhat-multiplication-ergodic-mixing`. -/
theorem paper_conclusion_qhat_multiplication_ergodic_mixing
    (D : conclusion_qhat_multiplication_ergodic_mixing_data) :
    D.ergodic ∧ D.strongMixing ∧ D.birkhoffConclusion := by
  have hmul_ne_one :
      (D.conclusion_qhat_multiplication_ergodic_mixing_multiplier : ℤ) ≠ 1 := by
    have hgt :
        (1 : ℤ) < D.conclusion_qhat_multiplication_ergodic_mixing_multiplier := by
      exact_mod_cast Nat.lt_of_succ_le
        D.conclusion_qhat_multiplication_ergodic_mixing_multiplier_ge_two
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro k hk hfix
    have hprod :
        k * ((D.conclusion_qhat_multiplication_ergodic_mixing_multiplier : ℤ) - 1) = 0 := by
      rw [mul_sub, mul_one, hfix, sub_self]
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hprod with hzero | hone
    · exact hk hzero
    · exact hmul_ne_one (by omega)
  · intro a b ha
    by_cases hab : a = b
    · refine ⟨1, ?_⟩
      simpa [hab, pow_one] using
        (show a * (D.conclusion_qhat_multiplication_ergodic_mixing_multiplier : ℤ) ≠ a from
          (by
            intro hfix
            have hprod :
                a *
                    ((D.conclusion_qhat_multiplication_ergodic_mixing_multiplier : ℤ) - 1) =
                  0 := by
              rw [mul_sub, mul_one, hfix, sub_self]
            rcases eq_zero_or_eq_zero_of_mul_eq_zero hprod with hzero | hone
            · exact ha hzero
            · exact hmul_ne_one (by omega)))
    · refine ⟨0, ?_⟩
      simpa using hab
  · intro c N hN
    have hN_ne : (N : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hN
    simp [Finset.sum_const, nsmul_eq_mul, hN_ne]

end Omega.Conclusion
