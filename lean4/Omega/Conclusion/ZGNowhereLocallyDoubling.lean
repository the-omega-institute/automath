import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete dyadic mass data for the ZG nowhere-local-doubling obstruction. The sequence
`mass n` records the mass seen at radius `2^{-n}` around a fixed local point, and the
obstruction says that every polynomial lower bound forced by a doubling constant is eventually
violated by the zero local-dimension scale. -/
structure conclusion_zg_nowhere_locally_doubling_data where
  conclusion_zg_nowhere_locally_doubling_mass : ℕ → ℝ
  conclusion_zg_nowhere_locally_doubling_zero_dimension_obstruction :
    ∀ C : ℝ, 1 ≤ C →
      ∃ n : ℕ,
        conclusion_zg_nowhere_locally_doubling_mass 0 >
          C ^ n * conclusion_zg_nowhere_locally_doubling_mass n

namespace conclusion_zg_nowhere_locally_doubling_data

/-- A local doubling certificate along the dyadic scale. -/
def conclusion_zg_nowhere_locally_doubling_local_doubling
    (D : conclusion_zg_nowhere_locally_doubling_data) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ n : ℕ,
      D.conclusion_zg_nowhere_locally_doubling_mass n ≤
        C * D.conclusion_zg_nowhere_locally_doubling_mass (n + 1)

/-- Nowhere-local-doubling is the nonexistence of a dyadic local doubling certificate. -/
def nowhere_locally_doubling
    (D : conclusion_zg_nowhere_locally_doubling_data) : Prop :=
  ¬ D.conclusion_zg_nowhere_locally_doubling_local_doubling

lemma conclusion_zg_nowhere_locally_doubling_iterate
    (D : conclusion_zg_nowhere_locally_doubling_data) (C : ℝ) (hC : 1 ≤ C)
    (hstep :
      ∀ n : ℕ,
        D.conclusion_zg_nowhere_locally_doubling_mass n ≤
          C * D.conclusion_zg_nowhere_locally_doubling_mass (n + 1)) :
    ∀ n : ℕ,
      D.conclusion_zg_nowhere_locally_doubling_mass 0 ≤
        C ^ n * D.conclusion_zg_nowhere_locally_doubling_mass n := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hCnonneg : 0 ≤ C := by linarith
      have hpow_nonneg : 0 ≤ C ^ n := pow_nonneg hCnonneg n
      have hmul :
          C ^ n * D.conclusion_zg_nowhere_locally_doubling_mass n ≤
            C ^ n * (C * D.conclusion_zg_nowhere_locally_doubling_mass (n + 1)) :=
        mul_le_mul_of_nonneg_left (hstep n) hpow_nonneg
      calc
        D.conclusion_zg_nowhere_locally_doubling_mass 0
            ≤ C ^ n * D.conclusion_zg_nowhere_locally_doubling_mass n := ih
        _ ≤ C ^ n * (C * D.conclusion_zg_nowhere_locally_doubling_mass (n + 1)) :=
            hmul
        _ = C ^ (n + 1) *
              D.conclusion_zg_nowhere_locally_doubling_mass (n + 1) := by
            ring

end conclusion_zg_nowhere_locally_doubling_data

open conclusion_zg_nowhere_locally_doubling_data

/-- Paper label: `thm:conclusion-zg-nowhere-locally-doubling`. A local doubling certificate
iterates to a polynomial lower bound at every dyadic scale, contradicting the packaged
zero local-dimension obstruction. -/
theorem paper_conclusion_zg_nowhere_locally_doubling
    (D : conclusion_zg_nowhere_locally_doubling_data) : D.nowhere_locally_doubling := by
  rintro ⟨C, hC, hstep⟩
  rcases D.conclusion_zg_nowhere_locally_doubling_zero_dimension_obstruction C hC with
    ⟨n, hn⟩
  have hbound :=
    D.conclusion_zg_nowhere_locally_doubling_iterate C hC hstep n
  exact not_lt_of_ge hbound hn

end Omega.Conclusion
