import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

/-- Concrete finite CMV certificate data for Padé--Hardy freezing.  `taylorCoeff L k` is the
`k`-th Taylor coefficient seen at certificate level `L`, and `padeCode L` records the unique
`[M/N]` Padé approximant determined by the stabilized coefficient window. -/
structure conclusion_finite_cmv_certificate_pade_hardy_freezing_data where
  M : ℕ
  N : ℕ
  taylorCoeff : ℕ → ℕ → ℝ
  padeCode : ℕ → ℕ
  zeroCount : ℕ → ℕ
  poleCount : ℕ → ℕ
  coefficient_stabilizes :
    ∃ Lstar : ℕ, ∀ L, Lstar ≤ L → ∀ k, k ≤ M + N → taylorCoeff L k = taylorCoeff (M + N) k
  pade_unique_from_coefficients :
    ∀ L, (∀ k, k ≤ M + N → taylorCoeff L k = taylorCoeff (M + N) k) →
      padeCode L = padeCode (M + N)
  zero_pole_counts_from_pade :
    ∀ L, padeCode L = padeCode (M + N) →
      zeroCount L = zeroCount (M + N) ∧ poleCount L = poleCount (M + N)

namespace conclusion_finite_cmv_certificate_pade_hardy_freezing_data

/-- From some finite certificate level on, the Padé construction receives the same coefficient
window and therefore returns the same rational approximant. -/
def eventually_pade_equal
    (D : conclusion_finite_cmv_certificate_pade_hardy_freezing_data) : Prop :=
  ∃ Lstar : ℕ, ∀ L, Lstar ≤ L → D.padeCode L = D.padeCode (D.M + D.N)

/-- Local zero and pole counts freeze once the Padé approximant has frozen. -/
def eventually_zero_pole_counts_freeze
    (D : conclusion_finite_cmv_certificate_pade_hardy_freezing_data) : Prop :=
  ∃ Lstar : ℕ, ∀ L, Lstar ≤ L →
    D.zeroCount L = D.zeroCount (D.M + D.N) ∧
      D.poleCount L = D.poleCount (D.M + D.N)

end conclusion_finite_cmv_certificate_pade_hardy_freezing_data

/-- Paper label: `thm:conclusion-finite-cmv-certificate-pade-hardy-freezing`. -/
theorem paper_conclusion_finite_cmv_certificate_pade_hardy_freezing
    (D : conclusion_finite_cmv_certificate_pade_hardy_freezing_data) :
    D.eventually_pade_equal ∧ D.eventually_zero_pole_counts_freeze := by
  rcases D.coefficient_stabilizes with ⟨Lstar, hstable⟩
  refine ⟨⟨Lstar, ?_⟩, ⟨Lstar, ?_⟩⟩
  · intro L hL
    exact D.pade_unique_from_coefficients L (hstable L hL)
  · intro L hL
    exact D.zero_pole_counts_from_pade L (D.pade_unique_from_coefficients L (hstable L hL))

end Omega.Conclusion
