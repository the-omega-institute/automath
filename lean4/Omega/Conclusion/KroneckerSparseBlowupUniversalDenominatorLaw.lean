import Mathlib.Tactic
import Omega.Conclusion.EulerKroneckerThreepointTransportSpectrum

namespace Omega.Conclusion

/-- Concrete sparse-blowup denominator package: the already-defined blowup coefficient is
`0` on the `1 mod 3` branch and `1 / 2` on the remaining two branches, so its range is exactly
`{0, 1 / 2}`. -/
def conclusion_kronecker_sparse_blowup_universal_denominator_law_statement : Prop :=
  (∀ n : ℕ,
      n % 3 = 0 ∨ n % 3 = 2 →
      conclusion_euler_kronecker_threepoint_transport_spectrum_blowup_coeff n = 1 / 2) ∧
    (∀ n : ℕ,
      n % 3 = 1 →
      conclusion_euler_kronecker_threepoint_transport_spectrum_blowup_coeff n = 0) ∧
    Set.range conclusion_euler_kronecker_threepoint_transport_spectrum_blowup_coeff =
      ({0, 1 / 2} : Set ℚ)

/-- Paper label: `thm:conclusion-kronecker-sparse-blowup-universal-denominator-law`. -/
theorem paper_conclusion_kronecker_sparse_blowup_universal_denominator_law :
    conclusion_kronecker_sparse_blowup_universal_denominator_law_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rcases hn with h0 | h2
    · simp [conclusion_euler_kronecker_threepoint_transport_spectrum_blowup_coeff, h0]
    · simp [conclusion_euler_kronecker_threepoint_transport_spectrum_blowup_coeff, h2]
  · intro n h1
    simp [conclusion_euler_kronecker_threepoint_transport_spectrum_blowup_coeff, h1]
  · ext x
    constructor
    · rintro ⟨n, rfl⟩
      have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases hcases with h0 | h1 | h2
      · simp [conclusion_euler_kronecker_threepoint_transport_spectrum_blowup_coeff, h0]
      · simp [conclusion_euler_kronecker_threepoint_transport_spectrum_blowup_coeff, h1]
      · simp [conclusion_euler_kronecker_threepoint_transport_spectrum_blowup_coeff, h2]
    · intro hx
      rcases hx with rfl | rfl
      · exact ⟨1, by simp [conclusion_euler_kronecker_threepoint_transport_spectrum_blowup_coeff]⟩
      · exact ⟨0, by simp [conclusion_euler_kronecker_threepoint_transport_spectrum_blowup_coeff]⟩

end Omega.Conclusion
