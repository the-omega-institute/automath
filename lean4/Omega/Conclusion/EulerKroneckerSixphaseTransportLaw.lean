import Omega.Conclusion.EulerKroneckerThreepointTransportSpectrum

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-euler-kronecker-sixphase-transport-law`. -/
theorem paper_conclusion_euler_kronecker_sixphase_transport_law :
    (∀ n : ℕ,
        n % 6 = 0 ∨ n % 6 = 2 →
        conclusion_euler_kronecker_threepoint_transport_spectrum_transport_constant n = 1 / 3) ∧
      (∀ n : ℕ,
        n % 6 = 1 ∨ n % 6 = 4 →
        conclusion_euler_kronecker_threepoint_transport_spectrum_transport_constant n = 1 / 2) ∧
      (∀ n : ℕ,
        n % 6 = 3 ∨ n % 6 = 5 →
        conclusion_euler_kronecker_threepoint_transport_spectrum_transport_constant n = 3 / 4) := by
  rcases paper_conclusion_euler_kronecker_threepoint_transport_spectrum with
    ⟨h0, h1, h2, _, _, _, _, _⟩
  exact ⟨h0, h1, h2⟩

end Omega.Conclusion
