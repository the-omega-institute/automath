import Mathlib.Tactic
import Omega.Zeta.AdamsBinomialProbeFourierDiagonalization

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Paper label: `thm:conclusion-single-adams-phase-profile-arithmetic-fourier-microscope`. -/
theorem paper_conclusion_single_adams_phase_profile_arithmetic_fourier_microscope
    (N d : ℕ) (c : ℤ → ℂ) :
    (∀ ω : ℂˣ,
      Omega.Zeta.adamsBinomialProbeFourierSeries N d c ω =
        Finset.sum (Finset.Icc (-(N : ℤ)) N) fun m =>
          Omega.Zeta.adamsBinomialProbeFourierCoeff N d c m * ((ω : ℂ) ^ m)) ∧
      (∀ m : ℤ, m ∈ Finset.Icc (-(N : ℤ)) N →
        c (-(d : ℤ) * m) =
          ((-1 : ℂ) ^ Int.natAbs m) *
            (((4 : ℂ) ^ N) /
              (Nat.choose (2 * N) (Omega.Zeta.adamsBinomialProbeCenteredIndex N m) : ℂ)) *
              Omega.Zeta.adamsBinomialProbeFourierCoeff N d c m) := by
  have hdiag := Omega.Zeta.paper_xi_adams_binomial_probe_fourier_diagonalization N d c
  exact ⟨fun ω => rfl, hdiag.2.2⟩

end

end Omega.Conclusion
