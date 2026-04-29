import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.BinfoldEscortCsiszarBlackwellPhi
import Omega.Conclusion.TwoAtomScalarRecoveryAlpha2

namespace Omega.Conclusion

noncomputable section

/-- Paper label: `thm:conclusion-chi2-linear-recovers-phi`. Specializing the closed `α = 2`
formula gives the baseline `χ²` scalar, rewriting `φ^3` with `φ^2 = φ + 1` makes that scalar
linear in `φ`, and solving the resulting affine equation recovers the golden ratio. -/
theorem paper_conclusion_chi2_linear_recovers_phi :
    BinfoldEscortCsiszarBlackwellPhiDatum.chi2UniformBaseline =
      (2 * Real.goldenRatio - 3) / 5 ∧
      Real.goldenRatio =
        (5 * BinfoldEscortCsiszarBlackwellPhiDatum.chi2UniformBaseline + 3) / 2 := by
  have hchi2_closed :
      BinfoldEscortCsiszarBlackwellPhiDatum.chi2UniformBaseline =
        (Real.goldenRatio ^ 3 + 1) / 5 - 1 := by
    rw [BinfoldEscortCsiszarBlackwellPhiDatum.chi2UniformBaseline, twoAtomScalar2_goldenRatio]
  have hphi_cube : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    nlinarith [Real.goldenRatio_sq]
  have hlinear :
      BinfoldEscortCsiszarBlackwellPhiDatum.chi2UniformBaseline =
        (2 * Real.goldenRatio - 3) / 5 := by
    rw [hchi2_closed]
    nlinarith [hphi_cube]
  refine ⟨hlinear, ?_⟩
  nlinarith [hlinear]

end

end Omega.Conclusion
