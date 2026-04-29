import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.CircleDimension.PoissonBivariateFdivFourthOrderComplexM2

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-poisson-bivariate-quartic-null-cone-covariance-balance`.
The quartic null cone is exactly the covariance-balance plane, equivalently the vanishing of the
complex second moment `m₂ = A + 2 B i`. -/
theorem paper_conclusion_poisson_bivariate_quartic_null_cone_covariance_balance
    (sigmaGamma2 sigmaDelta2 sigmaGammaDelta : Real) :
    let A := sigmaGamma2 - sigmaDelta2
    let B := sigmaGammaDelta
    let m2 : Complex := Complex.ofReal A + Complex.ofReal (2 * B) * Complex.I
    (Omega.CircleDimension.poissonBivariateFourthOrderQuadraticInvariant
        sigmaGamma2 sigmaDelta2 sigmaGammaDelta = 0 ↔ A = 0 ∧ B = 0) ∧
      ((A = 0 ∧ B = 0) ↔ m2 = 0) := by
  dsimp
  constructor
  · constructor
    · intro hInv
      have hrewrite :=
        Omega.CircleDimension.paper_cdim_poisson_bivariate_fdiv_fourth_order_complex_m2
          8 sigmaGamma2 sigmaDelta2 sigmaGammaDelta
      have hsum :
          (sigmaGamma2 - sigmaDelta2) ^ 2 + (2 * sigmaGammaDelta) ^ 2 = 0 := by
        nlinarith [hInv, hrewrite]
      have hA_sq : (sigmaGamma2 - sigmaDelta2) ^ 2 = 0 := by
        nlinarith [sq_nonneg (sigmaGamma2 - sigmaDelta2), sq_nonneg (2 * sigmaGammaDelta), hsum]
      have hB_sq : sigmaGammaDelta ^ 2 = 0 := by
        nlinarith [sq_nonneg (sigmaGamma2 - sigmaDelta2), sq_nonneg sigmaGammaDelta, hsum]
      constructor
      · nlinarith
      · nlinarith
    · rintro ⟨hA, hB⟩
      simp [Omega.CircleDimension.poissonBivariateFourthOrderQuadraticInvariant, hA, hB]
  · constructor
    · rintro ⟨hA, hB⟩
      simp [hA, hB]
    · intro hm2
      have hA : sigmaGamma2 - sigmaDelta2 = 0 := by
        simpa using congrArg Complex.re hm2
      have h2B : 2 * sigmaGammaDelta = 0 := by
        simpa using congrArg Complex.im hm2
      constructor
      · exact hA
      · linarith

end Omega.Conclusion
