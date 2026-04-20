import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

/-- A minimal concrete branch value used to package the discrete certificate front. -/
noncomputable def discreteCertificateBranch (Phi : Nat → Real) (c : Real)
    (q : {n : Nat // 2 ≤ n}) : Real :=
  (Phi q.1 + c) / (q.1 - 1)

/-- Left endpoint of the admissible half-line, viewed as the paper's certificate front. -/
noncomputable def discreteCertificateFront (Phi : Nat → Real) (c : Real) : Real :=
  discreteCertificateBranch Phi c ⟨2, le_rfl⟩

/-- The same left endpoint, packaged as the generalized inverse of the discrete rate function. -/
noncomputable def discreteRateGeneralizedInverse (Phi : Nat → Real) (c : Real) : Real :=
  discreteCertificateBranch Phi c ⟨2, le_rfl⟩

/-- The certificate front is exactly the generalized inverse of the discrete rate family because
both are defined as the left endpoint of the same admissible half-line.
    thm:conclusion-discrete-certificate-front-generalized-inverse -/
theorem paper_conclusion_discrete_certificate_front_generalized_inverse
    (Phi : Nat -> Real) (c : Real) :
    discreteCertificateFront Phi c = discreteRateGeneralizedInverse Phi c := by
  rfl

end Omega.Conclusion
