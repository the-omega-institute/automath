import Omega.Conclusion.RankoneResultantDiscriminantClosedForm

namespace Omega.Conclusion

/-- Concrete rank-one package for the two branch speeds attached to the same resultant/discriminant
data. -/
structure conclusion_rankone_eigenvalue_speed_discriminant_identity_data (n : Nat) where
  resultantData : RankoneResultantData n

namespace conclusion_rankone_eigenvalue_speed_discriminant_identity_data

/-- The `λ`-branch speed written as the reciprocal Cauchy secant factor. -/
noncomputable def conclusion_rankone_eigenvalue_speed_discriminant_identity_lam_speed {n : Nat}
    (D : conclusion_rankone_eigenvalue_speed_discriminant_identity_data n) : ℝ :=
  1 / rankoneCauchySecant D.resultantData.D0 D.resultantData.g D.resultantData.lam

/-- The `μ`-branch speed written as the reciprocal Cauchy secant factor. -/
noncomputable def conclusion_rankone_eigenvalue_speed_discriminant_identity_mu_speed {n : Nat}
    (D : conclusion_rankone_eigenvalue_speed_discriminant_identity_data n) : ℝ :=
  1 / rankoneCauchySecant D.resultantData.D0 D.resultantData.g D.resultantData.mu

/-- The two reciprocal secant speeds both equal the coupling parameter, and the same package
identifies the resultant and discriminant closed forms. -/
def speed_discriminant_identity {n : Nat}
    (D : conclusion_rankone_eigenvalue_speed_discriminant_identity_data n) : Prop :=
  D.conclusion_rankone_eigenvalue_speed_discriminant_identity_lam_speed = D.resultantData.b ∧
    D.conclusion_rankone_eigenvalue_speed_discriminant_identity_mu_speed = D.resultantData.b ∧
    rankoneResultantClosedForm D.resultantData = rankoneDiscriminantClosedForm D.resultantData

end conclusion_rankone_eigenvalue_speed_discriminant_identity_data

/-- Paper label: `cor:conclusion-rankone-eigenvalue-speed-discriminant-identity`. The reciprocal
secant formulas recover the two branch speeds, and the existing resultant/discriminant closed form
provides the final identity. -/
theorem paper_conclusion_rankone_eigenvalue_speed_discriminant_identity {n : Nat}
    (D : conclusion_rankone_eigenvalue_speed_discriminant_identity_data n) :
    D.speed_discriminant_identity := by
  have hClosed := paper_conclusion_rankone_resultant_discriminant_closed_form D.resultantData
  dsimp [conclusion_rankone_eigenvalue_speed_discriminant_identity_data.speed_discriminant_identity]
  refine ⟨?_, ?_, hClosed.2.2.2⟩
  · change 1 / rankoneCauchySecant D.resultantData.D0 D.resultantData.g D.resultantData.lam =
      D.resultantData.b
    simp [D.resultantData.hlam]
  · change 1 / rankoneCauchySecant D.resultantData.D0 D.resultantData.g D.resultantData.mu =
      D.resultantData.b
    simp [D.resultantData.hmu]

end Omega.Conclusion
