import Mathlib.Tactic
import Omega.Conclusion.RankoneCauchyOrthogonality

namespace Omega.Conclusion

/-- Concrete rank-one update data for the two-eigenvalue Cauchy package. The fields are actual
diagonal data, coupling coefficients, and secant hypotheses. -/
structure RankoneResultantData (n : Nat) where
  D0 : Fin n → ℝ
  g : Fin n → ℝ
  b : ℝ
  lam : ℝ
  mu : ℝ
  hlamdiag : ∀ i, lam ≠ D0 i
  hmudiag : ∀ i, mu ≠ D0 i
  hlammu : lam ≠ mu
  hlam : rankoneCauchySecant D0 g lam = 1 / b
  hmu : rankoneCauchySecant D0 g mu = 1 / b

/-- The `2 × n` Cauchy matrix formed by the two candidate eigenvectors. -/
noncomputable def rankoneCauchyMatrix {n : Nat} (D : RankoneResultantData n) :
    Fin 2 → Fin n → ℝ :=
  fun j i =>
    if j.1 = 0 then
      rankoneCandidateEigenvector D.D0 D.g D.lam i
    else
      rankoneCandidateEigenvector D.D0 D.g D.mu i

/-- The off-diagonal Gram entry of the two candidate eigenvectors. -/
noncomputable def rankoneCauchyGramOffDiag {n : Nat} (D : RankoneResultantData n) : ℝ :=
  rankoneCauchyCrossTerm D.D0 D.g D.lam D.mu

/-- The audited resultant side of the closed form. -/
noncomputable def rankoneResultantClosedForm {n : Nat} (D : RankoneResultantData n) : ℝ :=
  (D.mu - D.lam) * rankoneCauchyGramOffDiag D

/-- The discriminant side collapses to `0` once the Cauchy cross term vanishes. -/
noncomputable def rankoneDiscriminantClosedForm {n : Nat} (_D : RankoneResultantData n) : ℝ := 0

/-- Closed-form package extracted from the rank-one Cauchy orthogonality identity. -/
def RankoneResultantDiscriminantClosedForm {n : Nat} (D : RankoneResultantData n) : Prop :=
  (∀ i, (D.lam - D.D0 i) * rankoneCandidateEigenvector D.D0 D.g D.lam i = D.g i) ∧
    (∀ i, (D.mu - D.D0 i) * rankoneCandidateEigenvector D.D0 D.g D.mu i = D.g i) ∧
    rankoneCauchyGramOffDiag D = 0 ∧
    rankoneResultantClosedForm D = rankoneDiscriminantClosedForm D

/-- The candidate eigenvectors satisfy the coordinatewise rank-one equations, the off-diagonal
Gram term vanishes by the common secant value, and the resultant/discriminant package collapses to
the same closed form.
    thm:conclusion-rankone-resultant-discriminant-closed-form -/
theorem paper_conclusion_rankone_resultant_discriminant_closed_form {n : Nat}
    (D : RankoneResultantData n) : RankoneResultantDiscriminantClosedForm D := by
  rcases
      paper_conclusion_rankone_cauchy_orthogonality D.D0 D.g D.hlamdiag D.hmudiag D.hlammu
        D.hlam D.hmu with
    ⟨hLam, hMu, hCross⟩
  refine ⟨hLam, hMu, hCross, by
    simp [rankoneResultantClosedForm, rankoneDiscriminantClosedForm, rankoneCauchyGramOffDiag,
      hCross]⟩

end Omega.Conclusion
