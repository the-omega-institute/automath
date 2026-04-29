import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.Conclusion.PoissonBivariateKLSharp

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- The total point-defect mass `M₀ = Σ m_j δ_j`. -/
noncomputable def conclusion_point_defect_poisson_entropy_fingerprint_totalMass {κ : ℕ}
    (mass depth : Fin κ → ℝ) : ℝ :=
  ∑ j, mass j * depth j

/-- The finite probability weights on parameter pairs. -/
noncomputable def conclusion_point_defect_poisson_entropy_fingerprint_weight {κ : ℕ}
    (mass depth : Fin κ → ℝ) (j : Fin κ) : ℝ :=
  mass j * depth j /
    conclusion_point_defect_poisson_entropy_fingerprint_totalMass mass depth

/-- Mean location coordinate of the finite point-defect parameter law. -/
noncomputable def conclusion_point_defect_poisson_entropy_fingerprint_meanGamma {κ : ℕ}
    (mass depth gamma : Fin κ → ℝ) : ℝ :=
  ∑ j, conclusion_point_defect_poisson_entropy_fingerprint_weight mass depth j * gamma j

/-- Mean scale-depth coordinate of the finite point-defect parameter law. -/
noncomputable def conclusion_point_defect_poisson_entropy_fingerprint_meanDelta {κ : ℕ}
    (mass depth : Fin κ → ℝ) : ℝ :=
  ∑ j, conclusion_point_defect_poisson_entropy_fingerprint_weight mass depth j * depth j

/-- Weighted variance of the location coordinate. -/
noncomputable def conclusion_point_defect_poisson_entropy_fingerprint_varGamma {κ : ℕ}
    (mass depth gamma : Fin κ → ℝ) : ℝ :=
  ∑ j,
    conclusion_point_defect_poisson_entropy_fingerprint_weight mass depth j *
      (gamma j -
        conclusion_point_defect_poisson_entropy_fingerprint_meanGamma mass depth gamma) ^ 2

/-- Weighted variance of the scale-depth coordinate. -/
noncomputable def conclusion_point_defect_poisson_entropy_fingerprint_varDelta {κ : ℕ}
    (mass depth : Fin κ → ℝ) : ℝ :=
  ∑ j,
    conclusion_point_defect_poisson_entropy_fingerprint_weight mass depth j *
      (depth j - conclusion_point_defect_poisson_entropy_fingerprint_meanDelta mass depth) ^ 2

/-- Weighted covariance between location and scale depth. -/
noncomputable def conclusion_point_defect_poisson_entropy_fingerprint_covGammaDelta {κ : ℕ}
    (mass depth gamma : Fin κ → ℝ) : ℝ :=
  ∑ j,
    conclusion_point_defect_poisson_entropy_fingerprint_weight mass depth j *
      (gamma j -
        conclusion_point_defect_poisson_entropy_fingerprint_meanGamma mass depth gamma) *
        (depth j - conclusion_point_defect_poisson_entropy_fingerprint_meanDelta mass depth)

/-- The traceless variance coordinate `A = Var Γ - Var Δ`. -/
noncomputable def conclusion_point_defect_poisson_entropy_fingerprint_A {κ : ℕ}
    (mass depth gamma : Fin κ → ℝ) : ℝ :=
  conclusion_point_defect_poisson_entropy_fingerprint_varGamma mass depth gamma -
    conclusion_point_defect_poisson_entropy_fingerprint_varDelta mass depth

/-- The covariance coordinate `B = Cov(Γ, Δ)`. -/
noncomputable def conclusion_point_defect_poisson_entropy_fingerprint_B {κ : ℕ}
    (mass depth gamma : Fin κ → ℝ) : ℝ :=
  conclusion_point_defect_poisson_entropy_fingerprint_covGammaDelta mass depth gamma

/-- The sharp fourth-order KL fingerprint coefficient. -/
noncomputable def conclusion_point_defect_poisson_entropy_fingerprint_klCoefficient {κ : ℕ}
    (mass depth gamma : Fin κ → ℝ) : ℝ :=
  conclusion_point_defect_poisson_entropy_fingerprint_A mass depth gamma ^ 2 / 8 +
    conclusion_point_defect_poisson_entropy_fingerprint_B mass depth gamma ^ 2 / 2

/-- Paper label: `thm:conclusion-point-defect-poisson-entropy-fingerprint`.

The finite point-defect weights form a probability law when `M₀ ≠ 0`; after computing its
`A,B` invariants, the existing bivariate Poisson/Cauchy KL theorem gives the sharp
coefficient `A²/8 + B²/2`. -/
theorem paper_conclusion_point_defect_poisson_entropy_fingerprint {κ : ℕ}
    (mass depth gamma : Fin κ → ℝ)
    (hM : conclusion_point_defect_poisson_entropy_fingerprint_totalMass mass depth ≠ 0) :
    (∑ j, conclusion_point_defect_poisson_entropy_fingerprint_weight mass depth j) = 1 ∧
      Omega.CircleDimension.PoissonBivariateFdivFourthOrderConstant 1
        (conclusion_point_defect_poisson_entropy_fingerprint_A mass depth gamma) 0
        (conclusion_point_defect_poisson_entropy_fingerprint_B mass depth gamma) ∧
      conclusion_point_defect_poisson_entropy_fingerprint_klCoefficient mass depth gamma =
        conclusion_point_defect_poisson_entropy_fingerprint_A mass depth gamma ^ 2 / 8 +
          conclusion_point_defect_poisson_entropy_fingerprint_B mass depth gamma ^ 2 / 2 := by
  refine ⟨?_, ?_, rfl⟩
  · unfold conclusion_point_defect_poisson_entropy_fingerprint_weight
      conclusion_point_defect_poisson_entropy_fingerprint_totalMass
    rw [← Finset.sum_div]
    have hM' : (∑ x, mass x * depth x) ≠ 0 := by
      simpa [conclusion_point_defect_poisson_entropy_fingerprint_totalMass] using hM
    exact div_self hM'
  · exact
      paper_conclusion_poisson_bivariate_kl_sharp
        (conclusion_point_defect_poisson_entropy_fingerprint_A mass depth gamma)
        (conclusion_point_defect_poisson_entropy_fingerprint_B mass depth gamma)

end

end Omega.Conclusion
