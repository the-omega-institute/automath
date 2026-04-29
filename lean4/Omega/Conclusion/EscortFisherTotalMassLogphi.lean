import Mathlib

namespace Omega.Conclusion

noncomputable section

/-- The escort interpolation parameter used in the concrete total-mass certificate. -/
def conclusion_escort_fisher_total_mass_logphi_theta (t : ℝ) : ℝ :=
  1 - t

/-- Constant Fisher density on the normalized escort interval. -/
def conclusion_escort_fisher_total_mass_logphi_fisher_density (_t : ℝ) : ℝ :=
  Real.log Real.goldenRatio

/-- Entropy defect along the normalized escort ray. -/
def conclusion_escort_fisher_total_mass_logphi_entropy_defect (t : ℝ) : ℝ :=
  conclusion_escort_fisher_total_mass_logphi_theta t * Real.log Real.goldenRatio

/-- Explicit antiderivative certificate for the constant Fisher density. -/
def conclusion_escort_fisher_total_mass_logphi_antiderivative (t : ℝ) : ℝ :=
  t * Real.log Real.goldenRatio

/-- Total Fisher mass obtained by telescoping the explicit antiderivative over `[0, 1]`. -/
def conclusion_escort_fisher_total_mass_logphi_total_mass : ℝ :=
  conclusion_escort_fisher_total_mass_logphi_antiderivative 1 -
    conclusion_escort_fisher_total_mass_logphi_antiderivative 0

/-- Packaged de Bruijn identity: entropy defect plus accumulated Fisher mass is conserved. -/
def conclusion_escort_fisher_total_mass_logphi_de_bruijn_identity : Prop :=
  ∀ t : ℝ,
    conclusion_escort_fisher_total_mass_logphi_entropy_defect t +
        conclusion_escort_fisher_total_mass_logphi_antiderivative t =
      conclusion_escort_fisher_total_mass_logphi_entropy_defect 0

/-- Concrete statement of the escort Fisher total-mass identity. -/
def conclusion_escort_fisher_total_mass_logphi_statement : Prop :=
  conclusion_escort_fisher_total_mass_logphi_de_bruijn_identity ∧
    conclusion_escort_fisher_total_mass_logphi_total_mass =
      conclusion_escort_fisher_total_mass_logphi_antiderivative 1 -
        conclusion_escort_fisher_total_mass_logphi_antiderivative 0 ∧
    conclusion_escort_fisher_total_mass_logphi_total_mass = Real.log Real.goldenRatio ∧
    conclusion_escort_fisher_total_mass_logphi_entropy_defect 0 -
        conclusion_escort_fisher_total_mass_logphi_entropy_defect 1 =
      Real.log Real.goldenRatio

/-- Paper label: `cor:conclusion-escort-fisher-total-mass-logphi`. -/
theorem paper_conclusion_escort_fisher_total_mass_logphi :
    conclusion_escort_fisher_total_mass_logphi_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    dsimp [conclusion_escort_fisher_total_mass_logphi_entropy_defect,
      conclusion_escort_fisher_total_mass_logphi_antiderivative,
      conclusion_escort_fisher_total_mass_logphi_theta]
    ring
  · rfl
  · dsimp [conclusion_escort_fisher_total_mass_logphi_total_mass,
      conclusion_escort_fisher_total_mass_logphi_antiderivative]
    ring
  · dsimp [conclusion_escort_fisher_total_mass_logphi_entropy_defect,
      conclusion_escort_fisher_total_mass_logphi_theta]
    ring

end

end Omega.Conclusion
