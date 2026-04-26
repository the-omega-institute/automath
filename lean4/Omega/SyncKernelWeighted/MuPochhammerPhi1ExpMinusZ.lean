import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic
import Omega.SyncKernelWeighted.MuPochhammerNecklaceExpansion

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The surviving logarithmic term in the `α = 1` necklace expansion. -/
def mu_pochhammer_phi1_exp_minus_z_log (z : ℂ) : ℂ :=
  -((mu_pochhammer_necklace_expansion_coefficient 1 1 : ℂ) * z)

/-- Paper label: `cor:mu-pochhammer-phi1-exp-minus-z`. At `α = 1` the first necklace coefficient
is `1`, so the surviving logarithmic term is exactly `-z`, and exponentiating gives `exp (-z)`. -/
def mu_pochhammer_phi1_exp_minus_z_statement : Prop :=
  mu_pochhammer_necklace_expansion_coefficient 1 1 = 1 ∧
    ∀ z : ℂ,
      mu_pochhammer_phi1_exp_minus_z_log z = -z ∧
        Complex.exp (mu_pochhammer_phi1_exp_minus_z_log z) = Complex.exp (-z)

theorem paper_mu_pochhammer_phi1_exp_minus_z : mu_pochhammer_phi1_exp_minus_z_statement := by
  have hcoeff1 : mu_pochhammer_necklace_expansion_coefficient 1 1 = 1 := by
    simpa using (paper_mu_pochhammer_necklace_expansion 1).1 1 le_rfl
  refine ⟨hcoeff1, ?_⟩
  intro z
  constructor
  · simp [mu_pochhammer_phi1_exp_minus_z_log, hcoeff1]
  · simp [mu_pochhammer_phi1_exp_minus_z_log, hcoeff1]

end

end Omega.SyncKernelWeighted
