import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.MinkowskiBudgetBarrier
import Omega.POM.MultiAxisMixingBudgetBarrier

namespace Omega.POM

/-- Converting the multi-axis Minkowski budget barrier into the near-`1` pole-gap normalization
gives the claimed `B^{-2 / d}` upper bound for the pole distance. -/
theorem paper_pom_multi_axis_near1_pole_barrier
    {d : ℕ} (sigmaDiag : Fin d → ℝ) (Λ : Finset (Fin d → ℝ)) (hΛ : Λ.Nonempty)
    (Vd detSigma B r deltaSpec poleGap logLambda : ℝ) (θ : Fin d → ℝ) (hθΛ : θ ∈ Λ)
    (hθ : Omega.POM.pomQuadraticEnergy sigmaDiag θ ≤ r ^ 2)
    (hr : r ^ 2 = Omega.POM.pomMinkowskiBudgetUpperBound d Vd detSigma B)
    (hgap : deltaSpec = (1 / 2 : ℝ) * Omega.POM.pomShortestEnergy sigmaDiag Λ hΛ)
    (hpole : poleGap = deltaSpec / logLambda) (hlog : 0 < logLambda) :
    poleGap ≤ Omega.POM.pomMinkowskiBudgetUpperBound d Vd detSigma B / (2 * logLambda) := by
  have hbudget :
      Omega.POM.pomShortestEnergy sigmaDiag Λ hΛ ≤
        Omega.POM.pomMinkowskiBudgetUpperBound d Vd detSigma B :=
    (paper_pom_minkowski_budget_barrier sigmaDiag Λ hΛ Vd detSigma B r θ hθΛ hθ hr).2.2
  have hdelta :
      deltaSpec ≤ (1 / 2 : ℝ) * Omega.POM.pomMinkowskiBudgetUpperBound d Vd detSigma B := by
    rw [hgap]
    exact mul_le_mul_of_nonneg_left hbudget (by norm_num)
  have hdiv :
      deltaSpec / logLambda ≤
        ((1 / 2 : ℝ) * Omega.POM.pomMinkowskiBudgetUpperBound d Vd detSigma B) / logLambda := by
    exact div_le_div_of_nonneg_right hdelta hlog.le
  rw [hpole]
  calc
    deltaSpec / logLambda ≤
        ((1 / 2 : ℝ) * Omega.POM.pomMinkowskiBudgetUpperBound d Vd detSigma B) / logLambda := hdiv
    _ = Omega.POM.pomMinkowskiBudgetUpperBound d Vd detSigma B / (2 * logLambda) := by
      field_simp [hlog.ne']

end Omega.POM
