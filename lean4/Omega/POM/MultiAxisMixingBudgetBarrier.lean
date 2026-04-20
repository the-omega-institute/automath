import Mathlib.Tactic
import Omega.POM.MinkowskiBudgetBarrier

namespace Omega.POM

/-- Paper label: `cor:pom-multi-axis-mixing-budget-barrier`.
Combining the Minkowski upper bound for the minimizing energy `q(m)` with the quadratic
small-angle model `Δ_spec = q(m) / 2` forces a reciprocal lower bound for the mixing time. -/
theorem paper_pom_multi_axis_mixing_budget_barrier
    {d : ℕ} (sigmaDiag : Fin d → ℝ) (Λ : Finset (Fin d → ℝ)) (hΛ : Λ.Nonempty)
    (Vd detSigma B r deltaSpec tauMix : ℝ) (θ : Fin d → ℝ)
    (hθΛ : θ ∈ Λ)
    (hθ : pomQuadraticEnergy sigmaDiag θ ≤ r ^ 2)
    (hr : r ^ 2 = pomMinkowskiBudgetUpperBound d Vd detSigma B)
    (hgap : deltaSpec = (1 / 2 : ℝ) * pomShortestEnergy sigmaDiag Λ hΛ)
    (hgap_pos : 0 < deltaSpec)
    (htau : tauMix = 1 / deltaSpec) :
    pomShortestEnergy sigmaDiag Λ hΛ ≤ pomMinkowskiBudgetUpperBound d Vd detSigma B ∧
      deltaSpec ≤ (1 / 2 : ℝ) * pomMinkowskiBudgetUpperBound d Vd detSigma B ∧
      tauMix ≥ 1 / ((1 / 2 : ℝ) * pomMinkowskiBudgetUpperBound d Vd detSigma B) := by
  have hbudget :
      pomShortestEnergy sigmaDiag Λ hΛ ≤ pomMinkowskiBudgetUpperBound d Vd detSigma B :=
    (paper_pom_minkowski_budget_barrier sigmaDiag Λ hΛ Vd detSigma B r θ hθΛ hθ hr).2.2
  have hgap_le : deltaSpec ≤ (1 / 2 : ℝ) * pomMinkowskiBudgetUpperBound d Vd detSigma B := by
    rw [hgap]
    exact mul_le_mul_of_nonneg_left hbudget (by norm_num)
  have hmix_lower :
      1 / ((1 / 2 : ℝ) * pomMinkowskiBudgetUpperBound d Vd detSigma B) ≤ tauMix := by
    rw [htau]
    exact one_div_le_one_div_of_le hgap_pos hgap_le
  exact ⟨hbudget, hgap_le, hmix_lower⟩

end Omega.POM
