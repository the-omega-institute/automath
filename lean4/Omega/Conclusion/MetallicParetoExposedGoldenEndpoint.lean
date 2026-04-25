import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.MetallicLinearScalarizationThreshold

open scoped goldenRatio
open Omega.Folding.MetallicParetoFrontier

namespace Omega.Conclusion

open Omega.Folding

noncomputable section

private noncomputable def conclusion_metallic_pareto_exposed_golden_endpoint_scale_law :
    Omega.Folding.MetallicParetoScaleLawData :=
  Classical.choose paper_metallic_linear_scalarization_threshold

private lemma conclusion_metallic_pareto_exposed_golden_endpoint_betaCritical_eq :
    conclusion_metallic_pareto_exposed_golden_endpoint_scale_law.betaCritical =
      ((1 / 2 - 1 / Real.sqrt 5) * (Real.log Real.goldenRatio) ^ 2) /
        (Real.log Real.goldenRatio - 1 / Real.sqrt 5) :=
  Classical.choose_spec paper_metallic_linear_scalarization_threshold

/-- Conclusion-level metallic Pareto package: the frontier endpoints are `A = 1` and `A = 3/2`,
the optimizer stays in the interval `[1, 3/2]`, and at the critical supporting slope it locks to
the exposed golden endpoint `A = 1`. -/
def conclusion_metallic_pareto_exposed_golden_endpoint_statement : Prop :=
  conclusion_metallic_pareto_exposed_golden_endpoint_scale_law.betaCritical =
      ((1 / 2 - 1 / Real.sqrt 5) * (Real.log Real.goldenRatio) ^ 2) /
        (Real.log Real.goldenRatio - 1 / Real.sqrt 5) ∧
    metallicAOfLambda Real.goldenRatio = 1 ∧
    metallicAOfLambda (2 : ℝ) = 3 / 2 ∧
    (∀ β : ℝ, 0 ≤ β →
      conclusion_metallic_pareto_exposed_golden_endpoint_scale_law.optimalScale β ∈
        Set.Icc (1 : ℝ) (3 / 2 : ℝ)) ∧
    conclusion_metallic_pareto_exposed_golden_endpoint_scale_law.optimalScale
        conclusion_metallic_pareto_exposed_golden_endpoint_scale_law.betaCritical = 1

/-- Paper label: `thm:conclusion-metallic-pareto-exposed-golden-endpoint`. -/
theorem paper_conclusion_metallic_pareto_exposed_golden_endpoint :
    conclusion_metallic_pareto_exposed_golden_endpoint_statement := by
  rcases paper_metallic_pareto_frontier_lambda with ⟨hfront, _, _⟩
  have hphi : metallicAOfLambda Real.goldenRatio = 1 := by
    calc
      metallicAOfLambda Real.goldenRatio = Real.goldenRatio - Real.goldenRatio⁻¹ := by
        simpa using (hfront (lam := Real.goldenRatio) le_rfl).1
      _ = 1 := by
        rw [show (Real.goldenRatio : ℝ) = (1 + Real.sqrt 5) / 2 by rw [Real.goldenRatio]]
        have hsqrt5_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := by
          rw [Real.sq_sqrt]
          positivity
        have hsqrt5_ne : (Real.sqrt 5 : ℝ) ≠ 0 := by positivity
        field_simp [hsqrt5_ne]
        nlinarith
  have htwo : metallicAOfLambda (2 : ℝ) = 3 / 2 := by
    have htwo_front := hfront (lam := (2 : ℝ)) (le_of_lt Real.goldenRatio_lt_two)
    calc
      metallicAOfLambda (2 : ℝ) = 2 - (2 : ℝ)⁻¹ := by simpa using htwo_front.1
      _ = 3 / 2 := by norm_num
  have hscale :=
    paper_metallic_pareto_scale_law
      conclusion_metallic_pareto_exposed_golden_endpoint_scale_law
  refine ⟨conclusion_metallic_pareto_exposed_golden_endpoint_betaCritical_eq, hphi, htwo, ?_, ?_⟩
  · intro β hβ
    simpa [Set.mem_Icc] using hscale.1 β hβ
  · exact hscale.2.2 _ le_rfl

end

end Omega.Conclusion
