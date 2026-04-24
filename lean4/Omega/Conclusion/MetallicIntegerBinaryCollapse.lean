import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.MetallicCompressionExtremum
import Omega.Folding.MetallicIntegerScalarizationThreshold
import Omega.Folding.MetallicParetoFrontier
import Omega.Folding.MetallicTwoStateSFT

open scoped goldenRatio
open Omega.Folding.MetallicParetoFrontier

namespace Omega.Conclusion

open Omega.Folding

private lemma metallicPerronRoot_one : metallicPerronRoot (1 : ℝ) = Real.goldenRatio := by
  rw [metallicPerronRoot, Real.goldenRatio]
  norm_num

private lemma metallicPerronRoot_two : metallicPerronRoot (2 : ℝ) = 1 + Real.sqrt 2 := by
  rw [metallicPerronRoot]
  have hsqrt : Real.sqrt ((2 : ℝ) ^ 2 + 4) = 2 * Real.sqrt 2 := by
    rw [show ((2 : ℝ) ^ 2 + 4) = (2 * Real.sqrt 2) ^ 2 by
      have hsqrt2_sq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
        rw [Real.sq_sqrt]
        positivity
      nlinarith [hsqrt2_sq]]
    rw [Real.sqrt_sq]
    positivity
  rw [hsqrt]
  ring

private lemma one_add_sqrt_two_lt_three : 1 + Real.sqrt 2 < (3 : ℝ) := by
  have hsqrt2_sq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
    rw [Real.sq_sqrt]
    positivity
  nlinarith [hsqrt2_sq]

private lemma arg_lt_metallicPerronRoot {A : ℝ} (hA : 0 < A) : A < metallicPerronRoot A := by
  rw [metallicPerronRoot]
  have hsqrt : A < Real.sqrt (A ^ 2 + 4) := by
    have h' : Real.sqrt (A ^ 2) < Real.sqrt (A ^ 2 + 4) := by
      exact Real.sqrt_lt_sqrt (sq_nonneg A) (by nlinarith)
    simpa [Real.sqrt_sq (le_of_lt hA)] using h'
  nlinarith

private lemma metallicPerronRoot_two_lt_nat {A : ℕ} (hA : 3 ≤ A) :
    metallicPerronRoot (2 : ℝ) < metallicPerronRoot (A : ℝ) := by
  have hAreal : (3 : ℝ) ≤ A := by exact_mod_cast hA
  have hApos : 0 < (A : ℝ) := by positivity
  calc
    metallicPerronRoot (2 : ℝ) = 1 + Real.sqrt 2 := metallicPerronRoot_two
    _ < 3 := one_add_sqrt_two_lt_three
    _ ≤ A := hAreal
    _ < metallicPerronRoot (A : ℝ) := arg_lt_metallicPerronRoot hApos

private lemma metallicPerronRoot_nat_gt_two {A : ℕ} (hA : 3 ≤ A) :
    2 < metallicPerronRoot (A : ℝ) := by
  have hAreal : (2 : ℝ) < A := by exact_mod_cast hA
  have hApos : 0 < (A : ℝ) := by positivity
  exact lt_trans hAreal (arg_lt_metallicPerronRoot hApos)

private lemma metallicCompressionInside_diff {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (1 + y⁻¹ - y⁻¹ ^ 2) - (1 + x⁻¹ - x⁻¹ ^ 2) =
      (x - y) * (x * y - x - y) / (x ^ 2 * y ^ 2) := by
  field_simp [hx, hy]
  ring

private lemma metallicCompressionObjective_strictAntiOn_Ioi_two :
    StrictAntiOn metallicCompressionObjective (Set.Ioi 2) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := lt_trans (by norm_num) hx
  have hy0 : 0 < y := lt_trans (by norm_num) hy
  have hx1 : 1 < x := lt_trans (by norm_num) hx
  have hy1 : 1 < y := lt_trans (by norm_num) hy
  have hprod : 0 < x * y - x - y := by
    have hx2 : 0 < x - 2 := sub_pos.mpr hx
    have hy2 : 0 < y - 2 := sub_pos.mpr hy
    have hrew : x * y - x - y = (x - 2) * (y - 2) + (x - 2) + (y - 2) := by
      ring
    rw [hrew]
    positivity
  have hfrac :
      (x - y) * (x * y - x - y) / (x ^ 2 * y ^ 2) < 0 := by
    have hnum : (x - y) * (x * y - x - y) < 0 := by
      have hxy' : x - y < 0 := sub_neg.mpr hxy
      exact mul_neg_of_neg_of_pos hxy' hprod
    have hden : 0 < x ^ 2 * y ^ 2 := by positivity
    exact div_neg_of_neg_of_pos hnum hden
  have hinside :
      1 + y⁻¹ - y⁻¹ ^ 2 < 1 + x⁻¹ - x⁻¹ ^ 2 := by
    have hdiff := metallicCompressionInside_diff hx0.ne' hy0.ne'
    linarith
  have hposy : 0 < 1 + y⁻¹ - y⁻¹ ^ 2 := metallicCompressionInside_pos (le_of_lt hy1)
  simpa [metallicCompressionObjective] using Real.log_lt_log hposy hinside

private lemma metallicCompressionObjective_one_lt_two :
    metallicCompressionObjective (metallicPerronRoot (1 : ℝ)) <
      metallicCompressionObjective (metallicPerronRoot (2 : ℝ)) := by
  have hAphi : metallicAOfLambda Real.goldenRatio = 1 := by
    unfold metallicAOfLambda
    have hconj : Real.goldenRatio⁻¹ = -Real.goldenConj := by
      simpa [one_div] using Real.inv_goldenRatio
    nlinarith [hconj, Real.goldenRatio_add_goldenConj]
  have hAtwo : metallicAOfLambda (1 + Real.sqrt 2) = 2 := by
    unfold metallicAOfLambda
    have hne : (1 + Real.sqrt 2 : ℝ) ≠ 0 := by positivity
    field_simp [hne]
    have hsqrt2_sq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith [hsqrt2_sq]
  rcases paper_metallic_pareto_frontier_lambda with ⟨hfront, _, _⟩
  have hleft :
      metallicCompressionObjective (metallicPerronRoot (1 : ℝ)) = Real.log (2 / Real.goldenRatio) := by
    rw [metallicPerronRoot_one]
    have h := hfront (lam := Real.goldenRatio) le_rfl
    calc
      metallicCompressionObjective Real.goldenRatio = Real.log ((1 + 1) / Real.goldenRatio) := by
        simpa [hAphi] using h.2.2.1.symm
      _ = Real.log (2 / Real.goldenRatio) := by congr 1; ring
  have hright :
      metallicCompressionObjective (metallicPerronRoot (2 : ℝ)) = Real.log (3 / (1 + Real.sqrt 2)) := by
    rw [metallicPerronRoot_two]
    have hphi_le : Real.goldenRatio ≤ 1 + Real.sqrt 2 := by
      have hphi_lt_two : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
      have hsqrt2_gt_one : (1 : ℝ) < Real.sqrt 2 := by
        simpa [Real.sqrt_one] using
          (Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by positivity) (by norm_num : (1 : ℝ) < 2))
      linarith
    have h := hfront (lam := 1 + Real.sqrt 2) hphi_le
    calc
      metallicCompressionObjective (1 + Real.sqrt 2) = Real.log ((2 + 1) / (1 + Real.sqrt 2)) := by
        simpa [hAtwo] using h.2.2.1.symm
      _ = Real.log (3 / (1 + Real.sqrt 2)) := by congr 1; ring
  rw [hleft, hright]
  have hleft_pos : 0 < 2 / Real.goldenRatio := by positivity
  have hineq : 2 / Real.goldenRatio < 3 / (1 + Real.sqrt 2) := by
    change 2 / ((1 + Real.sqrt 5) / 2) < 3 / (1 + Real.sqrt 2)
    have hsqrt2_sq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
      rw [Real.sq_sqrt]
      positivity
    have hsqrt2_pos : 0 < (Real.sqrt 2 : ℝ) := by positivity
    have hsqrt5_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := by
      rw [Real.sq_sqrt]
      positivity
    have hsqrt5_pos : 0 < (Real.sqrt 5 : ℝ) := by positivity
    have hphi_ne : ((1 + Real.sqrt 5) / 2 : ℝ) ≠ 0 := by positivity
    have hsqrt2_ne : (1 + Real.sqrt 2 : ℝ) ≠ 0 := by positivity
    field_simp [hphi_ne, hsqrt2_ne]
    have hsq : (1 + 4 * Real.sqrt 2) ^ 2 < (3 * Real.sqrt 5) ^ 2 := by
      nlinarith [hsqrt2_sq, hsqrt5_sq]
    have hmain : 1 + 4 * Real.sqrt 2 < 3 * Real.sqrt 5 := by
      nlinarith [hsq]
    nlinarith [hmain]
  exact Real.log_lt_log hleft_pos hineq

/-- Under the integer restriction `A ∈ ℤ_{≥ 1}`, the metallic compression objective has the
unique maximizer `A = 2`, and every integer `A ≥ 3` is strictly dominated by `A = 2` in the
bi-objective order `(compression, -certificate)`.
    thm:conclusion-metallic-integer-binary-collapse -/
theorem paper_conclusion_metallic_integer_binary_collapse :
    Omega.Folding.MetallicParetoFrontier.metallicCompressionObjective
        (Omega.Folding.metallicPerronRoot (1 : ℝ)) <
      Omega.Folding.MetallicParetoFrontier.metallicCompressionObjective
        (Omega.Folding.metallicPerronRoot (2 : ℝ)) ∧
      (∀ A : ℕ, 3 ≤ A →
        Omega.Folding.MetallicParetoFrontier.metallicCompressionObjective
            (Omega.Folding.metallicPerronRoot (A : ℝ)) <
          Omega.Folding.MetallicParetoFrontier.metallicCompressionObjective
            (Omega.Folding.metallicPerronRoot (2 : ℝ)) ∧
        Omega.Folding.MetallicParetoFrontier.metallicCertificateObjective
            (Omega.Folding.metallicPerronRoot (2 : ℝ)) <
          Omega.Folding.MetallicParetoFrontier.metallicCertificateObjective
            (Omega.Folding.metallicPerronRoot (A : ℝ))) := by
  refine ⟨metallicCompressionObjective_one_lt_two, ?_⟩
  intro A hA
  have hroot_lt : metallicPerronRoot (2 : ℝ) < metallicPerronRoot (A : ℝ) :=
    metallicPerronRoot_two_lt_nat hA
  have hroot_two_mem : metallicPerronRoot (2 : ℝ) ∈ Set.Ioi 2 := by
    rw [metallicPerronRoot_two]
    show 2 < 1 + Real.sqrt 2
    have hsqrt2_gt_one : (1 : ℝ) < Real.sqrt 2 := by
      simpa [Real.sqrt_one] using
        (Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by positivity) (by norm_num : (1 : ℝ) < 2))
    linarith
  have hroot_A_mem : metallicPerronRoot (A : ℝ) ∈ Set.Ioi 2 := metallicPerronRoot_nat_gt_two hA
  have hcomp :
      metallicCompressionObjective (metallicPerronRoot (A : ℝ)) <
        metallicCompressionObjective (metallicPerronRoot (2 : ℝ)) := by
    exact metallicCompressionObjective_strictAntiOn_Ioi_two
      hroot_two_mem hroot_A_mem hroot_lt
  have hcert :
      Omega.Folding.MetallicParetoFrontier.metallicCertificateObjective
          (metallicPerronRoot (2 : ℝ)) <
        Omega.Folding.MetallicParetoFrontier.metallicCertificateObjective
          (metallicPerronRoot (A : ℝ)) := by
    have htwo : metallicPerronRoot (2 : ℝ) ∈ Set.Ioi 1 := by
      show 1 < metallicPerronRoot (2 : ℝ)
      exact lt_trans (by norm_num) hroot_two_mem
    have hA' : metallicPerronRoot (A : ℝ) ∈ Set.Ioi 1 := by
      show 1 < metallicPerronRoot (A : ℝ)
      exact lt_trans (by norm_num) hroot_A_mem
    have hcert' :
        Omega.Folding.MetallicParetoFrontier.metallicCertificateObjective
            (metallicPerronRoot (2 : ℝ)) <
          Omega.Folding.MetallicParetoFrontier.metallicCertificateObjective
            (metallicPerronRoot (A : ℝ)) := by
      simpa using (metallicCertificateObjective_strictMonoOn htwo hA' hroot_lt)
    exact hcert'
  exact ⟨hcomp, hcert⟩

end Omega.Conclusion
