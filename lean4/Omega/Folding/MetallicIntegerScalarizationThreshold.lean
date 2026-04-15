import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.MetallicParetoFrontier

open scoped goldenRatio
open Omega.Folding.MetallicParetoFrontier

namespace Omega.Folding

/-- The explicit scalarized score for the integer candidate `A = 1`. -/
noncomputable def metallicIntegerScoreOne (β : ℝ) : ℝ :=
  Real.log (2 / Real.goldenRatio) - β * (1 / Real.log Real.goldenRatio)

/-- The explicit scalarized score for the integer candidate `A = 2`. -/
noncomputable def metallicIntegerScoreTwo (β : ℝ) : ℝ :=
  Real.log (3 / (1 + Real.sqrt 2)) - β * (2 / Real.log (1 + Real.sqrt 2))

/-- The certificate gap between the two surviving integer candidates. -/
noncomputable def metallicIntegerDeltaK : ℝ :=
  2 / Real.log (1 + Real.sqrt 2) - 1 / Real.log Real.goldenRatio

/-- The unique scalarization threshold separating the integer phases `A = 1` and `A = 2`. -/
noncomputable def beta_ZZ : ℝ :=
  (Real.log (3 / (1 + Real.sqrt 2)) - Real.log (2 / Real.goldenRatio)) / metallicIntegerDeltaK

private lemma metallicA_goldenRatio : metallicAOfLambda Real.goldenRatio = 1 := by
  unfold metallicAOfLambda
  have hinv : Real.goldenRatio⁻¹ = -Real.goldenConj := by
    simpa [one_div] using Real.inv_goldenRatio
  nlinarith [hinv, Real.goldenRatio_add_goldenConj]

private lemma metallicA_one_add_sqrt_two : metallicAOfLambda (1 + Real.sqrt 2) = 2 := by
  unfold metallicAOfLambda
  have hne : (1 + Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have hsq : (Real.sqrt 2) ^ 2 = 2 := by
    rw [Real.sq_sqrt]
    positivity
  field_simp [hne]
  nlinarith

private lemma metallicCertificate_goldenRatio :
    metallicCertificateObjective Real.goldenRatio = 1 / Real.log Real.goldenRatio := by
  calc
    metallicCertificateObjective Real.goldenRatio
        = metallicAOfLambda Real.goldenRatio / Real.log Real.goldenRatio := by
            simp [metallicCertificateObjective, metallicAOfLambda]
    _ = 1 / Real.log Real.goldenRatio := by rw [metallicA_goldenRatio]

private lemma metallicCertificate_one_add_sqrt_two :
    metallicCertificateObjective (1 + Real.sqrt 2) = 2 / Real.log (1 + Real.sqrt 2) := by
  calc
    metallicCertificateObjective (1 + Real.sqrt 2)
        = metallicAOfLambda (1 + Real.sqrt 2) / Real.log (1 + Real.sqrt 2) := by
            simp [metallicCertificateObjective, metallicAOfLambda]
    _ = 2 / Real.log (1 + Real.sqrt 2) := by rw [metallicA_one_add_sqrt_two]

private lemma metallicIntegerDeltaK_pos : 0 < metallicIntegerDeltaK := by
  have hlt : Real.goldenRatio < 1 + Real.sqrt 2 := by
    have hphi_lt_two : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
    have htwo_lt : (2 : ℝ) < 1 + Real.sqrt 2 := by
      have hone_lt : (1 : ℝ) < Real.sqrt 2 := by
        simpa [Real.sqrt_one] using
          (Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by positivity) (by norm_num : (1 : ℝ) < 2))
      linarith
    exact lt_trans hphi_lt_two htwo_lt
  have hkappa :
      metallicCertificateObjective Real.goldenRatio <
        metallicCertificateObjective (1 + Real.sqrt 2) := by
    exact metallicCertificateObjective_strictMonoOn
      (show Real.goldenRatio ∈ Set.Ioi 1 by exact Real.one_lt_goldenRatio)
      (show 1 + Real.sqrt 2 ∈ Set.Ioi 1 by
        have hone_lt : (1 : ℝ) < Real.sqrt 2 := by
          simpa [Real.sqrt_one] using
            (Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by positivity) (by norm_num : (1 : ℝ) < 2))
        have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := lt_trans zero_lt_one hone_lt
        exact lt_add_of_pos_right 1 hsqrt2_pos)
      hlt
  rw [metallicCertificate_goldenRatio, metallicCertificate_one_add_sqrt_two] at hkappa
  simpa [metallicIntegerDeltaK] using hkappa

private lemma metallicIntegerScore_gap (β : ℝ) :
    metallicIntegerScoreTwo β - metallicIntegerScoreOne β =
      metallicIntegerDeltaK * (beta_ZZ - β) := by
  have hscale :
      Real.log (3 / (1 + Real.sqrt 2)) - Real.log (2 / Real.goldenRatio) =
        metallicIntegerDeltaK * beta_ZZ := by
    unfold beta_ZZ
    field_simp [metallicIntegerDeltaK_pos.ne']
  calc
    metallicIntegerScoreTwo β - metallicIntegerScoreOne β
        = (Real.log (3 / (1 + Real.sqrt 2)) - Real.log (2 / Real.goldenRatio)) -
            β * metallicIntegerDeltaK := by
              unfold metallicIntegerScoreTwo metallicIntegerScoreOne metallicIntegerDeltaK
              ring
    _ = metallicIntegerDeltaK * beta_ZZ - β * metallicIntegerDeltaK := by rw [hscale]
    _ = metallicIntegerDeltaK * (beta_ZZ - β) := by ring

/-- Paper-facing integer threshold law: once the continuous design space has already reduced the
    integer Pareto set to `{1, 2}`, the scalarization score has a unique threshold `beta_ZZ`
    separating the `A = 2`, tie, and `A = 1` phases. -/
theorem paper_metallic_integer_scalarization_threshold :
    (∀ β : ℝ, metallicIntegerScoreTwo β > metallicIntegerScoreOne β ↔ β < beta_ZZ) ∧
    (∀ β : ℝ, metallicIntegerScoreTwo β = metallicIntegerScoreOne β ↔ β = beta_ZZ) ∧
    (∀ β : ℝ, metallicIntegerScoreTwo β < metallicIntegerScoreOne β ↔ beta_ZZ < β) := by
  refine ⟨?_, ?_, ?_⟩
  · intro β
    have hgap := metallicIntegerScore_gap β
    constructor
    · intro h
      have h' : 0 < metallicIntegerScoreTwo β - metallicIntegerScoreOne β := sub_pos.mpr h
      rw [hgap] at h'
      nlinarith [metallicIntegerDeltaK_pos, h']
    · intro h
      have h' : 0 < metallicIntegerDeltaK * (beta_ZZ - β) := by
        nlinarith [metallicIntegerDeltaK_pos, h]
      rw [← hgap] at h'
      exact sub_pos.mp h'
  · intro β
    have hgap := metallicIntegerScore_gap β
    constructor
    · intro h
      have h' : metallicIntegerScoreTwo β - metallicIntegerScoreOne β = 0 := sub_eq_zero.mpr h
      rw [hgap] at h'
      nlinarith [metallicIntegerDeltaK_pos, h']
    · intro h
      have h' : metallicIntegerDeltaK * (beta_ZZ - β) = 0 := by
        rw [h]
        ring
      rw [← hgap] at h'
      exact sub_eq_zero.mp h'
  · intro β
    have hgap := metallicIntegerScore_gap β
    constructor
    · intro h
      have h' : metallicIntegerScoreTwo β - metallicIntegerScoreOne β < 0 := sub_neg.mpr h
      rw [hgap] at h'
      nlinarith [metallicIntegerDeltaK_pos, h']
    · intro h
      have h' : metallicIntegerDeltaK * (beta_ZZ - β) < 0 := by
        nlinarith [metallicIntegerDeltaK_pos, h]
      rw [← hgap] at h'
      exact sub_neg.mp h'

end Omega.Folding
