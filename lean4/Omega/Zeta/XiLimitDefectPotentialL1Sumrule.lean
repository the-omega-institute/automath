import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open MeasureTheory Real
open scoped BigOperators

namespace Omega.Zeta

/-- A finite defect family with explicit centers and weights. -/
structure XiLimitDefectPotentialL1SumruleData where
  n : ℕ
  center : Fin n → ℝ
  weight : Fin n → ℝ

/-- A single translated defect block of width `2π`. -/
noncomputable def XiLimitDefectPotentialL1SumruleData.summand
    (D : XiLimitDefectPotentialL1SumruleData) (i : Fin D.n) : ℝ → ℝ :=
  fun x => D.weight i *
    Set.indicator (Set.Icc (D.center i - Real.pi) (D.center i + Real.pi))
      (fun _ : ℝ => (1 : ℝ)) x

/-- The finite defect potential is the sum of the translated blocks. -/
noncomputable def XiLimitDefectPotentialL1SumruleData.defectPotential
    (D : XiLimitDefectPotentialL1SumruleData) : ℝ → ℝ :=
  fun x => ∑ i, D.summand i x

/-- The total defect weight. -/
noncomputable def XiLimitDefectPotentialL1SumruleData.weightedSum
    (D : XiLimitDefectPotentialL1SumruleData) : ℝ :=
  ∑ i, D.weight i

/-- The finite defect potential is Lebesgue integrable. -/
def XiLimitDefectPotentialL1SumruleData.integrable
    (D : XiLimitDefectPotentialL1SumruleData) : Prop :=
  Integrable D.defectPotential

/-- The integral of the finite defect potential is exactly `2π` times the total weight. -/
def XiLimitDefectPotentialL1SumruleData.integral_eq_two_pi_weighted_sum
    (D : XiLimitDefectPotentialL1SumruleData) : Prop :=
  ∫ x, D.defectPotential x = 2 * Real.pi * D.weightedSum

lemma xiLimitDefectPotentialL1Summand_integrable (D : XiLimitDefectPotentialL1SumruleData)
    (i : Fin D.n) : Integrable (D.summand i) := by
  have hbase : Integrable
      (Set.indicator (Set.Icc (D.center i - Real.pi) (D.center i + Real.pi))
        (fun _ : ℝ => (1 : ℝ))) := by
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Icc]
    simp [MeasureTheory.IntegrableOn]
  simpa [XiLimitDefectPotentialL1SumruleData.summand, mul_comm, mul_left_comm, mul_assoc] using
    hbase.const_mul (D.weight i)

lemma xiLimitDefectPotentialL1Indicator_integral_two_pi (D : XiLimitDefectPotentialL1SumruleData)
    (i : Fin D.n) :
    ∫ x,
        Set.indicator (Set.Icc (D.center i - Real.pi) (D.center i + Real.pi))
          (fun _ : ℝ => (1 : ℝ)) x = 2 * Real.pi := by
  calc
    ∫ x,
        Set.indicator (Set.Icc (D.center i - Real.pi) (D.center i + Real.pi))
          (fun _ : ℝ => (1 : ℝ)) x
        = volume.real (Set.Icc (D.center i - Real.pi) (D.center i + Real.pi)) := by
            simpa using
              (MeasureTheory.integral_indicator_const (μ := volume) (E := ℝ)
                (e := (1 : ℝ)) (s_meas := measurableSet_Icc)
                (s := Set.Icc (D.center i - Real.pi) (D.center i + Real.pi)))
    _ = ENNReal.toReal (volume (Set.Icc (D.center i - Real.pi) (D.center i + Real.pi))) := rfl
    _ = ENNReal.toReal (ENNReal.ofReal ((D.center i + Real.pi) - (D.center i - Real.pi))) := by
          simp [Real.volume_Icc]
    _ = 2 * Real.pi := by
          have h : 0 ≤ (2 * Real.pi : ℝ) := by
            positivity
          rw [show (D.center i + Real.pi) - (D.center i - Real.pi) = 2 * Real.pi by ring]
          rw [ENNReal.toReal_ofReal h]

lemma xiLimitDefectPotentialL1Summand_integral (D : XiLimitDefectPotentialL1SumruleData)
    (i : Fin D.n) :
    ∫ x, D.summand i x = 2 * Real.pi * D.weight i := by
  calc
    ∫ x, D.summand i x
        = ∫ x, D.weight i *
            Set.indicator (Set.Icc (D.center i - Real.pi) (D.center i + Real.pi))
              (fun _ : ℝ => (1 : ℝ)) x := by
            rfl
    _ = D.weight i *
          ∫ x,
            Set.indicator (Set.Icc (D.center i - Real.pi) (D.center i + Real.pi))
              (fun _ : ℝ => (1 : ℝ)) x := by
            rw [MeasureTheory.integral_const_mul]
    _ = D.weight i * (2 * Real.pi) := by
          rw [xiLimitDefectPotentialL1Indicator_integral_two_pi D i]
    _ = 2 * Real.pi * D.weight i := by
          ring

lemma xiLimitDefectPotentialL1_integrable (D : XiLimitDefectPotentialL1SumruleData) :
    Integrable D.defectPotential := by
  classical
  unfold XiLimitDefectPotentialL1SumruleData.defectPotential
  refine Finset.induction_on (Finset.univ : Finset (Fin D.n)) ?_ ?_
  · simp
  · intro i s hi hs
    simpa [hi, Pi.add_apply] using (xiLimitDefectPotentialL1Summand_integrable D i).add hs

lemma xiLimitDefectPotentialL1_integral (D : XiLimitDefectPotentialL1SumruleData) :
    ∫ x, D.defectPotential x = 2 * Real.pi * D.weightedSum := by
  classical
  unfold XiLimitDefectPotentialL1SumruleData.defectPotential
    XiLimitDefectPotentialL1SumruleData.weightedSum
  rw [MeasureTheory.integral_finset_sum (Finset.univ : Finset (Fin D.n))]
  · calc
      Finset.sum (Finset.univ : Finset (Fin D.n)) (fun i => ∫ x, D.summand i x)
          = Finset.sum (Finset.univ : Finset (Fin D.n)) (fun i => 2 * Real.pi * D.weight i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact xiLimitDefectPotentialL1Summand_integral D i
      _ = (2 * Real.pi) * Finset.sum (Finset.univ : Finset (Fin D.n)) (fun i => D.weight i) := by
              rw [Finset.mul_sum]
      _ = 2 * Real.pi * ∑ i, D.weight i := by
              simp
  · intro i hi
    simpa using (xiLimitDefectPotentialL1Summand_integrable D i)

/-- Finite additivity of the concrete translated defect blocks gives an `L¹` sum rule with exact
`2π` weight per defect.
    cor:xi-limit-defect-potential-L1-sumrule -/
theorem paper_xi_limit_defect_potential_l1_sumrule (D : XiLimitDefectPotentialL1SumruleData) :
    D.integrable ∧ D.integral_eq_two_pi_weighted_sum := by
  exact ⟨xiLimitDefectPotentialL1_integrable D, xiLimitDefectPotentialL1_integral D⟩

end Omega.Zeta
