import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Total multiplicity of the finite height family. -/
def xiHeightBudgetTotalMass {κ : ℕ} (mass : Fin κ → ℝ) : ℝ :=
  ∑ j, mass j

/-- Weighted total height. -/
def xiHeightBudgetWeightedSum {κ : ℕ} (mass height : Fin κ → ℝ) : ℝ :=
  ∑ j, mass j * height j

/-- Weighted mean height. -/
noncomputable def xiHeightBudgetAverage {κ : ℕ} (mass height : Fin κ → ℝ) : ℝ :=
  xiHeightBudgetWeightedSum mass height / xiHeightBudgetTotalMass mass

/-- Weighted centered second moment. -/
noncomputable def xiHeightBudgetCenteredSquareSum {κ : ℕ} (mass height : Fin κ → ℝ) : ℝ :=
  ∑ j, mass j * (height j - xiHeightBudgetAverage mass height) ^ 2

/-- Concrete finite-family package for the defect-entropy height budget. The key analytic input is
the explicit second-order pointwise upper bound around the weighted mean height. -/
structure XiDefectEntropyHeightBudgetData where
  κ : ℕ
  mass : Fin κ → ℝ
  height : Fin κ → ℝ
  curvatureLower : ℝ
  mass_nonneg : ∀ j, 0 ≤ mass j
  totalMass_pos : 0 < xiHeightBudgetTotalMass mass
  pointwise_second_order :
    ∀ j,
      1 - Real.exp (-height j) ≤
        (1 - Real.exp (-xiHeightBudgetAverage mass height)) +
          Real.exp (-xiHeightBudgetAverage mass height) *
            (height j - xiHeightBudgetAverage mass height) -
          curvatureLower / 2 * (height j - xiHeightBudgetAverage mass height) ^ 2

namespace XiDefectEntropyHeightBudgetData

/-- The defect entropy `S_def = Σ m_j (1 - e^{-s_j})`. -/
noncomputable def defectEntropy (D : XiDefectEntropyHeightBudgetData) : ℝ :=
  ∑ j, D.mass j * (1 - Real.exp (-D.height j))

/-- The weighted average height `\bar{s}`. -/
noncomputable def averageHeight (D : XiDefectEntropyHeightBudgetData) : ℝ :=
  xiHeightBudgetAverage D.mass D.height

/-- The variance numerator `Σ m_j (s_j - \bar{s})²`. -/
noncomputable def centeredSquareSum (D : XiDefectEntropyHeightBudgetData) : ℝ :=
  xiHeightBudgetCenteredSquareSum D.mass D.height

/-- The Jensen exponential height budget `κ_ind (1 - e^{-\bar{s}})`. -/
noncomputable def exponentialHeightBound (D : XiDefectEntropyHeightBudgetData) : ℝ :=
  xiHeightBudgetTotalMass D.mass * (1 - Real.exp (-D.averageHeight))

/-- The explicit second-order variance penalty term. -/
noncomputable def varianceGapTerm (D : XiDefectEntropyHeightBudgetData) : ℝ :=
  D.curvatureLower / 2 * D.centeredSquareSum

end XiDefectEntropyHeightBudgetData

open XiDefectEntropyHeightBudgetData

lemma xi_height_budget_centered_sum_eq_zero {κ : ℕ} (mass height : Fin κ → ℝ)
    (htotal_ne : xiHeightBudgetTotalMass mass ≠ 0) :
    ∑ j, mass j * (height j - xiHeightBudgetAverage mass height) = 0 := by
  let S : ℝ := xiHeightBudgetWeightedSum mass height
  let K : ℝ := xiHeightBudgetTotalMass mass
  have hsplit :
      ∑ j, mass j * (height j - S / K) = S - (S / K) * K := by
    calc
      ∑ j, mass j * (height j - S / K) = ∑ j, (mass j * height j - (S / K) * mass j) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        ring
      _ = (∑ j, mass j * height j) - ∑ j, (S / K) * mass j := by
        rw [Finset.sum_sub_distrib]
      _ = S - (S / K) * K := by
        simp [S, K, xiHeightBudgetWeightedSum, xiHeightBudgetTotalMass, Finset.mul_sum]
  calc
    ∑ j, mass j * (height j - xiHeightBudgetAverage mass height) = ∑ j, mass j * (height j - S / K) := by
      simp [S, K, xiHeightBudgetAverage]
    _ = S - (S / K) * K := hsplit
    _ = 0 := by
      field_simp [K, htotal_ne]
      ring_nf

/-- Paper label: `thm:xi-defect-entropy-height-budget-variance-gap`. Summing the concrete
second-order bound over the finite family yields the explicit variance-gap correction to the
Jensen exponential height budget. -/
theorem paper_xi_defect_entropy_height_budget_variance_gap
    (D : XiDefectEntropyHeightBudgetData) :
    D.defectEntropy <= D.exponentialHeightBound - D.varianceGapTerm := by
  have htotal_ne : xiHeightBudgetTotalMass D.mass ≠ 0 := ne_of_gt D.totalMass_pos
  let A : ℝ := 1 - Real.exp (-D.averageHeight)
  let B : Fin D.κ → ℝ := fun j => Real.exp (-D.averageHeight) * (D.height j - D.averageHeight)
  let C : Fin D.κ → ℝ := fun j => D.curvatureLower / 2 * (D.height j - D.averageHeight) ^ 2
  have hcenter :
      ∑ j, D.mass j * (D.height j - D.averageHeight) = 0 := by
    simpa [XiDefectEntropyHeightBudgetData.averageHeight] using
      xi_height_budget_centered_sum_eq_zero D.mass D.height htotal_ne
  have hsum :
      D.defectEntropy ≤
        ∑ j,
          D.mass j *
            ((1 - Real.exp (-D.averageHeight)) +
              Real.exp (-D.averageHeight) * (D.height j - D.averageHeight) -
              D.curvatureLower / 2 * (D.height j - D.averageHeight) ^ 2) := by
    unfold XiDefectEntropyHeightBudgetData.defectEntropy
    refine Finset.sum_le_sum ?_
    intro j hj
    exact mul_le_mul_of_nonneg_left (D.pointwise_second_order j) (D.mass_nonneg j)
  have hsplit :
      ∑ j, D.mass j * (A + B j - C j) =
        ∑ j, D.mass j * A + ∑ j, D.mass j * B j - ∑ j, D.mass j * C j := by
    calc
      ∑ j, D.mass j * (A + B j - C j) = ∑ j, (D.mass j * A + D.mass j * B j - D.mass j * C j) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        ring
      _ = ∑ j, D.mass j * A + ∑ j, D.mass j * B j - ∑ j, D.mass j * C j := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hA :
      ∑ j, D.mass j * A = xiHeightBudgetTotalMass D.mass * A := by
    simp [A, xiHeightBudgetTotalMass, Finset.sum_mul]
  have hB :
      ∑ j, D.mass j * B j =
        Real.exp (-D.averageHeight) * ∑ j, D.mass j * (D.height j - D.averageHeight) := by
    calc
      ∑ j, D.mass j * B j =
          ∑ j, Real.exp (-D.averageHeight) * (D.mass j * (D.height j - D.averageHeight)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [B]
            ring
      _ = Real.exp (-D.averageHeight) * ∑ j, D.mass j * (D.height j - D.averageHeight) := by
            rw [Finset.mul_sum]
  have hC :
      ∑ j, D.mass j * C j = D.curvatureLower / 2 * xiHeightBudgetCenteredSquareSum D.mass D.height := by
    calc
      ∑ j, D.mass j * C j =
          ∑ j, D.curvatureLower / 2 * (D.mass j * (D.height j - D.averageHeight) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [C]
            ring
      _ = D.curvatureLower / 2 * xiHeightBudgetCenteredSquareSum D.mass D.height := by
            rw [← Finset.mul_sum]
            simp [xiHeightBudgetCenteredSquareSum, XiDefectEntropyHeightBudgetData.averageHeight]
  calc
    D.defectEntropy ≤
        ∑ j,
          D.mass j *
            ((1 - Real.exp (-D.averageHeight)) +
              Real.exp (-D.averageHeight) * (D.height j - D.averageHeight) -
              D.curvatureLower / 2 * (D.height j - D.averageHeight) ^ 2) := hsum
    _ = ∑ j, D.mass j * A + ∑ j, D.mass j * B j - ∑ j, D.mass j * C j := by
          simpa [A, B, C] using hsplit
    _ =
        xiHeightBudgetTotalMass D.mass * (1 - Real.exp (-D.averageHeight)) +
          Real.exp (-D.averageHeight) * ∑ j, D.mass j * (D.height j - D.averageHeight) -
          D.curvatureLower / 2 * xiHeightBudgetCenteredSquareSum D.mass D.height := by
          rw [hA, hB, hC]
    _ = xiHeightBudgetTotalMass D.mass * (1 - Real.exp (-D.averageHeight)) -
          D.curvatureLower / 2 * xiHeightBudgetCenteredSquareSum D.mass D.height := by
          rw [hcenter, mul_zero, add_zero]
    _ = D.exponentialHeightBound - D.varianceGapTerm := by
          rw [XiDefectEntropyHeightBudgetData.exponentialHeightBound,
            XiDefectEntropyHeightBudgetData.varianceGapTerm,
            XiDefectEntropyHeightBudgetData.centeredSquareSum]

end Omega.Zeta
