import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Concrete audited branch-angle witnesses on the unit circle. The three angles are fixed to the
distinguished roots of the auxiliary cubic in the `2 cos t` coordinate. -/
structure PressureUnitCircleBranchAnglesData where
  t1 : ℝ
  t2 : ℝ
  t3 : ℝ
  ht1 : t1 = Real.pi / 3
  ht2 : t2 = 2 * Real.pi / 3
  ht3 : t3 = Real.pi

namespace PressureUnitCircleBranchAnglesData

/-- Audited cubic in the invariant variable `x = 2 cos t`. -/
def branchPolynomial (_D : PressureUnitCircleBranchAnglesData) (x : ℝ) : ℝ :=
  (x - 1) * (x + 1) * (x + 2)

/-- A branch angle is a root of the audited cubic after the `x = 2 cos t` substitution. -/
def isBranchAngle (D : PressureUnitCircleBranchAnglesData) (t : ℝ) : Prop :=
  D.branchPolynomial (2 * Real.cos t) = 0

lemma branchPolynomial_eq_zero_iff (D : PressureUnitCircleBranchAnglesData) (x : ℝ) :
    D.branchPolynomial x = 0 ↔ x = 1 ∨ x = -1 ∨ x = -2 := by
  unfold branchPolynomial
  constructor
  · intro hx
    have hmul : ((x - 1) * (x + 1)) * (x + 2) = 0 := by
      simpa [mul_assoc] using hx
    rcases mul_eq_zero.mp hmul with h12 | h3
    · rcases mul_eq_zero.mp h12 with h1 | h2
      · left
        linarith
      · right
        left
        linarith
    · right
      right
      linarith
  · rintro (rfl | rfl | rfl) <;> ring

lemma isBranchAngle_iff (D : PressureUnitCircleBranchAnglesData) (t : ℝ) :
    D.isBranchAngle t ↔ 2 * Real.cos t = 1 ∨ 2 * Real.cos t = -1 ∨ 2 * Real.cos t = -2 := by
  simpa [isBranchAngle] using D.branchPolynomial_eq_zero_iff (2 * Real.cos t)

end PressureUnitCircleBranchAnglesData

open PressureUnitCircleBranchAnglesData

/-- Paper label: `cor:pressure-unit-circle-branch-angles`.
The audited cubic in `x = 2 cos t` has the three ordered roots `1`, `-1`, `-2`, corresponding on
`(0, π]` to the angles `π/3`, `2π/3`, and `π`. -/
theorem paper_pressure_unit_circle_branch_angles (D : PressureUnitCircleBranchAnglesData) :
    0 < D.t1 ∧ D.t1 < D.t2 ∧ D.t2 < D.t3 ∧ D.t3 ≤ Real.pi ∧ D.isBranchAngle D.t1 ∧
      D.isBranchAngle D.t2 ∧ D.isBranchAngle D.t3 ∧
      (∀ t : ℝ, 0 < t → t ≤ Real.pi → D.isBranchAngle t → t = D.t1 ∨ t = D.t2 ∨ t = D.t3) := by
  have hpi3_mem : Real.pi / 3 ∈ Set.Icc 0 Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  have h2pi3_mem : 2 * Real.pi / 3 ∈ Set.Icc 0 Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  have hpi_mem : Real.pi ∈ Set.Icc 0 Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  have hcos_t2 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    have hrewrite : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [hrewrite, Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  have hbranch1 : D.isBranchAngle D.t1 := by
    rw [D.ht1, PressureUnitCircleBranchAnglesData.isBranchAngle, branchPolynomial,
      Real.cos_pi_div_three]
    ring
  have hbranch2 : D.isBranchAngle D.t2 := by
    rw [D.ht2, PressureUnitCircleBranchAnglesData.isBranchAngle, branchPolynomial, hcos_t2]
    ring
  have hbranch3 : D.isBranchAngle D.t3 := by
    rw [D.ht3, PressureUnitCircleBranchAnglesData.isBranchAngle, branchPolynomial, Real.cos_pi]
    ring
  refine ⟨?_, ?_, ?_, ?_, hbranch1, hbranch2, hbranch3, ?_⟩
  · rw [D.ht1]
    nlinarith [Real.pi_pos]
  · rw [D.ht1, D.ht2]
    nlinarith [Real.pi_pos]
  · rw [D.ht2, D.ht3]
    nlinarith [Real.pi_pos]
  · rw [D.ht3]
  · intro t ht0 htpi ht
    have ht_mem : t ∈ Set.Icc 0 Real.pi := ⟨ht0.le, htpi⟩
    have hroot := (D.isBranchAngle_iff t).mp ht
    rcases hroot with h1 | h2 | h3
    · have hcos : Real.cos t = Real.cos (Real.pi / 3) := by
        rw [Real.cos_pi_div_three]
        linarith
      have ht_eq : t = Real.pi / 3 := Real.injOn_cos ht_mem hpi3_mem hcos
      left
      simpa [D.ht1] using ht_eq
    · have hcos : Real.cos t = Real.cos (2 * Real.pi / 3) := by
        rw [hcos_t2]
        linarith
      have ht_eq : t = 2 * Real.pi / 3 := Real.injOn_cos ht_mem h2pi3_mem hcos
      right
      left
      simpa [D.ht2] using ht_eq
    · have hcos : Real.cos t = Real.cos Real.pi := by
        rw [Real.cos_pi]
        linarith
      have ht_eq : t = Real.pi := Real.injOn_cos ht_mem hpi_mem hcos
      right
      right
      simpa [D.ht3] using ht_eq

end

end Omega.SyncKernelWeighted
