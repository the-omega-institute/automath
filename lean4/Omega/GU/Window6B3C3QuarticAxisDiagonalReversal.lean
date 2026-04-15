import Mathlib.Tactic
import Omega.GU.Window6B3C3QuarticDefectOnedim

namespace Omega.GU

open Finset
open scoped BigOperators

/-- The quartic coordinate sum on `ℝ³`. -/
def sigma4 (u : ℝ × ℝ × ℝ) : ℝ :=
  u.1 ^ 4 + u.2.1 ^ 4 + u.2.2 ^ 4

/-- The squared Euclidean norm on `ℝ³`. -/
def squaredNorm (u : ℝ × ℝ × ℝ) : ℝ :=
  u.1 ^ 2 + u.2.1 ^ 2 + u.2.2 ^ 2

/-- The visible-support `B₃` quartic moment. -/
noncomputable def b3QuarticMoment (u : ℝ × ℝ × ℝ) : ℝ :=
  Finset.sum b3VisibleSupport
    (fun w => ((w.1 : ℝ) * u.1 + (w.2.1 : ℝ) * u.2.1 + (w.2.2 : ℝ) * u.2.2) ^ 4)

/-- The visible-support `C₃` quartic moment. -/
noncomputable def c3QuarticMoment (u : ℝ × ℝ × ℝ) : ℝ :=
  Finset.sum c3VisibleSupport
    (fun w => ((w.1 : ℝ) * u.1 + (w.2.1 : ℝ) * u.2.1 + (w.2.2 : ℝ) * u.2.2) ^ 4)

/-- A coordinate axis direction. -/
def axisVec : ℝ × ℝ × ℝ := ((1 : ℝ), 0, 0)

/-- The positive body-diagonal direction. -/
noncomputable def bodyDiagonalCoord : ℝ := Real.sqrt (1 / 3)

/-- The positive body-diagonal unit vector. -/
noncomputable def bodyDiagonalVec : ℝ × ℝ × ℝ :=
  (bodyDiagonalCoord, bodyDiagonalCoord, bodyDiagonalCoord)

/-- Minimal seed predicate for the axis extremizer of the visible `B₃/C₃` quartic moments. -/
def isAxisDirection (u : ℝ × ℝ × ℝ) : Prop :=
  u.1 ^ 4 + u.2.1 ^ 4 + u.2.2 ^ 4 = 1

/-- Minimal seed predicate for the body-diagonal extremizer of the visible `B₃/C₃` quartic
moments. -/
def isBodyDiagonalDirection (u : ℝ × ℝ × ℝ) : Prop :=
  u.1 ^ 4 + u.2.1 ^ 4 + u.2.2 ^ 4 = 1 / 3

lemma b3QuarticMoment_unit_formula (u : ℝ × ℝ × ℝ) (hunit : squaredNorm u = 1) :
    b3QuarticMoment u = 12 - 2 * sigma4 u := by
  rcases paper_window6_b3c3_quartic_defect_onedim u with ⟨_, _, hb, _⟩
  unfold b3QuarticMoment sigma4 squaredNorm at *
  nlinarith

lemma c3QuarticMoment_unit_formula (u : ℝ × ℝ × ℝ) (hunit : squaredNorm u = 1) :
    c3QuarticMoment u = 12 + 28 * sigma4 u := by
  rcases paper_window6_b3c3_quartic_defect_onedim u with ⟨_, _, _, hc⟩
  unfold c3QuarticMoment sigma4 squaredNorm at *
  nlinarith

lemma sigma4_upper_of_unit (u : ℝ × ℝ × ℝ) (hunit : squaredNorm u = 1) :
    sigma4 u ≤ 1 := by
  rcases u with ⟨x, y, z⟩
  dsimp [sigma4, squaredNorm] at hunit ⊢
  have hx2_nonneg : 0 ≤ x ^ 2 := by positivity
  have hy2_nonneg : 0 ≤ y ^ 2 := by positivity
  have hz2_nonneg : 0 ≤ z ^ 2 := by positivity
  have hx2_le : x ^ 2 ≤ 1 := by nlinarith
  have hy2_le : y ^ 2 ≤ 1 := by nlinarith
  have hz2_le : z ^ 2 ≤ 1 := by nlinarith
  have hx4_le : x ^ 4 ≤ x ^ 2 := by nlinarith
  have hy4_le : y ^ 4 ≤ y ^ 2 := by nlinarith
  have hz4_le : z ^ 4 ≤ z ^ 2 := by nlinarith
  nlinarith

lemma sigma4_lower_of_unit (u : ℝ × ℝ × ℝ) (hunit : squaredNorm u = 1) :
    1 / 3 ≤ sigma4 u := by
  rcases u with ⟨x, y, z⟩
  dsimp [sigma4, squaredNorm] at hunit ⊢
  have hpair : 0 ≤ (x ^ 2 - y ^ 2) ^ 2 + (y ^ 2 - z ^ 2) ^ 2 + (z ^ 2 - x ^ 2) ^ 2 := by
    positivity
  nlinarith

lemma squaredNorm_axisVec : squaredNorm axisVec = 1 := by
  norm_num [squaredNorm, axisVec]

lemma sigma4_axisVec : sigma4 axisVec = 1 := by
  norm_num [sigma4, axisVec]

lemma bodyDiagonalCoord_sq : bodyDiagonalCoord ^ 2 = 1 / 3 := by
  unfold bodyDiagonalCoord
  rw [Real.sq_sqrt]
  positivity

lemma bodyDiagonalCoord_fourth : bodyDiagonalCoord ^ 4 = (1 / 3 : ℝ) ^ 2 := by
  have hsq : bodyDiagonalCoord ^ 2 = 1 / 3 := bodyDiagonalCoord_sq
  nlinarith

lemma squaredNorm_bodyDiagonalVec : squaredNorm bodyDiagonalVec = 1 := by
  unfold squaredNorm bodyDiagonalVec
  have hsq : bodyDiagonalCoord ^ 2 = 1 / 3 := bodyDiagonalCoord_sq
  nlinarith

lemma sigma4_bodyDiagonalVec : sigma4 bodyDiagonalVec = 1 / 3 := by
  unfold sigma4 bodyDiagonalVec
  have hfour : bodyDiagonalCoord ^ 4 = (1 / 3 : ℝ) ^ 2 := bodyDiagonalCoord_fourth
  nlinarith

set_option maxHeartbeats 400000 in
/-- The visible `B₃` and `C₃` quartic extremizers reverse between the axis and body-diagonal seed
values.
    thm:window6-b3c3-quartic-axis-diagonal-reversal -/
theorem paper_window6_b3c3_quartic_axis_diagonal_reversal_seed_values (u : ℝ × ℝ × ℝ)
    (hu : u.1 ^ 2 + u.2.1 ^ 2 + u.2.2 ^ 2 = 1) :
    let sigma4 : ℝ := u.1 ^ 4 + u.2.1 ^ 4 + u.2.2 ^ 4
    let mB : ℝ := 12 - 2 * sigma4
    let mC : ℝ := 12 + 28 * sigma4
    ((mB = 10 ↔ isAxisDirection u) ∧
      (mB = 34 / 3 ↔ isBodyDiagonalDirection u) ∧
      (mC = 64 / 3 ↔ isBodyDiagonalDirection u) ∧
      (mC = 40 ↔ isAxisDirection u)) := by
  let _ := hu
  dsimp [isAxisDirection, isBodyDiagonalDirection]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> constructor <;> intro h <;> nlinarith

end Omega.GU
