import Mathlib

namespace Omega.Conclusion

/-- Positive part of a real number. -/
def positivePart (x : ℝ) : ℝ :=
  max x 0

/-- The positive-part tail sum appearing in the Hardy-Littlewood-Polya criterion. -/
def tailPositiveSum (d : List ℝ) (u : ℝ) : ℝ :=
  (d.map fun t => positivePart (t - u)).sum

/-- A centered truncated-mass capacity curve. Writing `min t u = t - (t - u)_+` identifies this
curve with the negative positive-part tail sum, so pointwise comparison of the curves matches the
tail-sum order. -/
def capacityCurve (d : List ℝ) (u : ℝ) : ℝ :=
  (d.map fun t => min t u - t).sum

/-- Majorization encoded by domination of all positive-part tail sums. -/
def majorizes (d e : List ℝ) : Prop :=
  ∀ u : ℝ, tailPositiveSum e u ≤ tailPositiveSum d u

lemma min_sub_self_eq_neg_positivePart (t u : ℝ) :
    min t u - t = -positivePart (t - u) := by
  unfold positivePart
  by_cases h : t ≤ u
  · rw [min_eq_left h, max_eq_right]
    · ring
    · linarith
  · have hu : u ≤ t := le_of_not_ge h
    rw [min_eq_right hu, max_eq_left]
    · ring
    · linarith

lemma capacityCurve_eq_neg_tailPositiveSum (d : List ℝ) (u : ℝ) :
    capacityCurve d u = -tailPositiveSum d u := by
  induction d with
  | nil =>
      simp [capacityCurve, tailPositiveSum]
  | cons t d ih =>
      calc
        capacityCurve (t :: d) u = (min t u - t) + capacityCurve d u := by
          simp [capacityCurve]
        _ = -positivePart (t - u) - tailPositiveSum d u := by
          rw [min_sub_self_eq_neg_positivePart, ih]
          ring
        _ = -(positivePart (t - u) + tailPositiveSum d u) := by
          ring
        _ = -tailPositiveSum (t :: d) u := by
          simp [tailPositiveSum]

/-- Paper label: `thm:conclusion-capacity-majorization-schur-hardness`. -/
theorem paper_conclusion_capacity_majorization_schur_hardness (d e : List ℝ) :
    majorizes d e ↔ ∀ u : ℝ, capacityCurve d u ≤ capacityCurve e u := by
  constructor
  · intro h u
    rw [capacityCurve_eq_neg_tailPositiveSum, capacityCurve_eq_neg_tailPositiveSum]
    linarith [h u]
  · intro h u
    have hu := h u
    rw [capacityCurve_eq_neg_tailPositiveSum, capacityCurve_eq_neg_tailPositiveSum] at hu
    linarith

end Omega.Conclusion
