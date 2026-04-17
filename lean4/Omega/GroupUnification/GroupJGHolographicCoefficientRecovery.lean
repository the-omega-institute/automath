import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic

namespace Omega.GroupUnification

/-- The base polynomial reconstructed from its root list and leading coefficient. -/
def groupJGBasePolynomial (aN : ℝ) (roots : List ℝ) (t : ℝ) : ℝ :=
  aN * (roots.map (fun z => t - z)).prod

/-- The constant coefficient determined by the root list and the leading coefficient. -/
def groupJGConstantCoeff (aN : ℝ) (roots : List ℝ) : ℝ :=
  aN * (roots.map fun z => -z).prod

/-- The top Laurent coefficient of `Q_r (r t)`. -/
def groupJGTopLaurentCoeff (aN : ℝ) (roots : List ℝ) (t : ℝ) : ℝ :=
  aN ^ 2 * (roots.map (fun z => z ^ 2 - t * z)).prod

/-- The bottom Laurent coefficient of `Q_r (r t)`. -/
def groupJGBottomLaurentCoeff (aN : ℝ) : ℝ :=
  aN ^ 2

theorem groupJG_root_factorization (roots : List ℝ) (t : ℝ) :
    (roots.map (fun z => z ^ 2 - t * z)).prod =
      (roots.map fun z => -z).prod * (roots.map (fun z => t - z)).prod := by
  induction roots with
  | nil =>
      simp
  | cons z zs ih =>
      simp [ih]
      ring

/-- The top Laurent coefficient recovers `a₀ P(t)`, while the bottom Laurent coefficient is
the square of the leading coefficient.
    thm:group-jg-holographic-coefficient-recovery -/
theorem paper_group_jg_holographic_coefficient_recovery (aN : ℝ) (roots : List ℝ) (t : ℝ) :
    groupJGTopLaurentCoeff aN roots t =
      groupJGConstantCoeff aN roots * groupJGBasePolynomial aN roots t ∧
      groupJGBottomLaurentCoeff aN = aN ^ 2 := by
  constructor
  · rw [groupJGTopLaurentCoeff, groupJGConstantCoeff, groupJGBasePolynomial,
      groupJG_root_factorization]
    ring
  · rfl

end Omega.GroupUnification
