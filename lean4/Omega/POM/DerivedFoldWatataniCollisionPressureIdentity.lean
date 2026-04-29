import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.OperatorAlgebra.FoldCenterExpectationIndexCollision2

namespace Omega.POM

open Omega.OperatorAlgebra

/-- Derived bridge package for the Watatani/collision-pressure comparison: the Watatani index
trace is the normalized second collision moment, and the `q = 2` pressure anchor agrees with the
equivalent entropy-side logarithmic normalization. -/
def DerivedFoldWatataniCollisionPressureIdentityLaw : Prop :=
  (∀ {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X]
    (fold : Ω → X) (m : ℕ) (_hcard : Fintype.card Ω = 2 ^ m),
      foldCenterExpectationTraceOfIndex fold =
        foldCenterExpectationSecondCollisionMoment fold / 2 ^ m) ∧
  ∀ r2 : ℝ, 0 < r2 →
    Real.log r2 - Real.log 2 = Real.log 2 - Real.log (4 / r2)

/-- Paper label: `thm:derived-fold-watatani-collision-pressure-identity`.
The Watatani trace identity comes directly from the center-expectation package, and the `q = 2`
pressure anchor is the elementary logarithmic rewrite `log r₂ - log 2 = log 2 - log (4 / r₂)`. -/
theorem paper_derived_fold_watatani_collision_pressure_identity :
    DerivedFoldWatataniCollisionPressureIdentityLaw := by
  refine ⟨?_, ?_⟩
  · intro Ω X _ _ _ _ fold m hcard
    exact (paper_op_algebra_fold_center_expectation_index_collision2 fold m hcard).2.2
  · intro r2 hr2
    have hr2ne : r2 ≠ 0 := ne_of_gt hr2
    have hratio_ne : (4 / r2 : ℝ) ≠ 0 := by
      exact div_ne_zero (by norm_num) hr2ne
    have hratio : r2 / 2 = 2 / (4 / r2) := by
      field_simp [hr2ne]
      ring
    calc
      Real.log r2 - Real.log 2 = Real.log (r2 / 2) := by
        rw [Real.log_div hr2ne (by norm_num : (2 : ℝ) ≠ 0)]
      _ = Real.log (2 / (4 / r2)) := by rw [hratio]
      _ = Real.log 2 - Real.log (4 / r2) := by
        rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hratio_ne]

end Omega.POM
