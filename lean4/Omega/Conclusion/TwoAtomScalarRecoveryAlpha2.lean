import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable def twoAtomScalar2 (φ : ℝ) : ℝ := (φ ^ 3 + 1) / 5 - 1

/-- α = 2 specialization of the two-atom scalar.
    cor:conclusion-binfold-single-scalar-recovers-golden-parameter -/
theorem twoAtomScalar2_goldenRatio :
    twoAtomScalar2 Real.goldenRatio = (Real.goldenRatio ^ 3 + 1) / 5 - 1 := rfl

/-- Strict monotonicity on the positive reals.
    cor:conclusion-binfold-single-scalar-recovers-golden-parameter -/
theorem twoAtomScalar2_strictMono {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    twoAtomScalar2 x < twoAtomScalar2 y := by
  unfold twoAtomScalar2
  have hy : 0 < y := lt_trans hx hxy
  have hfac : 0 < x ^ 2 + x * y + y ^ 2 := by positivity
  have hpow : x ^ 3 < y ^ 3 := by
    have : 0 < y ^ 3 - x ^ 3 := by
      rw [show y ^ 3 - x ^ 3 = (y - x) * (x ^ 2 + x * y + y ^ 2) by ring]
      exact mul_pos (sub_pos.mpr hxy) hfac
    linarith
  linarith

/-- Injectivity of the α = 2 scalar on the positive reals.
    cor:conclusion-binfold-single-scalar-recovers-golden-parameter -/
theorem twoAtomScalar2_injective_on_pos :
    Set.InjOn twoAtomScalar2 {φ : ℝ | 0 < φ} := by
  intro x hx y hy hEq
  by_cases hxy : x < y
  · have hstrict := twoAtomScalar2_strictMono hx hxy
    rw [hEq] at hstrict
    exact (lt_irrefl _ hstrict).elim
  · by_cases hyx : y < x
    · have hstrict := twoAtomScalar2_strictMono hy hyx
      rw [hEq] at hstrict
      exact (lt_irrefl _ hstrict).elim
    · linarith

end Omega.Conclusion
