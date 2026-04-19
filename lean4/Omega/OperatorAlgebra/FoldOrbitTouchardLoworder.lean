import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldOrbitMgfFiberFactorization

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- The truncated Bell factor contributed by one orbit fiber of size `n`. -/
def truncatedBell (q n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond q k

/-- The Touchard polynomial evaluated at `x`. -/
def touchardPolynomial (q x : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (q + 1), Nat.stirlingSecond q k * x ^ k

/-- The low-order Touchard coefficient obtained by specializing the polynomial at `x = 1`. -/
def touchardCoefficientAtOne (q : ℕ) : ℕ :=
  touchardPolynomial q 1

/-- The low-order orbit count coming from the truncated Bell factors. -/
def foldOrbitBellLowOrder {m : ℕ} (N : Fin m → ℕ) (q : ℕ) : ℕ :=
  ∏ d, truncatedBell q (N d)

/-- The same low-order coefficient written in Touchard form. -/
def foldOrbitTouchardLowOrder {m : ℕ} (_N : Fin m → ℕ) (q : ℕ) : ℕ :=
  ∏ _d : Fin m, touchardCoefficientAtOne q

private theorem truncatedBell_eq_touchardCoefficientAtOne (q n : ℕ) (hq : q ≤ n) :
    truncatedBell q n = touchardCoefficientAtOne q := by
  rw [truncatedBell, touchardCoefficientAtOne, touchardPolynomial]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hq
  induction r with
  | zero =>
      simp
  | succ r ih =>
      rw [show q + (r + 1) + 1 = (q + r + 1) + 1 by omega, Finset.sum_range_succ]
      have ih' := ih (by omega)
      rw [ih']
      have hzero : Nat.stirlingSecond q (q + r + 1) = 0 := by
        apply Nat.stirlingSecond_eq_zero_of_lt
        omega
      simp [hzero]

/-- In the low-order regime `q ≤ d_min`, every truncated Bell factor is already the full Bell sum,
so the Burnside-factorized fold-orbit count matches the Touchard specialization term-by-term.
    thm:op-algebra-fold-orbit-touchard-loworder -/
theorem paper_op_algebra_fold_orbit_touchard_loworder {m : ℕ}
    (N : Fin m → ℕ) (q : ℕ) (hq : ∀ d, q ≤ N d) :
    foldOrbitMgf N (1 : ℚ) = ∏ d : Fin m, fiberFixedPointMgf (N d) (1 : ℚ) ∧
      foldOrbitBellLowOrder N q = foldOrbitTouchardLowOrder N q := by
  refine ⟨(paper_op_algebra_fold_orbit_mgf_fiber_factorization N (1 : ℚ)).2, ?_⟩
  unfold foldOrbitBellLowOrder foldOrbitTouchardLowOrder
  refine Finset.prod_congr rfl ?_
  intro d hd
  exact truncatedBell_eq_touchardCoefficientAtOne q (N d) (hq d)

end Omega.OperatorAlgebra
