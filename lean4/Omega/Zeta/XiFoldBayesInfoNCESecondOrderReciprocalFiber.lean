import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.POM.BayesInfonceThirdOrderLargeK

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- Fold push-forward entropy written from concrete fiber multiplicities. -/
def xi_fold_bayes_infonce_second_order_reciprocal_fiber_entropy
    {X : Type} [Fintype X] (m : ℕ) (d : X → ℕ) : ℝ :=
  -∑ x : X,
    ((d x : ℝ) / ((2 ^ m : ℕ) : ℝ)) *
      Real.log ((d x : ℝ) / ((2 ^ m : ℕ) : ℝ))

/-- The reciprocal-fiber invariant `∑ₓ 2^m / dₘ(x)`. -/
def xi_fold_bayes_infonce_second_order_reciprocal_fiber_sum
    {X : Type} [Fintype X] (m : ℕ) (d : X → ℕ) : ℝ :=
  ∑ x : X, ((2 ^ m : ℕ) : ℝ) / (d x : ℝ)

/-- The second-order `n = K - 1` Fold Bayes--InfoNCE main term after collecting powers of `n`. -/
def xi_fold_bayes_infonce_second_order_reciprocal_fiber_main
    {X : Type} [Fintype X] (m : ℕ) (d : X → ℕ) (n : ℝ) : ℝ :=
  Real.log n - xi_fold_bayes_infonce_second_order_reciprocal_fiber_entropy m d +
    ((Fintype.card X : ℝ) + 1) / (2 * n) +
      (xi_fold_bayes_infonce_second_order_reciprocal_fiber_sum m d -
          6 * (Fintype.card X : ℝ) - 1) / (12 * n ^ 2)

/-- Paper label: `thm:xi-fold-bayes-infonce-second-order-reciprocal-fiber`.
Specializing the third-order Bayes--InfoNCE expansion to Fold and expanding
`log (n + 1)` gives the displayed reciprocal-fiber second-order coefficient. -/
theorem paper_xi_fold_bayes_infonce_second_order_reciprocal_fiber
    {X : Type} [Fintype X] (m K : ℕ) (d : X → ℕ) (Lstar Sminus1 n Rlog C Sm2 : ℝ)
    (hthird :
      |Lstar - (Real.log (K : ℝ) -
          xi_fold_bayes_infonce_second_order_reciprocal_fiber_entropy m d +
          ((Fintype.card X : ℝ) - 1) / (2 * n) +
          (Sminus1 - 6 * (Fintype.card X : ℝ) + 5) /
            (12 * n ^ 2))| ≤
        C / (n ^ 3) * Sm2)
    (hreciprocal :
      Sminus1 = xi_fold_bayes_infonce_second_order_reciprocal_fiber_sum m d)
    (hlog :
      Real.log (K : ℝ) =
        Real.log n + 1 / n - 1 / (2 * n ^ 2) + Rlog) :
    |Lstar -
        xi_fold_bayes_infonce_second_order_reciprocal_fiber_main m d n| ≤
      C / (n ^ 3) * Sm2 + |Rlog| := by
  let oldMain : ℝ :=
    Real.log (K : ℝ) - xi_fold_bayes_infonce_second_order_reciprocal_fiber_entropy m d +
      ((Fintype.card X : ℝ) - 1) / (2 * n) +
      (Sminus1 - 6 * (Fintype.card X : ℝ) + 5) / (12 * n ^ 2)
  let newMain : ℝ :=
    xi_fold_bayes_infonce_second_order_reciprocal_fiber_main m d n
  have hcollect : oldMain = newMain + Rlog := by
    dsimp [oldMain, newMain, xi_fold_bayes_infonce_second_order_reciprocal_fiber_main]
    rw [hlog, hreciprocal]
    ring_nf
  have hrewrite : Lstar - newMain = (Lstar - oldMain) + Rlog := by
    rw [hcollect]
    ring
  calc
    |Lstar - newMain| = |(Lstar - oldMain) + Rlog| := by rw [hrewrite]
    _ ≤ |Lstar - oldMain| + |Rlog| := abs_add_le _ _
    _ ≤ C / (n ^ 3) * Sm2 + |Rlog| := by
      simpa [add_comm] using add_le_add_right (by simpa [oldMain] using hthird) |Rlog|

end

end Omega.Zeta
