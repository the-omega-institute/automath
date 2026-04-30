import Mathlib.Tactic
import Omega.POM.FiberMultivariateHolographicConservation
import Omega.POM.PathIndSetPolyClosed

namespace Omega.Zeta

open scoped BigOperators

/-- The finite support partition used by the one-variable specialization. -/
def xi_fold_univariate_holographic_conservation_supports (m : ℕ) :
    Finset (Finset (Fin m)) :=
  (Finset.univ : Finset (Fin m)).powerset

/-- Concrete one-variable specialization data for the xi-fold holographic conservation law. The
field `holographicFiber` is the specialized multivariate fiber contribution; the rewrite field
records the independent-set factorization of each fiber. -/
structure xi_fold_univariate_holographic_conservation_data where
  xi_fold_univariate_holographic_conservation_m : ℕ
  xi_fold_univariate_holographic_conservation_z : ℤ
  xi_fold_univariate_holographic_conservation_indsetPolynomial :
    Finset (Fin xi_fold_univariate_holographic_conservation_m) → ℤ
  xi_fold_univariate_holographic_conservation_holographicFiber :
    Finset (Fin xi_fold_univariate_holographic_conservation_m) → ℤ
  xi_fold_univariate_holographic_conservation_fiber_rewrite :
    ∀ S ∈ xi_fold_univariate_holographic_conservation_supports
        xi_fold_univariate_holographic_conservation_m,
      xi_fold_univariate_holographic_conservation_holographicFiber S =
        xi_fold_univariate_holographic_conservation_z ^ S.card *
          xi_fold_univariate_holographic_conservation_indsetPolynomial S
  xi_fold_univariate_holographic_conservation_multivariate_specialization :
    Finset.sum
        (xi_fold_univariate_holographic_conservation_supports
          xi_fold_univariate_holographic_conservation_m)
        xi_fold_univariate_holographic_conservation_holographicFiber =
      Omega.POM.sumOverFibers
        (fun _ : Fin xi_fold_univariate_holographic_conservation_m =>
          xi_fold_univariate_holographic_conservation_z)

/-- The paper-facing one-variable conservation statement: after each fiber is rewritten as
`z^|x|` times its independent-set polynomial, the finite fiber sum is `(1+z)^m`. -/
def xi_fold_univariate_holographic_conservation_statement
    (D : xi_fold_univariate_holographic_conservation_data) : Prop :=
  Finset.sum
      (xi_fold_univariate_holographic_conservation_supports
        D.xi_fold_univariate_holographic_conservation_m)
      (fun S =>
        D.xi_fold_univariate_holographic_conservation_z ^ S.card *
          D.xi_fold_univariate_holographic_conservation_indsetPolynomial S) =
    (1 + D.xi_fold_univariate_holographic_conservation_z) ^
      D.xi_fold_univariate_holographic_conservation_m

/-- Paper label: `thm:xi-fold-univariate-holographic-conservation`. -/
theorem paper_xi_fold_univariate_holographic_conservation
    (D : xi_fold_univariate_holographic_conservation_data) :
    xi_fold_univariate_holographic_conservation_statement D := by
  unfold xi_fold_univariate_holographic_conservation_statement
  calc
    Finset.sum
        (xi_fold_univariate_holographic_conservation_supports
          D.xi_fold_univariate_holographic_conservation_m)
        (fun S =>
          D.xi_fold_univariate_holographic_conservation_z ^ S.card *
            D.xi_fold_univariate_holographic_conservation_indsetPolynomial S)
        =
          Finset.sum
            (xi_fold_univariate_holographic_conservation_supports
              D.xi_fold_univariate_holographic_conservation_m)
            D.xi_fold_univariate_holographic_conservation_holographicFiber := by
          refine Finset.sum_congr rfl ?_
          intro S hS
          exact (D.xi_fold_univariate_holographic_conservation_fiber_rewrite S hS).symm
    _ = Omega.POM.sumOverFibers
          (fun _ : Fin D.xi_fold_univariate_holographic_conservation_m =>
            D.xi_fold_univariate_holographic_conservation_z) :=
          D.xi_fold_univariate_holographic_conservation_multivariate_specialization
    _ = Omega.POM.booleanCubeProduct
          (fun _ : Fin D.xi_fold_univariate_holographic_conservation_m =>
            D.xi_fold_univariate_holographic_conservation_z) := by
          exact Omega.POM.paper_pom_fiber_multivariate_holographic_conservation
            D.xi_fold_univariate_holographic_conservation_m
            (fun _ : Fin D.xi_fold_univariate_holographic_conservation_m =>
              D.xi_fold_univariate_holographic_conservation_z)
    _ = (1 + D.xi_fold_univariate_holographic_conservation_z) ^
          D.xi_fold_univariate_holographic_conservation_m := by
          simp [Omega.POM.booleanCubeProduct]

end Omega.Zeta
