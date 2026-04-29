import Omega.Folding.FibonacciPolynomial

namespace Omega

open Polynomial

/-- Paper label: `cor:pom-Lk-det-lucas-unit`. -/
theorem paper_pom_lk_det_lucas_unit :
    detPoly 0 = 1 ∧ detPoly 1 = 1 + X ∧
      (∀ k : Nat, detPoly (k + 2) = (X + 2) * detPoly (k + 1) - detPoly k) ∧
        (∀ k : Nat,
          (detPoly (k + 2)).eval (-1 : ℤ) =
            (detPoly (k + 1)).eval (-1 : ℤ) - (detPoly k).eval (-1 : ℤ)) := by
  refine ⟨detPoly_zero, detPoly_one, ?_, ?_⟩
  · intro k
    exact detPoly_succ_succ k
  · intro k
    exact detPoly_eval_neg_one_rec k

end Omega
