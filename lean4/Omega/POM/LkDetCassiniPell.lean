import Omega.Folding.FibonacciPolynomial

namespace Omega

open Polynomial

/-- Paper label: `prop:pom-Lk-det-cassini-pell`. -/
theorem paper_pom_lk_det_cassini_pell (k : Nat) (hk : 1 ≤ k) :
    detPoly (k + 1) * detPoly (k - 1) - detPoly k ^ 2 = X := by
  exact detPoly_cassini_pell k hk

end Omega
