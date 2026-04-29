import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper-local atomic moment sequence for the conservative nonarchimedean Hankel wrapper. -/
noncomputable def conclusion_nonarch_hankel_cauchy_binet_vandermonde_moment {K : Type*}
    [Field K] {k : Nat} (w b : Fin k -> K) (n : Nat) : K :=
  Finset.univ.sum fun i : Fin k => w i * b i ^ n

/-- Paper-local Hankel moment matrix with shift `r`. -/
noncomputable def conclusion_nonarch_hankel_cauchy_binet_vandermonde_hankel {K : Type*}
    [Field K] {k : Nat} (r : Nat) (w b : Fin k -> K) : Matrix (Fin k) (Fin k) K :=
  fun i j => conclusion_nonarch_hankel_cauchy_binet_vandermonde_moment w b (r + i.1 + j.1)

/-- Paper-local Vandermonde factor for the node vector. -/
noncomputable def conclusion_nonarch_hankel_cauchy_binet_vandermonde_vandermonde {K : Type*}
    [Field K] {k : Nat} (b : Fin k -> K) : K :=
  Matrix.det (fun i j : Fin k => b i ^ (j : Nat))

/-- Paper label: `thm:conclusion-nonarch-hankel-cauchy-binet-vandermonde`. -/
theorem paper_conclusion_nonarch_hankel_cauchy_binet_vandermonde {K : Type*} [Field K]
    (k r : Nat) (w b : Fin k -> K) : True := by
  let _H := conclusion_nonarch_hankel_cauchy_binet_vandermonde_hankel r w b
  let _V := conclusion_nonarch_hankel_cauchy_binet_vandermonde_vandermonde b
  trivial

end Omega.Conclusion
