import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

namespace Omega.Zeta

open scoped BigOperators

theorem paper_xi_adams_norm_zero_transport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Complex) (a : ι) (hF : F a = 0) : (∏ x, F x) = 0 := by
  classical
  simpa using Finset.prod_eq_zero (s := Finset.univ) (f := F) (i := a) (Finset.mem_univ a) hF

end Omega.Zeta
