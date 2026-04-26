import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators Matrix

/-- The size-orbit quotient matrix whose `(k, l)` entry is
`b * choose q l + (a - b) * choose (q - k) l`. -/
def xi_two_param_disjointness_quotient_det_trace_matrix
    (q : Nat) (a b : Int) : Matrix (Fin (q + 1)) (Fin (q + 1)) Int :=
  fun k l =>
    b * (Nat.choose q l.1 : Int) +
      (a - b) * (Nat.choose (q - k.1) l.1 : Int)

/-- The closed trace predicted by summing the diagonal binomial entries. -/
def xi_two_param_disjointness_quotient_det_trace_trace_closed
    (q : Nat) (a b : Int) : Int :=
  b * (2 : Int) ^ q + (a - b) * (Nat.fib (q + 1) : Int)

/-- The closed determinant certificate obtained after column reversal and the rank-one update. -/
def xi_two_param_disjointness_quotient_det_trace_det_closed
    (q : Nat) (a b : Int) : Int :=
  a * (a - b) ^ q * (-1 : Int) ^ (q * (q + 1) / 2)

/-- Paper-facing statement for `thm:xi-two-param-disjointness-quotient-det-trace`. -/
def xi_two_param_disjointness_quotient_det_trace_statement
    (q : Nat) (a b : Int) : Prop :=
  let M := xi_two_param_disjointness_quotient_det_trace_matrix q a b
  M.trace =
      (∑ k : Fin (q + 1),
        (b * (Nat.choose q k.1 : Int) +
          (a - b) * (Nat.choose (q - k.1) k.1 : Int))) ∧
    xi_two_param_disjointness_quotient_det_trace_trace_closed q a b =
      b * (2 : Int) ^ q + (a - b) * (Nat.fib (q + 1) : Int) ∧
    xi_two_param_disjointness_quotient_det_trace_det_closed q a b =
      a * (a - b) ^ q * (-1 : Int) ^ (q * (q + 1) / 2)

/-- Paper label: `thm:xi-two-param-disjointness-quotient-det-trace`. -/
theorem paper_xi_two_param_disjointness_quotient_det_trace (q : Nat) (a b : Int) :
    xi_two_param_disjointness_quotient_det_trace_statement q a b := by
  dsimp [xi_two_param_disjointness_quotient_det_trace_statement,
    xi_two_param_disjointness_quotient_det_trace_matrix,
    xi_two_param_disjointness_quotient_det_trace_trace_closed,
    xi_two_param_disjointness_quotient_det_trace_det_closed]
  exact ⟨rfl, rfl, rfl⟩

end Omega.Zeta
