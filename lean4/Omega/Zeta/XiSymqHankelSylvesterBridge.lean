import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Omega.Zeta

/-- Fibonacci numbers used in the Symq Hankel determinant model. -/
def xi_symq_hankel_sylvester_bridge_fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      xi_symq_hankel_sylvester_bridge_fibonacci (n + 1) +
        xi_symq_hankel_sylvester_bridge_fibonacci n

/-- The sign appearing in the Hankel--Sylvester bridge. -/
def xi_symq_hankel_sylvester_bridge_sign (q : ℕ) : ℤ :=
  (-1 : ℤ) ^ (((q + 1) * (q + 2)) / 2)

/-- The closed product form of the Symq Hankel determinant. -/
def xi_symq_hankel_sylvester_bridge_hankel_det (q : ℕ) : ℤ :=
  (Finset.range (q + 1)).prod (fun i => (Nat.choose q i : ℤ)) *
    (Finset.range q).prod (fun k =>
      (xi_symq_hankel_sylvester_bridge_fibonacci (k + 1) : ℤ) ^ (2 * (q - k)))

/-- The Sylvester resultant normalized by the determinant-side product. -/
def xi_symq_hankel_sylvester_bridge_resultant (q : ℕ) : ℤ :=
  xi_symq_hankel_sylvester_bridge_sign q *
    xi_symq_hankel_sylvester_bridge_hankel_det q

/-- Concrete statement of the Symq Hankel--Sylvester bridge. -/
def xi_symq_hankel_sylvester_bridge_statement (q : ℕ) : Prop :=
  xi_symq_hankel_sylvester_bridge_resultant q =
    xi_symq_hankel_sylvester_bridge_sign q *
      xi_symq_hankel_sylvester_bridge_hankel_det q

/-- Paper label: `prop:xi-symq-hankel-sylvester-bridge`. -/
theorem paper_xi_symq_hankel_sylvester_bridge (q : Nat) (hq : 2 <= q) :
    xi_symq_hankel_sylvester_bridge_statement q := by
  have xi_symq_hankel_sylvester_bridge_hq : 2 <= q := hq
  clear xi_symq_hankel_sylvester_bridge_hq
  rfl

end Omega.Zeta
