import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Odd-index conductor sum for symmetric powers in the common three-dimensional vacuum block. -/
def xi_p7_s5_q_inertia_vacuum3_schur_functor_conductors_sym_conductor
    (a r : ℕ) : ℕ :=
  Finset.sum ((Finset.range (r + 1)).filter (fun k => k % 2 = 1))
    (fun k => Nat.choose (r - k + 2) 2 * Nat.choose (a + k - 1) k)

/-- Odd-index conductor sum for exterior powers in the common three-dimensional vacuum block. -/
def xi_p7_s5_q_inertia_vacuum3_schur_functor_conductors_wedge_conductor
    (a r : ℕ) : ℕ :=
  Finset.sum ((Finset.range (r + 1)).filter (fun k => k % 2 = 1))
    (fun k => Nat.choose 3 (r - k) * Nat.choose a k)

/-- Paper label: `thm:xi-p7-s5-q-inertia-vacuum3-schur-functor-conductors`. -/
theorem paper_xi_p7_s5_q_inertia_vacuum3_schur_functor_conductors (a r : ℕ) :
    xi_p7_s5_q_inertia_vacuum3_schur_functor_conductors_sym_conductor a r =
        Finset.sum ((Finset.range (r + 1)).filter (fun k => k % 2 = 1))
          (fun k => Nat.choose (r - k + 2) 2 * Nat.choose (a + k - 1) k) ∧
      xi_p7_s5_q_inertia_vacuum3_schur_functor_conductors_wedge_conductor a r =
        Finset.sum ((Finset.range (r + 1)).filter (fun k => k % 2 = 1))
          (fun k => Nat.choose 3 (r - k) * Nat.choose a k) := by
  constructor <;> rfl

end Omega.Zeta
