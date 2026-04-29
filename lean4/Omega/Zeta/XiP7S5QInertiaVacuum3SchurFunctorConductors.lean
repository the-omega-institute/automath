import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:xi-p7-s5-q-inertia-vacuum3-schur-functor-conductors`. -/
theorem paper_xi_p7_s5_q_inertia_vacuum3_schur_functor_conductors :
    (∀ a ∈ ({1, 2, 3} : Finset ℕ),
      (Finset.sum (Finset.range 3) fun k =>
          if Odd k then Nat.choose (2 - k + 2) 2 * Nat.choose (a + k - 1) k else 0) =
        3 * a ∧
      (Finset.sum (Finset.range 3) fun k =>
          if Odd k then Nat.choose 3 (2 - k) * Nat.choose a k else 0) =
        3 * a) := by
  intro a ha
  simp at ha
  rcases ha with rfl | rfl | rfl <;> norm_num [Finset.sum_range_succ, Nat.choose]

end Omega.Zeta
