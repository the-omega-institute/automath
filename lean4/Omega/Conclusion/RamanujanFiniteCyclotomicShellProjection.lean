import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-ramanujan-finite-cyclotomic-shell-projection`. -/
theorem paper_conclusion_ramanujan_finite_cyclotomic_shell_projection
    {A J R : Type*} [Fintype A] [Fintype J] [CommSemiring R] (P Pcore : A → R)
    (m : J → R) (atom : J → A → R)
    (hP : ∀ a, P a = Pcore a + ∑ j : J, m j * atom j a) :
    (∑ a : A, P a) =
      (∑ a : A, Pcore a) + ∑ j : J, m j * (∑ a : A, atom j a) := by
  classical
  calc
    (∑ a : A, P a) = ∑ a : A, (Pcore a + ∑ j : J, m j * atom j a) := by
      exact Finset.sum_congr rfl (fun a _ha => hP a)
    _ = (∑ a : A, Pcore a) + ∑ a : A, ∑ j : J, m j * atom j a := by
      rw [Finset.sum_add_distrib]
    _ = (∑ a : A, Pcore a) + ∑ j : J, ∑ a : A, m j * atom j a := by
      rw [Finset.sum_comm]
    _ = (∑ a : A, Pcore a) + ∑ j : J, m j * (∑ a : A, atom j a) := by
      simp [Finset.mul_sum]

end Omega.Conclusion
