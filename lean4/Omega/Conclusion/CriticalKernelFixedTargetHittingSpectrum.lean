import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-critical-kernel-fixed-target-hitting-spectrum`. -/
theorem paper_conclusion_critical_kernel_fixed_target_hitting_spectrum {α : Type*}
    (d : Nat) (lambda : Fin d -> Rat) (omega : α -> Fin d -> Rat)
    (hit tail : α -> Nat -> Rat)
    (htail : ∀ x k, tail x k = ∑ i, omega x i * lambda i ^ k)
    (hdiff : ∀ x k, hit x (k + 1) = tail x k - tail x (k + 1)) :
    (∀ x k, hit x (k + 1) = ∑ i, omega x i * (1 - lambda i) * lambda i ^ k) ∧
      (∀ x k, tail x k = ∑ i, omega x i * lambda i ^ k) := by
  constructor
  · intro x k
    rw [hdiff, htail x k, htail x (k + 1), ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp [pow_succ]
    ring
  · exact htail

end Omega.Conclusion
