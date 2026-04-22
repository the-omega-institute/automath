import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- The coefficient of `s^k` in the product of a denominator
`1 + a₁ s + ... + a_d s^d` with the sequence generating function of `s_x`. -/
def criticalKernelProductCoeff {α : Type*} (d : ℕ) (a : Fin d → ℚ) (seq : α → ℕ → ℚ)
    (x : α) (k : ℕ) : ℚ :=
  seq x k + ∑ j : Fin d, a j * seq x (k - (j.1 + 1))

/-- Degree bound `deg N_x ≤ d - 1`, encoded coefficientwise. -/
def criticalKernelNumeratorDegreeBound {α : Type*} (d : ℕ) (N : α → ℕ → ℚ) : Prop :=
  ∀ x k, d ≤ k → N x k = 0

/-- Coefficientwise encoding of the common rational generating function relation
`Δ_δ(s) S_x(s) = N_x(s)`. -/
def criticalKernelGeneratingRelation {α : Type*} (d : ℕ) (a : Fin d → ℚ) (seq N : α → ℕ → ℚ) :
    Prop :=
  ∀ x k, criticalKernelProductCoeff d a seq x k = N x k

/-- The shared order-`d + 1` linear recurrence extracted from the common denominator. -/
def criticalKernelCommonRecurrence {α : Type*} (d : ℕ) (a : Fin d → ℚ) (seq : α → ℕ → ℚ)
    (x : α) (m : ℕ) : ℚ :=
  criticalKernelProductCoeff d a seq x (m + d)

/-- Paper label: `thm:conclusion-critical-kernel-separation-common-recurrence`. Once every start
state has a common denominator `Δ_δ` and the numerators have degree at most `d - 1`, the
coefficient of `s^(m + d)` in `Δ_δ(s) S_x(s)` vanishes, yielding the same recurrence for every
start state. -/
theorem paper_conclusion_critical_kernel_separation_common_recurrence {α : Type*} (d : ℕ)
    (a : Fin d → ℚ) (seq N : α → ℕ → ℚ)
    (hrel : criticalKernelGeneratingRelation d a seq N)
    (hdeg : criticalKernelNumeratorDegreeBound d N) :
    ∀ x m, criticalKernelCommonRecurrence d a seq x m = 0 := by
  intro x m
  unfold criticalKernelCommonRecurrence
  rw [hrel]
  exact hdeg x (m + d) (Nat.le_add_left d m)

end Omega.Conclusion
