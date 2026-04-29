import Omega.Zeta.AuditedEvenFirstCapacityKinkFibonacciJump

namespace Omega.Zeta

/-- Paper label: `cor:xi-audited-even-dyadic-first-capacity-linear-regime`. -/
theorem paper_xi_audited_even_dyadic_first_capacity_linear_regime (m : ℕ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht : t ≤ (auditedEvenFirstKink m : ℝ)) :
    auditedEvenContinuousCapacity m t = ((Nat.fib (m + 2) : ℕ) : ℝ) * t ∧
      auditedEvenContinuousCapacity m t / (2 : ℝ) ^ m =
        t * ((Nat.fib (m + 2) : ℕ) : ℝ) / (2 : ℝ) ^ m := by
  have hcap :=
    (paper_xi_audited_even_first_capacity_kink_fibonacci_jump m).1 ht0 ht
  refine ⟨hcap, ?_⟩
  rw [hcap]
  ring

end Omega.Zeta
