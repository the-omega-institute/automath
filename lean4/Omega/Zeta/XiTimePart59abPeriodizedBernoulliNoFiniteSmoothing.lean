import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part59ab-periodized-bernoulli-no-finite-smoothing`. -/
theorem paper_xi_time_part59ab_periodized_bernoulli_no_finite_smoothing
    (a : ℕ → ℕ → ℝ) (fib luc : ℕ → ℕ) (cFib cLuc : ℝ)
    (Limit : (ℕ → ℝ) → ℝ → Prop)
    (hbaseFib : Limit (fun n => a 1 (fib n)) cFib)
    (hbaseLuc : Limit (fun n => a 1 (luc n)) cLuc)
    (hmul : ∀ r u, a (r + 1) u = a r u * a 1 u)
    (hLimitMul : ∀ f g A B, Limit f A → Limit g B →
      Limit (fun n => f n * g n) (A * B)) :
    ∀ r, 1 ≤ r →
      Limit (fun n => a r (fib n)) (cFib ^ r) ∧
        Limit (fun n => a r (luc n)) (cLuc ^ r) := by
  refine Nat.le_induction ?base ?step
  · constructor
    · simpa using hbaseFib
    · simpa using hbaseLuc
  · intro r hr ih
    constructor
    · have hFib :=
        hLimitMul (fun n => a r (fib n)) (fun n => a 1 (fib n)) (cFib ^ r) cFib
          ih.1 hbaseFib
      have hFibFunction :
          (fun n => a (r + 1) (fib n)) = fun n => a r (fib n) * a 1 (fib n) := by
        funext n
        exact hmul r (fib n)
      have hFibPower : cFib ^ (r + 1) = cFib ^ r * cFib := by
        rw [pow_succ]
      rw [hFibFunction, hFibPower]
      exact hFib
    · have hLuc :=
        hLimitMul (fun n => a r (luc n)) (fun n => a 1 (luc n)) (cLuc ^ r) cLuc
          ih.2 hbaseLuc
      have hLucFunction :
          (fun n => a (r + 1) (luc n)) = fun n => a r (luc n) * a 1 (luc n) := by
        funext n
        exact hmul r (luc n)
      have hLucPower : cLuc ^ (r + 1) = cLuc ^ r * cLuc := by
        rw [pow_succ]
      rw [hLucFunction, hLucPower]
      exact hLuc

end Omega.Zeta
