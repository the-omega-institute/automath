import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-diagonal-rate-finite-moment-closure`.  Starting from the quadratic
coefficient, the finite-moment closure step determines every higher Taylor coefficient. -/
theorem paper_pom_diagonal_rate_finite_moment_closure
    (coefficientDeterminedByMoments : ℕ → Prop) (h2 : coefficientDeterminedByMoments 2)
    (hstep : ∀ j, 2 ≤ j →
      (∀ k, 2 ≤ k → k ≤ j → coefficientDeterminedByMoments k) →
      coefficientDeterminedByMoments (j + 1)) :
    ∀ j, 2 ≤ j → coefficientDeterminedByMoments j := by
  intro j
  revert j
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hj
      by_cases hbase : j = 2
      · simpa [hbase] using h2
      · have hjpred : 2 ≤ j - 1 := by omega
        have hsucc : j - 1 + 1 = j := by omega
        rw [← hsucc]
        exact hstep (j - 1) hjpred (by
          intro k hk2 hkle
          exact ih k (by omega) hk2)

end Omega.POM
