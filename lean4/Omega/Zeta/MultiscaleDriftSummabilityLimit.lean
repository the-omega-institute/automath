import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

namespace Omega.Zeta

open Filter

/-- Summable multiscale drift bounds force convergence of the shifted zero sequence, with the
total displacement controlled by the tail sum of the drift budget.
    thm:xi-multiscale-drift-summability-limit -/
theorem paper_xi_multiscale_drift_summability_limit
    (tau A : Nat -> Real) (k0 : Nat)
    (hA_nonneg : forall n, 0 <= A n) (hA : Summable A)
    (hstep : forall n, k0 <= n -> |tau (n + 1) - tau n| <= A n) :
    ∃ tauInf : Real,
      Tendsto (fun n => tau (n + k0)) atTop (nhds tauInf) ∧
        |tauInf - tau k0| <= tsum (fun n => A (n + k0)) := by
  let u : ℕ → ℝ := fun n => tau (n + k0)
  have hAshift : Summable (fun n => A (n + k0)) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (summable_nat_add_iff k0).2 hA
  have hdist_le : ∀ n, dist (u n) (u n.succ) <= A (n + k0) := by
    intro n
    have hk : k0 <= n + k0 := Nat.le_add_left _ _
    simpa [u, Real.dist_eq, abs_sub_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      hstep (n + k0) hk
  have hdist : Summable (fun n => dist (u n) (u n.succ)) := by
    refine Summable.of_nonneg_of_le (fun _ => dist_nonneg) hdist_le hAshift
  have hcauchy : CauchySeq u := cauchySeq_of_summable_dist hdist
  obtain ⟨tauInf, htauInf⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨tauInf, by simpa [u] using htauInf, ?_⟩
  have hdist0 :
      dist (u 0) tauInf <= tsum (fun n => A (n + k0)) := by
    exact dist_le_tsum_of_dist_le_of_tendsto₀ (fun n => A (n + k0)) hdist_le hAshift htauInf
  simpa [u, Real.dist_eq, abs_sub_comm] using hdist0

end Omega.Zeta
