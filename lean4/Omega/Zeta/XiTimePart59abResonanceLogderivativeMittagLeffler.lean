import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete recurrence-and-convergence package for the resonance log-derivative skeleton.  The
sequence `L` is the log-derivative sampled along the self-similar orbit, `driver` is the tangent
forcing term, and `rho` is the one-step scaling factor. -/
structure xi_time_part59ab_resonance_logderivative_mittagleffler_data where
  L : ℕ → ℝ
  driver : ℕ → ℝ
  rho : ℝ
  tangentPartial : ℕ → ℝ
  mittagLefflerPartial : ℕ → ℝ
  tangentLimit : ℝ
  principalValueLimit : ℝ
  one_step_riccati : ∀ n : ℕ, L n = driver n + rho * L (n + 1)
  tangent_converges :
    Filter.Tendsto tangentPartial Filter.atTop (nhds tangentLimit)
  mittag_leffler_principal_value_converges :
    Filter.Tendsto mittagLefflerPartial Filter.atTop (nhds principalValueLimit)
  principal_value_matches_tangent_limit : principalValueLimit = tangentLimit

/-- The finite Riccati iterate through `N` self-similar steps. -/
noncomputable def xi_time_part59ab_resonance_logderivative_mittagleffler_riccatiPartial
    (D : xi_time_part59ab_resonance_logderivative_mittagleffler_data) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, D.rho ^ n * D.driver n

/-- The paper-facing conclusion: the finite iteration follows from the one-step Riccati recursion,
and the tangent and principal-value Mittag-Leffler convergence clauses are retained explicitly. -/
def xi_time_part59ab_resonance_logderivative_mittagleffler_holds
    (D : xi_time_part59ab_resonance_logderivative_mittagleffler_data) : Prop :=
  (∀ N : ℕ,
      D.L 0 =
        xi_time_part59ab_resonance_logderivative_mittagleffler_riccatiPartial D N +
          D.rho ^ N * D.L N) ∧
    Filter.Tendsto D.tangentPartial Filter.atTop (nhds D.tangentLimit) ∧
    Filter.Tendsto D.mittagLefflerPartial Filter.atTop (nhds D.principalValueLimit) ∧
    D.principalValueLimit = D.tangentLimit

/-- Paper label: `thm:xi-time-part59ab-resonance-logderivative-mittagleffler`. -/
theorem paper_xi_time_part59ab_resonance_logderivative_mittagleffler
    (D : xi_time_part59ab_resonance_logderivative_mittagleffler_data) :
    xi_time_part59ab_resonance_logderivative_mittagleffler_holds D := by
  have hIter :
      ∀ N : ℕ,
        D.L 0 =
          xi_time_part59ab_resonance_logderivative_mittagleffler_riccatiPartial D N +
            D.rho ^ N * D.L N := by
    intro N
    induction N with
    | zero =>
        simp [xi_time_part59ab_resonance_logderivative_mittagleffler_riccatiPartial]
    | succ N ih =>
        calc
          D.L 0 =
              xi_time_part59ab_resonance_logderivative_mittagleffler_riccatiPartial D N +
                D.rho ^ N * D.L N := ih
          _ =
              xi_time_part59ab_resonance_logderivative_mittagleffler_riccatiPartial D N +
                D.rho ^ N * (D.driver N + D.rho * D.L (N + 1)) := by
                rw [D.one_step_riccati N]
          _ =
              xi_time_part59ab_resonance_logderivative_mittagleffler_riccatiPartial D (N + 1) +
                D.rho ^ (N + 1) * D.L (N + 1) := by
                simp [xi_time_part59ab_resonance_logderivative_mittagleffler_riccatiPartial,
                  Finset.sum_range_succ, pow_succ]
                ring
  exact ⟨hIter, D.tangent_converges, D.mittag_leffler_principal_value_converges,
    D.principal_value_matches_tangent_limit⟩

end Omega.Zeta
