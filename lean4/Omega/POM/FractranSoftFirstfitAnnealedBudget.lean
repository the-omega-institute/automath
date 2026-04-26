import Mathlib

namespace Omega.POM

noncomputable section

/-- Finite annealed failure budget over the first `T` soft first-fit steps. -/
def pom_fractran_soft_firstfit_annealed_budget_partial_budget (u : ℕ → ℝ) (T : ℕ) : ℝ :=
  (Finset.range T).sum u

/-- Total annealed failure budget obtained by summing the stepwise upper bounds. -/
def pom_fractran_soft_firstfit_annealed_budget_total_budget (u : ℕ → ℝ) : ℝ :=
  tsum u

/-- Paper label: `thm:pom-fractran-soft-firstfit-annealed-budget`.

If each soft first-fit failure probability is bounded by a nonnegative budget term `u_t`, then
the finite failure mass is bounded by the finite annealed budget, the full countable failure mass
is bounded by the total annealed budget, and any `ε`-upper bound on that total budget controls all
finite horizons. -/
theorem paper_pom_fractran_soft_firstfit_annealed_budget
    (failureProb u : ℕ → ℝ) (hfailure_nonneg : ∀ t, 0 ≤ failureProb t)
    (hstep : ∀ t, failureProb t ≤ u t) (hu_summable : Summable u) :
    Summable failureProb ∧
      (∀ T : ℕ,
        pom_fractran_soft_firstfit_annealed_budget_partial_budget failureProb T ≤
          pom_fractran_soft_firstfit_annealed_budget_partial_budget u T) ∧
      pom_fractran_soft_firstfit_annealed_budget_total_budget failureProb ≤
        pom_fractran_soft_firstfit_annealed_budget_total_budget u ∧
      ∀ ε : ℝ,
        pom_fractran_soft_firstfit_annealed_budget_total_budget u ≤ ε →
          ∀ T : ℕ,
            pom_fractran_soft_firstfit_annealed_budget_partial_budget failureProb T ≤ ε := by
  have hfailure_summable : Summable failureProb :=
    hu_summable.of_nonneg_of_le hfailure_nonneg hstep
  refine ⟨hfailure_summable, ?_, ?_, ?_⟩
  · intro T
    simpa [pom_fractran_soft_firstfit_annealed_budget_partial_budget] using
      (Finset.sum_le_sum fun t _ => hstep t :
        (Finset.range T).sum failureProb ≤ (Finset.range T).sum u)
  · simpa [pom_fractran_soft_firstfit_annealed_budget_total_budget] using
      (Summable.tsum_le_tsum hstep hfailure_summable hu_summable)
  · intro ε hε T
    have hfinite :
        pom_fractran_soft_firstfit_annealed_budget_partial_budget failureProb T ≤
          pom_fractran_soft_firstfit_annealed_budget_total_budget failureProb := by
      simpa [pom_fractran_soft_firstfit_annealed_budget_partial_budget,
        pom_fractran_soft_firstfit_annealed_budget_total_budget] using
        hfailure_summable.sum_le_tsum (Finset.range T) (fun t _ => hfailure_nonneg t)
    have hcountable :
        pom_fractran_soft_firstfit_annealed_budget_total_budget failureProb ≤
          pom_fractran_soft_firstfit_annealed_budget_total_budget u := by
      simpa [pom_fractran_soft_firstfit_annealed_budget_total_budget] using
        (Summable.tsum_le_tsum hstep hfailure_summable hu_summable)
    exact le_trans hfinite <|
      le_trans hcountable hε

end

end Omega.POM
