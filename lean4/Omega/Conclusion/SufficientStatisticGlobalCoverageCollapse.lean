import Omega.Conclusion.FoldgaugePiSufficientStatisticFiberObstruction

namespace Omega.Conclusion

/-- Concrete global coverage collapse statement: any map through a visible fiber and an
`m + 1`-valued residual has image at most `(m + 1)|X|`, and the Fibonacci growth bound already
proved for the sufficient-statistic module tends to zero after normalization. -/
def conclusion_sufficient_statistic_global_coverage_collapse_statement : Prop :=
  (∀ (m : Nat) (X : Type*) [Fintype X] [DecidableEq X]
      (Ψ : Fin (2 ^ m) → X × Fin (m + 1)),
      (((Finset.univ.image Ψ).card : ℝ) / (2 : ℝ) ^ m) ≤
        (((m + 1 : Nat) : ℝ) * Fintype.card X) / (2 : ℝ) ^ m) ∧
    Filter.Tendsto
      (fun m : ℕ => (((m + 2 : ℕ) : ℝ) / Nat.fib (m + 2)))
      Filter.atTop (nhds 0)

/-- Paper label: `cor:conclusion-sufficient-statistic-global-coverage-collapse`. -/
theorem paper_conclusion_sufficient_statistic_global_coverage_collapse :
    conclusion_sufficient_statistic_global_coverage_collapse_statement := by
  classical
  refine ⟨?_, ?_⟩
  · intro m X _ _ Ψ
    have hcard :
        (Finset.univ.image Ψ).card ≤ Fintype.card (X × Fin (m + 1)) := by
      simpa using Finset.card_le_univ (Finset.univ.image Ψ)
    have hcard_real :
        ((Finset.univ.image Ψ).card : ℝ) ≤ (((m + 1 : Nat) : ℝ) * Fintype.card X) := by
      have hprod :
          Fintype.card (X × Fin (m + 1)) = Fintype.card X * (m + 1) := by
        simp
      have hnat : (Finset.univ.image Ψ).card ≤ Fintype.card X * (m + 1) := by
        simpa [hprod] using hcard
      have hreal : ((Finset.univ.image Ψ).card : ℝ) ≤
          ((Fintype.card X * (m + 1) : Nat) : ℝ) := by
        exact_mod_cast hnat
      simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hreal
    exact div_le_div_of_nonneg_right hcard_real (by positivity)
  · rcases paper_conclusion_sufficient_statistic_externalization_success_collapse with
      ⟨_, _, _, hlimit⟩
    exact hlimit

end Omega.Conclusion
