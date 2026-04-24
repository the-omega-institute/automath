import Omega.Conclusion.StableSuccessorFaithfulSemigroup
import Omega.Conclusion.WallisFiniteAdditiveLedgerImpossible

namespace Omega.Conclusion

/-- The positive-valuation sector `X_infty^times` in the concrete stable-successor model. -/
abbrev conclusion_stable_multiplication_finite_rank_ledger_impossibility_x_infty_times :=
  { n : ℕ // 0 < n }

/-- Paper-facing package for the stable-multiplication ledger obstruction: the positive-valuation
sector is nonempty, the stable-successor model yields a faithful multiplicative semigroup action,
and the existing finite additive linearization obstruction rules out any finite-rank ledger
linearization. -/
def conclusion_stable_multiplication_finite_rank_ledger_impossibility_statement : Prop :=
  Nonempty conclusion_stable_multiplication_finite_rank_ledger_impossibility_x_infty_times ∧
    (let M : ℕ → ℕ → ℕ := fun n c => n * c
     ∀ m n, M m = M n → m = n) ∧
    ¬ conclusion_wallis_finite_additive_ledger_impossible_hasFiniteAdditiveLinearization

/-- Paper label: `thm:conclusion-stable-multiplication-finite-rank-ledger-impossibility`. -/
theorem paper_conclusion_stable_multiplication_finite_rank_ledger_impossibility :
    conclusion_stable_multiplication_finite_rank_ledger_impossibility_statement := by
  have hfaithful :
      let M : ℕ → ℕ → ℕ := fun n c => n * c
      ∀ m n, M m = M n → m = n :=
    (paper_conclusion_stable_successor_faithful_semigroup
      (X := ℕ) 0 Nat.succ (fun n => n) (fun n => n) (fun n => rfl)
      (fun n => by
        induction n with
        | zero =>
            rfl
        | succ n ih =>
            simpa [Function.iterate_succ_apply', ih])).2.2
  have hno_linear :
      ¬ conclusion_wallis_finite_additive_ledger_impossible_hasFiniteAdditiveLinearization :=
    paper_conclusion_wallis_finite_additive_ledger_impossible.2
  exact ⟨⟨⟨1, by decide⟩⟩, hfaithful, hno_linear⟩

end Omega.Conclusion
