import Omega.Conclusion.PrimeRegisterRanktwoHostNonobstruction

namespace Omega.Conclusion

/-- Concrete conclusion-level fracture statement: the same fixed rank-two ambient supports a
faithful finite host, while multiplicative prime-register semantics cannot be faithfully collapsed
to a single additive ledger or to the stable finite-rank ledger package. -/
def conclusion_prime_register_ambient_vs_semantic_ledger_fracture_statement : Prop :=
  Fintype.card (Fin 2) = 2 ∧
    Function.Injective primeRegisterAffineAction ∧
    Function.Injective conclusion_prime_register_ranktwo_host_nonobstruction_eventEncoding ∧
    conclusion_stable_multiplication_finite_rank_ledger_impossibility_statement ∧
    ∀ f : ℕ → ℕ,
      f 1 = 0 → (∀ m n, f (m * n) = f m + f n) → ¬ Function.Injective f

/-- Paper label: `cor:conclusion-prime-register-ambient-vs-semantic-ledger-fracture`. -/
theorem paper_conclusion_prime_register_ambient_vs_semantic_ledger_fracture :
    conclusion_prime_register_ambient_vs_semantic_ledger_fracture_statement := by
  rcases paper_conclusion_prime_register_ranktwo_host_nonobstruction with
    ⟨hcard, hambient, hencoding, hstable⟩
  rcases paper_conclusion_prime_register_fixed_2adic_ambient_vs_finite_ledger with
    ⟨_, _, hsingle⟩
  exact ⟨hcard, hambient, hencoding, hstable, hsingle⟩

end Omega.Conclusion
