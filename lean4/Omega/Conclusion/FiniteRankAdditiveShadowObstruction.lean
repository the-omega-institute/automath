import Omega.Folding.KilloPrimeFreedomNonFinitizability

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-finite-rank-additive-shadow-obstruction`.
Passing a faithful additive shadow model to Grothendieck completion would produce a finite-rank
linear host for the prime-exponent directions, but the existing finite-rank obstruction rules out
every such linearization. -/
def conclusion_finite_rank_additive_shadow_obstruction_statement : Prop :=
  Omega.Folding.killoPrimeExponentEmbeddingFaithful ∧
    ∀ k : ℕ, Omega.Folding.killoFiniteRegisterLinearizationObstructed k

theorem paper_conclusion_finite_rank_additive_shadow_obstruction :
    conclusion_finite_rank_additive_shadow_obstruction_statement := by
  exact Omega.Folding.paper_killo_prime_freedom_non_finitizability

end Omega.Conclusion
