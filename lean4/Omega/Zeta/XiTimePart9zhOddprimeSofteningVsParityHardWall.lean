import Omega.Zeta.XiTimePart9xgParityWallVersusCofinalPrimeTwists

namespace Omega.Zeta

/-- Concrete part9zh statement: the parity wall is bounded away from the Perron branch, while
cofinally many odd-prime twists sit strictly above that fixed parity ratio. -/
def xi_time_part9zh_oddprime_softening_vs_parity_hard_wall_statement
    (rhoRatio : ℕ → ℝ) (rhoMinusOverLambda : ℝ) : Prop :=
  rhoMinusOverLambda < 1 ∧
    ∀ B : ℕ,
      ∃ p : ℕ, B ≤ p ∧ Nat.Prime p ∧ Odd p ∧ rhoMinusOverLambda < rhoRatio p

/-- Paper label: `thm:xi-time-part9zh-oddprime-softening-vs-parity-hard-wall`.

The part9zh theorem is the named repackaging of the established parity-wall versus cofinal
odd-prime-twist theorem. -/
theorem paper_xi_time_part9zh_oddprime_softening_vs_parity_hard_wall
    (rhoRatio : ℕ → ℝ) (rhoMinusOverLambda : ℝ) (hwall : rhoMinusOverLambda < 1)
    (hcofinal :
      ∀ B : ℕ,
        ∃ p : ℕ, B ≤ p ∧ Nat.Prime p ∧ Odd p ∧ rhoMinusOverLambda < rhoRatio p) :
    xi_time_part9zh_oddprime_softening_vs_parity_hard_wall_statement
      rhoRatio rhoMinusOverLambda := by
  exact
    paper_xi_time_part9xg_parity_wall_versus_cofinal_prime_twists
      rhoRatio rhoMinusOverLambda hwall hcofinal

end Omega.Zeta
