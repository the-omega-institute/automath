import Omega.Discussion.LambdaEquivariantPrimitive

namespace Omega.Discussion

/-- Paper label: `thm:discussion-chebyshev-witt-equivariance`. The Chebyshev-Adams action composes
by index multiplication, commutes with primitive extraction, and the completed ghost line at
`S = 3` agrees with the Lucas shadow from `DynZeta`. -/
def discussion_chebyshev_witt_equivariance_statement : Prop :=
  (∀ m n : ℕ, ∀ S : ℤ,
    lambdaAdamsAction (m * n) S = lambdaAdamsAction m (lambdaAdamsAction n S)) ∧
  (∀ n : ℕ, ∀ S : ℤ,
    lambdaPrimitiveExtraction (lambdaAdamsAction n S) =
      lambdaAdamsAction n (lambdaPrimitiveExtraction S)) ∧
  (∀ n : ℕ, lambdaAdamsAction n 3 = Omega.Zeta.lucasNum (2 * n))

theorem paper_discussion_chebyshev_witt_equivariance :
    discussion_chebyshev_witt_equivariance_statement := by
  refine ⟨lambdaAdamsAction_mul, lambdaPrimitiveExtraction_equivariant, ?_⟩
  intro n
  simpa [lambdaAdamsAction] using chebyAdams_at_three_eq_lucas_even n

end Omega.Discussion
