import Omega.Discussion.ChebyshevAdams

namespace Omega.Discussion

/-- Primitive extraction on the generator `S` of the polynomial ring `ℤ[S]`. In this seed model it
returns the generator itself, matching the primitive Witt coordinate. -/
def lambdaPrimitiveExtraction (S : ℤ) : ℤ :=
  chebyAdams 1 S

/-- Adams action on `ℤ[S]`, encoded by the Chebyshev-Adams polynomial `C_n(S)`. -/
def lambdaAdamsAction (n : ℕ) (S : ℤ) : ℤ :=
  chebyAdams n S

@[simp] theorem lambdaPrimitiveExtraction_eq_generator (S : ℤ) :
    lambdaPrimitiveExtraction S = S := by
  simp [lambdaPrimitiveExtraction]

/-- Adams operations compose by multiplication of indices. -/
theorem lambdaAdamsAction_mul (m n : ℕ) (S : ℤ) :
    lambdaAdamsAction (m * n) S = lambdaAdamsAction m (lambdaAdamsAction n S) := by
  simpa [lambdaAdamsAction] using chebyAdams_mul m n S

/-- Primitive extraction commutes with the Adams action on the generator line. -/
theorem lambdaPrimitiveExtraction_equivariant (n : ℕ) (S : ℤ) :
    lambdaPrimitiveExtraction (lambdaAdamsAction n S) =
      lambdaAdamsAction n (lambdaPrimitiveExtraction S) := by
  simp [lambdaPrimitiveExtraction, lambdaAdamsAction]

/-- Paper-facing wrapper repackaging the Chebyshev/Witt reciprocity statements as
Adams-equivariance of primitive extraction on `ℤ[S]`.
    cor:discussion-lambda-equivariant-primitive -/
theorem paper_discussion_lambda_equivariant_primitive :
    (∀ m n : ℕ, ∀ S : ℤ,
      lambdaAdamsAction (m * n) S = lambdaAdamsAction m (lambdaAdamsAction n S)) ∧
    (∀ n : ℕ, ∀ S : ℤ,
      lambdaPrimitiveExtraction (lambdaAdamsAction n S) =
        lambdaAdamsAction n (lambdaPrimitiveExtraction S)) ∧
    (lambdaPrimitiveExtraction 3 = 3 ∧
      lambdaAdamsAction 2 3 = 7 ∧
      lambdaAdamsAction 3 3 = 18) := by
  refine ⟨lambdaAdamsAction_mul, lambdaPrimitiveExtraction_equivariant, ?_⟩
  norm_num [lambdaPrimitiveExtraction, lambdaAdamsAction, chebyAdams]

end Omega.Discussion
