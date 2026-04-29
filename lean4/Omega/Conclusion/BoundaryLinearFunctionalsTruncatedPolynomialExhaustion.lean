import Mathlib
import Omega.Conclusion.BoundaryStokesStrictLinearHolography

namespace Omega.Conclusion

open scoped BigOperators

/-- The truncated polynomial attached to the boundary holography package is just its coefficient
vector in the moment-box coordinates. -/
abbrev BoundaryTruncatedPolynomial (m n : ℕ) := BoundaryMomentBoxSpace m n

/-- The monomial basis vector indexed by a dyadic moment coordinate. -/
noncomputable def boundaryTruncatedPolynomialBasis (m n : ℕ) (α : BoundaryMomentIndex m n) :
    BoundaryTruncatedPolynomial m n :=
  Pi.basisFun ℚ (BoundaryMomentIndex m n) α

/-- Recover the coefficient vector of a boundary linear functional by transporting it through the
strict linear holography equivalence and evaluating on the standard basis. -/
noncomputable def boundaryTruncatedPolynomialOfFunctional (m n : ℕ)
    (Λ : BoundaryImageSpace m n →ₗ[ℚ] ℚ) : BoundaryTruncatedPolynomial m n :=
  fun α =>
    Λ ((boundaryStokesStrictLinearHolography m n).symm (boundaryTruncatedPolynomialBasis m n α))

/-- The boundary linear functional encoded by a truncated polynomial. -/
noncomputable def boundaryLinearFunctionalOfTruncatedPolynomial (m n : ℕ)
    (p : BoundaryTruncatedPolynomial m n) : BoundaryImageSpace m n →ₗ[ℚ] ℚ :=
  ((Pi.basisFun ℚ (BoundaryMomentIndex m n)).constr ℚ p).comp
    (boundaryStokesStrictLinearHolography m n).toLinearMap

lemma boundaryLinearFunctionalOfTruncatedPolynomial_basis_apply
    (m n : ℕ) (p : BoundaryTruncatedPolynomial m n) (α : BoundaryMomentIndex m n) :
    boundaryLinearFunctionalOfTruncatedPolynomial m n p
      ((boundaryStokesStrictLinearHolography m n).symm (boundaryTruncatedPolynomialBasis m n α)) =
        p α := by
  let B := Pi.basisFun ℚ (BoundaryMomentIndex m n)
  simpa [boundaryLinearFunctionalOfTruncatedPolynomial, boundaryTruncatedPolynomialBasis, B] using
    B.constr_basis ℚ p α

/-- Paper label: `cor:conclusion-boundary-linear-functionals-truncated-polynomial-exhaustion`.
Every boundary linear functional is represented by a unique truncated polynomial in the strict
linear holography coordinates. -/
theorem paper_conclusion_boundary_linear_functionals_truncated_polynomial_exhaustion
    (m n : ℕ) (Λ : BoundaryImageSpace m n →ₗ[ℚ] ℚ) :
    ∃! p : BoundaryTruncatedPolynomial m n,
      boundaryLinearFunctionalOfTruncatedPolynomial m n p = Λ := by
  let B := Pi.basisFun ℚ (BoundaryMomentIndex m n)
  let h := boundaryStokesStrictLinearHolography m n
  let L : BoundaryTruncatedPolynomial m n →ₗ[ℚ] ℚ :=
    Λ.comp (h.symm : BoundaryTruncatedPolynomial m n →ₗ[ℚ] BoundaryImageSpace m n)
  refine ⟨boundaryTruncatedPolynomialOfFunctional m n Λ, ?_, ?_⟩
  · apply LinearMap.ext
    intro b
    change (B.constr ℚ fun α => L (B α)) (h b) = Λ b
    rw [B.constr_self]
    simp [L, h]
  · intro p hp
    ext α
    have hα := congrArg
      (fun F =>
        F ((boundaryStokesStrictLinearHolography m n).symm
          (boundaryTruncatedPolynomialBasis m n α))) hp
    calc
      p α
          = boundaryLinearFunctionalOfTruncatedPolynomial m n p
              ((boundaryStokesStrictLinearHolography m n).symm
                (boundaryTruncatedPolynomialBasis m n α)) := by
                  symm
                  exact boundaryLinearFunctionalOfTruncatedPolynomial_basis_apply m n p α
      _ = Λ ((boundaryStokesStrictLinearHolography m n).symm
            (boundaryTruncatedPolynomialBasis m n α)) := hα
      _ = boundaryTruncatedPolynomialOfFunctional m n Λ α := by
            rfl

end Omega.Conclusion
