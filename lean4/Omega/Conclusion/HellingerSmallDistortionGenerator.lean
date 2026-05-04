import Omega.Conclusion.HellingerGeneratorReversibilityDirichlet

namespace Omega.Conclusion

/-- Concrete certificate for the small-distortion Hellinger generator.  The off-diagonal and
diagonal entries are named explicitly, and the off-diagonal certificate is in the normalized form
used by the reversibility corollary. -/
structure conclusion_hellinger_small_distortion_generator_data where
  conclusion_hellinger_small_distortion_generator_State : Type*
  conclusion_hellinger_small_distortion_generator_fintype :
    Fintype conclusion_hellinger_small_distortion_generator_State
  conclusion_hellinger_small_distortion_generator_decidableEq :
    DecidableEq conclusion_hellinger_small_distortion_generator_State
  conclusion_hellinger_small_distortion_generator_weight :
    conclusion_hellinger_small_distortion_generator_State → ℝ
  conclusion_hellinger_small_distortion_generator_sqrtWeight :
    conclusion_hellinger_small_distortion_generator_State → ℝ
  conclusion_hellinger_small_distortion_generator_generator :
    conclusion_hellinger_small_distortion_generator_State →
      conclusion_hellinger_small_distortion_generator_State → ℝ
  conclusion_hellinger_small_distortion_generator_A : ℝ
  conclusion_hellinger_small_distortion_generator_offDiagonal :
    conclusion_hellinger_small_distortion_generator_State →
      conclusion_hellinger_small_distortion_generator_State → ℝ
  conclusion_hellinger_small_distortion_generator_diagonal :
    conclusion_hellinger_small_distortion_generator_State → ℝ
  conclusion_hellinger_small_distortion_generator_offDiagonal_formula :
    ∀ x y, x ≠ y →
      conclusion_hellinger_small_distortion_generator_offDiagonal x y =
        conclusion_hellinger_small_distortion_generator_sqrtWeight x *
          conclusion_hellinger_small_distortion_generator_sqrtWeight y /
            (conclusion_hellinger_small_distortion_generator_A ^ 2 - 1)
  conclusion_hellinger_small_distortion_generator_generator_offDiagonal :
    ∀ x y, x ≠ y →
      conclusion_hellinger_small_distortion_generator_weight x *
          conclusion_hellinger_small_distortion_generator_generator x y =
        conclusion_hellinger_small_distortion_generator_offDiagonal x y
  conclusion_hellinger_small_distortion_generator_generator_diagonal :
    ∀ x,
      conclusion_hellinger_small_distortion_generator_generator x x =
        conclusion_hellinger_small_distortion_generator_diagonal x

/-- Paper-facing statement for the explicit generator package: the certified off-diagonal and
diagonal entries are exposed, and the off-diagonal part is reversible with respect to `w`. -/
def conclusion_hellinger_small_distortion_generator_statement
    (D : conclusion_hellinger_small_distortion_generator_data) : Prop :=
  (∀ x y, x ≠ y →
    D.conclusion_hellinger_small_distortion_generator_weight x *
        D.conclusion_hellinger_small_distortion_generator_generator x y =
      D.conclusion_hellinger_small_distortion_generator_offDiagonal x y) ∧
    (∀ x,
      D.conclusion_hellinger_small_distortion_generator_generator x x =
        D.conclusion_hellinger_small_distortion_generator_diagonal x) ∧
      ∀ x y, x ≠ y →
        D.conclusion_hellinger_small_distortion_generator_weight x *
            D.conclusion_hellinger_small_distortion_generator_generator x y =
          D.conclusion_hellinger_small_distortion_generator_weight y *
            D.conclusion_hellinger_small_distortion_generator_generator y x

/-- Paper label: `thm:conclusion-hellinger-small-distortion-generator`. -/
theorem paper_conclusion_hellinger_small_distortion_generator
    (D : conclusion_hellinger_small_distortion_generator_data) :
    conclusion_hellinger_small_distortion_generator_statement D := by
  letI := D.conclusion_hellinger_small_distortion_generator_fintype
  letI := D.conclusion_hellinger_small_distortion_generator_decidableEq
  refine ⟨D.conclusion_hellinger_small_distortion_generator_generator_offDiagonal,
    D.conclusion_hellinger_small_distortion_generator_generator_diagonal, ?_⟩
  have hoff :
      ∀ x y, x ≠ y →
        D.conclusion_hellinger_small_distortion_generator_weight x *
            D.conclusion_hellinger_small_distortion_generator_generator x y =
          D.conclusion_hellinger_small_distortion_generator_sqrtWeight x *
            D.conclusion_hellinger_small_distortion_generator_sqrtWeight y /
              (D.conclusion_hellinger_small_distortion_generator_A ^ 2 - 1) := by
    intro x y hxy
    rw [D.conclusion_hellinger_small_distortion_generator_generator_offDiagonal x y hxy,
      D.conclusion_hellinger_small_distortion_generator_offDiagonal_formula x y hxy]
  exact paper_conclusion_hellinger_generator_reversibility_dirichlet
    D.conclusion_hellinger_small_distortion_generator_weight
    D.conclusion_hellinger_small_distortion_generator_sqrtWeight
    D.conclusion_hellinger_small_distortion_generator_generator
    D.conclusion_hellinger_small_distortion_generator_A hoff

end Omega.Conclusion
