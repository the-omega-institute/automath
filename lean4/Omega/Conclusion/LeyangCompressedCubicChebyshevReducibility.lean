import Mathlib.Tactic

namespace Omega.Conclusion

open Polynomial

/-- The compressed cubic Chebyshev map used for the Lee--Yang reduction model. -/
def conclusion_leyang_compressed_cubic_chebyshev_reducibility_T3 (s : ℚ) : ℚ :=
  s ^ 3 - 3 * s

/-- The concrete compressed cubic fiber over the Chebyshev value `t`. -/
noncomputable def conclusion_leyang_compressed_cubic_chebyshev_reducibility_F
    (t : ℚ) : Polynomial ℚ :=
  X ^ 3 - C 3 * X - C t

/-- Reducibility of this cubic is represented by the existence of a rational linear factor. -/
def conclusion_leyang_compressed_cubic_chebyshev_reducibility_reducible (t : ℚ) : Prop :=
  ∃ y : ℚ, (conclusion_leyang_compressed_cubic_chebyshev_reducibility_F t).eval y = 0

/-- Explicit linear-factor formulation. -/
def conclusion_leyang_compressed_cubic_chebyshev_reducibility_linear_factor (t : ℚ) :
    Prop :=
  ∃ y : ℚ, (conclusion_leyang_compressed_cubic_chebyshev_reducibility_F t).eval y = 0

/-- Membership in the cubic Chebyshev image. -/
def conclusion_leyang_compressed_cubic_chebyshev_reducibility_chebyshev_image (t : ℚ) :
    Prop :=
  ∃ s : ℚ, conclusion_leyang_compressed_cubic_chebyshev_reducibility_T3 s = t

/-- A Chebyshev witness transferred back to a root of the compressed cubic. -/
def conclusion_leyang_compressed_cubic_chebyshev_reducibility_transferred_root (t : ℚ) :
    Prop :=
  ∃ s0 : ℚ,
    conclusion_leyang_compressed_cubic_chebyshev_reducibility_T3 s0 = t ∧
      (conclusion_leyang_compressed_cubic_chebyshev_reducibility_F t).eval s0 = 0

/-- The residual quadratic after the root `s0` is removed from `T3(s)-T3(s0)`. -/
def conclusion_leyang_compressed_cubic_chebyshev_reducibility_residual
    (s0 s : ℚ) : ℚ :=
  s ^ 2 + s0 * s + s0 ^ 2 - 3

/-- The residual quadratic has a rational root. -/
def conclusion_leyang_compressed_cubic_chebyshev_reducibility_residual_reducible
    (s0 : ℚ) : Prop :=
  ∃ s : ℚ, conclusion_leyang_compressed_cubic_chebyshev_reducibility_residual s0 s = 0

/-- The residual discriminant is a rational square. -/
def conclusion_leyang_compressed_cubic_chebyshev_reducibility_discriminant_square
    (s0 : ℚ) : Prop :=
  ∃ δ : ℚ, δ ^ 2 = 12 - 3 * s0 ^ 2

/-- Concrete statement package for the compressed cubic: the four root/reducibility conditions are
equivalent, and the remaining roots are governed by the residual quadratic discriminant. -/
def conclusion_leyang_compressed_cubic_chebyshev_reducibility_statement : Prop :=
  ∀ t : ℚ,
    (conclusion_leyang_compressed_cubic_chebyshev_reducibility_reducible t ↔
        conclusion_leyang_compressed_cubic_chebyshev_reducibility_linear_factor t) ∧
      (conclusion_leyang_compressed_cubic_chebyshev_reducibility_linear_factor t ↔
        conclusion_leyang_compressed_cubic_chebyshev_reducibility_chebyshev_image t) ∧
      (conclusion_leyang_compressed_cubic_chebyshev_reducibility_chebyshev_image t ↔
        conclusion_leyang_compressed_cubic_chebyshev_reducibility_transferred_root t) ∧
      (∀ s0 : ℚ,
        conclusion_leyang_compressed_cubic_chebyshev_reducibility_T3 s0 = t →
          (∀ s : ℚ,
            conclusion_leyang_compressed_cubic_chebyshev_reducibility_T3 s -
                conclusion_leyang_compressed_cubic_chebyshev_reducibility_T3 s0 =
              (s - s0) *
                conclusion_leyang_compressed_cubic_chebyshev_reducibility_residual s0 s) ∧
            (conclusion_leyang_compressed_cubic_chebyshev_reducibility_residual_reducible s0 ↔
              conclusion_leyang_compressed_cubic_chebyshev_reducibility_discriminant_square s0))

private lemma conclusion_leyang_compressed_cubic_chebyshev_reducibility_eval_root_iff
    (t y : ℚ) :
    (conclusion_leyang_compressed_cubic_chebyshev_reducibility_F t).eval y = 0 ↔
      conclusion_leyang_compressed_cubic_chebyshev_reducibility_T3 y = t := by
  unfold conclusion_leyang_compressed_cubic_chebyshev_reducibility_F
    conclusion_leyang_compressed_cubic_chebyshev_reducibility_T3
  constructor <;> intro h
  · have h' : y ^ 3 - 3 * y - t = 0 := by
      simpa using h
    linarith
  · have h' : y ^ 3 - 3 * y - t = 0 := by
      linarith
    simpa using h'

private lemma conclusion_leyang_compressed_cubic_chebyshev_reducibility_factor_identity
    (s0 s : ℚ) :
    conclusion_leyang_compressed_cubic_chebyshev_reducibility_T3 s -
        conclusion_leyang_compressed_cubic_chebyshev_reducibility_T3 s0 =
      (s - s0) *
        conclusion_leyang_compressed_cubic_chebyshev_reducibility_residual s0 s := by
  unfold conclusion_leyang_compressed_cubic_chebyshev_reducibility_T3
    conclusion_leyang_compressed_cubic_chebyshev_reducibility_residual
  ring

private lemma conclusion_leyang_compressed_cubic_chebyshev_reducibility_residual_square_iff
    (s0 : ℚ) :
    conclusion_leyang_compressed_cubic_chebyshev_reducibility_residual_reducible s0 ↔
      conclusion_leyang_compressed_cubic_chebyshev_reducibility_discriminant_square s0 := by
  unfold conclusion_leyang_compressed_cubic_chebyshev_reducibility_residual_reducible
    conclusion_leyang_compressed_cubic_chebyshev_reducibility_discriminant_square
    conclusion_leyang_compressed_cubic_chebyshev_reducibility_residual
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨2 * s + s0, ?_⟩
    nlinarith
  · rintro ⟨δ, hδ⟩
    refine ⟨(δ - s0) / 2, ?_⟩
    nlinarith

/-- Paper label: `thm:conclusion-leyang-compressed-cubic-chebyshev-reducibility`. -/
theorem paper_conclusion_leyang_compressed_cubic_chebyshev_reducibility :
    conclusion_leyang_compressed_cubic_chebyshev_reducibility_statement := by
  intro t
  refine ⟨Iff.rfl, ?_, ?_, ?_⟩
  · unfold conclusion_leyang_compressed_cubic_chebyshev_reducibility_linear_factor
      conclusion_leyang_compressed_cubic_chebyshev_reducibility_chebyshev_image
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, (conclusion_leyang_compressed_cubic_chebyshev_reducibility_eval_root_iff t y).mp hy⟩
    · rintro ⟨s, hs⟩
      exact ⟨s, (conclusion_leyang_compressed_cubic_chebyshev_reducibility_eval_root_iff t s).mpr hs⟩
  · unfold conclusion_leyang_compressed_cubic_chebyshev_reducibility_chebyshev_image
      conclusion_leyang_compressed_cubic_chebyshev_reducibility_transferred_root
    constructor
    · rintro ⟨s0, hs0⟩
      exact
        ⟨s0, hs0,
          (conclusion_leyang_compressed_cubic_chebyshev_reducibility_eval_root_iff t s0).mpr hs0⟩
    · rintro ⟨s0, hs0, _hroot⟩
      exact ⟨s0, hs0⟩
  · intro s0 _hs0
    exact
      ⟨conclusion_leyang_compressed_cubic_chebyshev_reducibility_factor_identity s0,
        conclusion_leyang_compressed_cubic_chebyshev_reducibility_residual_square_iff s0⟩

end Omega.Conclusion
