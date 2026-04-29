import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite Fourier ledger for the `T₂` precision statement.  The finite character type
models one finite quotient of the profinite character basis; `fourierOrder` records the exact
order of a character and `fourierCoeff` records the coefficient of the function in that basis. -/
structure conclusion_leyang_t2_fourier_truncation_equals_precision_data where
  conclusion_leyang_t2_fourier_truncation_equals_precision_Character : Type
  conclusion_leyang_t2_fourier_truncation_equals_precision_fintype :
    Fintype conclusion_leyang_t2_fourier_truncation_equals_precision_Character
  conclusion_leyang_t2_fourier_truncation_equals_precision_decidableEq :
    DecidableEq conclusion_leyang_t2_fourier_truncation_equals_precision_Character
  conclusion_leyang_t2_fourier_truncation_equals_precision_fourierOrder :
    conclusion_leyang_t2_fourier_truncation_equals_precision_Character → ℕ
  conclusion_leyang_t2_fourier_truncation_equals_precision_fourierCoeff :
    conclusion_leyang_t2_fourier_truncation_equals_precision_Character → ℝ
  conclusion_leyang_t2_fourier_truncation_equals_precision_precision : ℕ

attribute [instance]
  conclusion_leyang_t2_fourier_truncation_equals_precision_data.conclusion_leyang_t2_fourier_truncation_equals_precision_fintype
  conclusion_leyang_t2_fourier_truncation_equals_precision_data.conclusion_leyang_t2_fourier_truncation_equals_precision_decidableEq

namespace conclusion_leyang_t2_fourier_truncation_equals_precision_data

/-- Characters visible at precision `2^n`. -/
def conclusion_leyang_t2_fourier_truncation_equals_precision_retainedCharacters
    (D : conclusion_leyang_t2_fourier_truncation_equals_precision_data) :
    Finset D.conclusion_leyang_t2_fourier_truncation_equals_precision_Character :=
  Finset.univ.filter
    (fun χ =>
      D.conclusion_leyang_t2_fourier_truncation_equals_precision_fourierOrder χ ≤
        2 ^ D.conclusion_leyang_t2_fourier_truncation_equals_precision_precision)

/-- The complementary Fourier tail beyond precision `2^n`. -/
def conclusion_leyang_t2_fourier_truncation_equals_precision_tailCharacters
    (D : conclusion_leyang_t2_fourier_truncation_equals_precision_data) :
    Finset D.conclusion_leyang_t2_fourier_truncation_equals_precision_Character :=
  Finset.univ.filter
    (fun χ =>
      2 ^ D.conclusion_leyang_t2_fourier_truncation_equals_precision_precision <
        D.conclusion_leyang_t2_fourier_truncation_equals_precision_fourierOrder χ)

/-- Finite-level conditional expectation in Fourier coordinates: keep exactly the characters whose
order divides the finite `2^n` quotient and delete the complementary tail. -/
def conclusion_leyang_t2_fourier_truncation_equals_precision_applyTruncation
    (D : conclusion_leyang_t2_fourier_truncation_equals_precision_data)
    (a : D.conclusion_leyang_t2_fourier_truncation_equals_precision_Character → ℝ) :
    D.conclusion_leyang_t2_fourier_truncation_equals_precision_Character → ℝ :=
  fun χ =>
    if D.conclusion_leyang_t2_fourier_truncation_equals_precision_fourierOrder χ ≤
        2 ^ D.conclusion_leyang_t2_fourier_truncation_equals_precision_precision then
      a χ
    else
      0

/-- The truncated Fourier coefficient vector of the given function. -/
def conclusion_leyang_t2_fourier_truncation_equals_precision_truncatedCoeff
    (D : conclusion_leyang_t2_fourier_truncation_equals_precision_data) :
    D.conclusion_leyang_t2_fourier_truncation_equals_precision_Character → ℝ :=
  D.conclusion_leyang_t2_fourier_truncation_equals_precision_applyTruncation
    D.conclusion_leyang_t2_fourier_truncation_equals_precision_fourierCoeff

/-- Squared `L²` error in the finite orthonormal Fourier model. -/
def conclusion_leyang_t2_fourier_truncation_equals_precision_squaredError
    (D : conclusion_leyang_t2_fourier_truncation_equals_precision_data) : ℝ :=
  ∑ χ,
    (D.conclusion_leyang_t2_fourier_truncation_equals_precision_fourierCoeff χ -
      D.conclusion_leyang_t2_fourier_truncation_equals_precision_truncatedCoeff χ) ^ 2

/-- The squared Fourier mass of the complementary tail. -/
def conclusion_leyang_t2_fourier_truncation_equals_precision_fourierTail
    (D : conclusion_leyang_t2_fourier_truncation_equals_precision_data) : ℝ :=
  ∑ χ ∈ D.conclusion_leyang_t2_fourier_truncation_equals_precision_tailCharacters,
    D.conclusion_leyang_t2_fourier_truncation_equals_precision_fourierCoeff χ ^ 2

/-- The finite conditional expectation is the idempotent orthogonal coordinate projection onto
characters of order at most `2^n`. -/
def conclusion_leyang_t2_fourier_truncation_equals_precision_projectionStatement
    (D : conclusion_leyang_t2_fourier_truncation_equals_precision_data) : Prop :=
  (∀ χ ∈ D.conclusion_leyang_t2_fourier_truncation_equals_precision_retainedCharacters,
      D.conclusion_leyang_t2_fourier_truncation_equals_precision_truncatedCoeff χ =
        D.conclusion_leyang_t2_fourier_truncation_equals_precision_fourierCoeff χ) ∧
    (∀ χ ∉ D.conclusion_leyang_t2_fourier_truncation_equals_precision_retainedCharacters,
      D.conclusion_leyang_t2_fourier_truncation_equals_precision_truncatedCoeff χ = 0) ∧
    (∀ a,
      D.conclusion_leyang_t2_fourier_truncation_equals_precision_applyTruncation
          (D.conclusion_leyang_t2_fourier_truncation_equals_precision_applyTruncation a) =
        D.conclusion_leyang_t2_fourier_truncation_equals_precision_applyTruncation a)

/-- Concrete Parseval tail identity for the finite quotient of the profinite `2`-adic filtration. -/
def conclusion_leyang_t2_fourier_truncation_equals_precision_statement
    (D : conclusion_leyang_t2_fourier_truncation_equals_precision_data) : Prop :=
  D.conclusion_leyang_t2_fourier_truncation_equals_precision_projectionStatement ∧
    D.conclusion_leyang_t2_fourier_truncation_equals_precision_squaredError =
      D.conclusion_leyang_t2_fourier_truncation_equals_precision_fourierTail

end conclusion_leyang_t2_fourier_truncation_equals_precision_data

open conclusion_leyang_t2_fourier_truncation_equals_precision_data

lemma conclusion_leyang_t2_fourier_truncation_equals_precision_projection
    (D : conclusion_leyang_t2_fourier_truncation_equals_precision_data) :
    D.conclusion_leyang_t2_fourier_truncation_equals_precision_projectionStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro χ hχ
    simp [conclusion_leyang_t2_fourier_truncation_equals_precision_retainedCharacters] at hχ
    simp [conclusion_leyang_t2_fourier_truncation_equals_precision_truncatedCoeff,
      conclusion_leyang_t2_fourier_truncation_equals_precision_applyTruncation, hχ]
  · intro χ hχ
    have hnot :
        ¬ D.conclusion_leyang_t2_fourier_truncation_equals_precision_fourierOrder χ ≤
          2 ^ D.conclusion_leyang_t2_fourier_truncation_equals_precision_precision := by
      intro hle
      exact hχ (by
        simp [conclusion_leyang_t2_fourier_truncation_equals_precision_retainedCharacters,
          hle])
    simp [conclusion_leyang_t2_fourier_truncation_equals_precision_truncatedCoeff,
      conclusion_leyang_t2_fourier_truncation_equals_precision_applyTruncation, hnot]
  · intro a
    funext χ
    by_cases hle :
        D.conclusion_leyang_t2_fourier_truncation_equals_precision_fourierOrder χ ≤
          2 ^ D.conclusion_leyang_t2_fourier_truncation_equals_precision_precision
    · simp [conclusion_leyang_t2_fourier_truncation_equals_precision_applyTruncation, hle]
    · simp [conclusion_leyang_t2_fourier_truncation_equals_precision_applyTruncation, hle]

lemma conclusion_leyang_t2_fourier_truncation_equals_precision_parseval_tail
    (D : conclusion_leyang_t2_fourier_truncation_equals_precision_data) :
    D.conclusion_leyang_t2_fourier_truncation_equals_precision_squaredError =
      D.conclusion_leyang_t2_fourier_truncation_equals_precision_fourierTail := by
  classical
  rw [conclusion_leyang_t2_fourier_truncation_equals_precision_squaredError,
    conclusion_leyang_t2_fourier_truncation_equals_precision_fourierTail,
    conclusion_leyang_t2_fourier_truncation_equals_precision_tailCharacters]
  calc
    (∑ χ,
      (D.conclusion_leyang_t2_fourier_truncation_equals_precision_fourierCoeff χ -
        D.conclusion_leyang_t2_fourier_truncation_equals_precision_truncatedCoeff χ) ^ 2) =
        ∑ χ,
          if 2 ^ D.conclusion_leyang_t2_fourier_truncation_equals_precision_precision <
              D.conclusion_leyang_t2_fourier_truncation_equals_precision_fourierOrder χ then
            D.conclusion_leyang_t2_fourier_truncation_equals_precision_fourierCoeff χ ^ 2
          else
            0 := by
          refine Finset.sum_congr rfl ?_
          intro χ _hχ
          by_cases hle :
              D.conclusion_leyang_t2_fourier_truncation_equals_precision_fourierOrder χ ≤
                2 ^ D.conclusion_leyang_t2_fourier_truncation_equals_precision_precision
          · have hnotlt :
                ¬ 2 ^ D.conclusion_leyang_t2_fourier_truncation_equals_precision_precision <
                  D.conclusion_leyang_t2_fourier_truncation_equals_precision_fourierOrder χ :=
              not_lt.mpr hle
            simp [conclusion_leyang_t2_fourier_truncation_equals_precision_truncatedCoeff,
              conclusion_leyang_t2_fourier_truncation_equals_precision_applyTruncation, hle,
              hnotlt]
          · have hlt :
                2 ^ D.conclusion_leyang_t2_fourier_truncation_equals_precision_precision <
                  D.conclusion_leyang_t2_fourier_truncation_equals_precision_fourierOrder χ :=
              Nat.lt_of_not_ge hle
            simp [conclusion_leyang_t2_fourier_truncation_equals_precision_truncatedCoeff,
              conclusion_leyang_t2_fourier_truncation_equals_precision_applyTruncation, hle,
              hlt]
    _ =
        ∑ χ ∈ (Finset.univ.filter
          (fun χ =>
            2 ^ D.conclusion_leyang_t2_fourier_truncation_equals_precision_precision <
              D.conclusion_leyang_t2_fourier_truncation_equals_precision_fourierOrder χ)),
          D.conclusion_leyang_t2_fourier_truncation_equals_precision_fourierCoeff χ ^ 2 := by
          rw [Finset.sum_filter]

/-- Paper label:
`thm:conclusion-leyang-t2-fourier-truncation-equals-precision`. -/
theorem paper_conclusion_leyang_t2_fourier_truncation_equals_precision
    (D : conclusion_leyang_t2_fourier_truncation_equals_precision_data) :
    conclusion_leyang_t2_fourier_truncation_equals_precision_statement D := by
  exact ⟨conclusion_leyang_t2_fourier_truncation_equals_precision_projection D,
    conclusion_leyang_t2_fourier_truncation_equals_precision_parseval_tail D⟩

end Omega.Conclusion
