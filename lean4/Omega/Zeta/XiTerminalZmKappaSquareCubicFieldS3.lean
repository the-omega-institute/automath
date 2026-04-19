import Mathlib.Tactic

namespace Omega.Zeta

/-- The cubic satisfied by the double root `λ₀` on the Lee-Yang branch. -/
def xiTerminalLambdaCubic (lam : ℚ) : ℚ :=
  16 * lam ^ 3 - 9 * lam ^ 2 + 1

/-- The rational expression recovering `λ₀` from `u = κ_*²`. -/
def xiTerminalLambdaFromU (u : ℚ) : ℚ :=
  3 * (2 * u - 1) / (4 * (3 * u - 2))

/-- The cubic polynomial satisfied by `u = κ_*²`. -/
def xiTerminalKappaSquareCubic (u : ℚ) : ℚ :=
  324 * u ^ 3 - 540 * u ^ 2 + 333 * u - 74

/-- The cubic discriminant formula in coefficient form. -/
def cubicDiscriminant (a b c d : ℤ) : ℤ :=
  b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d - 27 * a ^ 2 * d ^ 2 + 18 * a * b * c * d

/-- The discriminant of `324 u^3 - 540 u^2 + 333 u - 74`. -/
def xiTerminalKappaSquareDiscriminant : ℤ :=
  cubicDiscriminant 324 (-540) 333 (-74)

/-- The ten rational-root candidates for `16 λ^3 - 9 λ^2 + 1`, coming from the rational-root
audit `num ∣ 1`, `den ∣ 16`. -/
def xiTerminalLambdaRationalRootCandidateAudit : Prop :=
  xiTerminalLambdaCubic (1 : ℚ) ≠ 0 ∧
  xiTerminalLambdaCubic (1 / 2 : ℚ) ≠ 0 ∧
  xiTerminalLambdaCubic (1 / 4 : ℚ) ≠ 0 ∧
  xiTerminalLambdaCubic (1 / 8 : ℚ) ≠ 0 ∧
  xiTerminalLambdaCubic (1 / 16 : ℚ) ≠ 0 ∧
  xiTerminalLambdaCubic (-1 : ℚ) ≠ 0 ∧
  xiTerminalLambdaCubic (-1 / 2 : ℚ) ≠ 0 ∧
  xiTerminalLambdaCubic (-1 / 4 : ℚ) ≠ 0 ∧
  xiTerminalLambdaCubic (-1 / 8 : ℚ) ≠ 0 ∧
  xiTerminalLambdaCubic (-1 / 16 : ℚ) ≠ 0

/-- Concrete `S₃` audit: the rational-root candidates all miss, the discriminant has the displayed
value, and that value is not a square. -/
def xiTerminalKappaSquareS3Audit : Prop :=
  xiTerminalLambdaRationalRootCandidateAudit ∧
    xiTerminalKappaSquareDiscriminant = -((2 : ℤ) ^ 6 * 3 ^ 9 * 37) ∧
    ¬ IsSquare xiTerminalKappaSquareDiscriminant

private theorem xiTerminalLambdaRationalRootCandidateAudit_true :
    xiTerminalLambdaRationalRootCandidateAudit := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [xiTerminalLambdaCubic]

private theorem xiTerminalKappaSquareDiscriminant_eval :
    xiTerminalKappaSquareDiscriminant = -((2 : ℤ) ^ 6 * 3 ^ 9 * 37) := by
  norm_num [xiTerminalKappaSquareDiscriminant, cubicDiscriminant]

private theorem xiTerminalKappaSquareDiscriminant_not_square :
    ¬ IsSquare xiTerminalKappaSquareDiscriminant := by
  intro hsquare
  rcases hsquare with ⟨n, hn⟩
  have hnonneg : 0 ≤ xiTerminalKappaSquareDiscriminant := by
    simpa [pow_two, hn] using sq_nonneg n
  rw [xiTerminalKappaSquareDiscriminant_eval] at hnonneg
  norm_num at hnonneg

/-- Concrete audit package for the Lee-Yang `u = κ_*²` cubic:
the displayed formula for `λ₀(u)`, the fact that `u = 2/3` is not a root of the `u`-cubic, the
full rational-root candidate exclusion table for `16 λ^3 - 9 λ^2 + 1`, and the nonsquare
discriminant value `-2^6 · 3^9 · 37`.
    thm:xi-terminal-zm-kappa-square-cubic-field-s3 -/
theorem paper_xi_terminal_zm_kappa_square_cubic_field_s3 :
    (∀ u : ℚ, xiTerminalLambdaFromU u = 3 * (2 * u - 1) / (4 * (3 * u - 2))) ∧
    xiTerminalKappaSquareCubic ((2 : ℚ) / 3) = 4 ∧
    xiTerminalLambdaRationalRootCandidateAudit ∧
    xiTerminalKappaSquareDiscriminant = -((2 : ℤ) ^ 6 * 3 ^ 9 * 37) ∧
    xiTerminalKappaSquareS3Audit := by
  refine ⟨?_, ?_, xiTerminalLambdaRationalRootCandidateAudit_true,
    xiTerminalKappaSquareDiscriminant_eval, ?_⟩
  · intro u
    rfl
  · norm_num [xiTerminalKappaSquareCubic]
  · exact ⟨xiTerminalLambdaRationalRootCandidateAudit_true,
      xiTerminalKappaSquareDiscriminant_eval,
      xiTerminalKappaSquareDiscriminant_not_square⟩

end Omega.Zeta
