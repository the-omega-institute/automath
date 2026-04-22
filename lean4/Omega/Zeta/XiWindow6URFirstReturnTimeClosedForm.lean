import Mathlib.Tactic

namespace Omega.Zeta

/-- The numerator of the audited first-return PGF for the window-`6` boundary block `U_R`. -/
def xiWindow6UrFirstReturnNumerator (z : ℚ) : ℚ :=
  110 * z ^ 4 + 1525 * z ^ 3 - 1221 * z ^ 2 - 10692 * z

/-- The denominator of the audited first-return PGF for the window-`6` boundary block `U_R`. -/
def xiWindow6UrFirstReturnDenominator (z : ℚ) : ℚ :=
  623 * z ^ 3 + 14317 * z ^ 2 + 71010 * z - 96228

/-- The explicit rational PGF read off from the generated certificate. -/
def xiWindow6UrFirstReturnPgf (z : ℚ) : ℚ :=
  xiWindow6UrFirstReturnNumerator z / xiWindow6UrFirstReturnDenominator z

/-- Quotient-rule numerator for the first derivative of the explicit PGF. -/
def xiWindow6UrFirstReturnDerivNumerator (z : ℚ) : ℚ :=
  68530 * z ^ 6 + 3149740 * z ^ 5 + 46027408 * z ^ 4 + 187562412 * z ^ 3 -
    373868946 * z ^ 2 + 234988776 * z + 1028869776

/-- Formal first derivative of the audited PGF. -/
def xiWindow6UrFirstReturnPgfDeriv (z : ℚ) : ℚ :=
  xiWindow6UrFirstReturnDerivNumerator z / xiWindow6UrFirstReturnDenominator z ^ 2

/-- Quotient-rule numerator for the second derivative of the explicit PGF. -/
def xiWindow6UrFirstReturnSecondDerivNumerator (z : ℚ) : ℚ :=
  7209938412 * z ^ 6 + 280867935132 * z ^ 5 + 3267696941388 * z ^ 4 +
    5575678570548 * z ^ 3 - 68085185486472 * z ^ 2 - 3654545444352 * z -
    168732585524448

/-- Formal second derivative of the audited PGF. -/
def xiWindow6UrFirstReturnPgfSecondDeriv (z : ℚ) : ℚ :=
  xiWindow6UrFirstReturnSecondDerivNumerator z / xiWindow6UrFirstReturnDenominator z ^ 3

/-- The exact mean extracted from the first derivative at `z = 1`. -/
def xiWindow6UrFirstReturnMean : ℚ :=
  xiWindow6UrFirstReturnPgfDeriv 1

/-- The exact variance extracted from `F''(1) + F'(1) - F'(1)^2`. -/
def xiWindow6UrFirstReturnVariance : ℚ :=
  xiWindow6UrFirstReturnPgfSecondDeriv 1 + xiWindow6UrFirstReturnMean -
    xiWindow6UrFirstReturnMean ^ 2

/-- Closed-form certificate for the window-`6` `U_R` first-return PGF and its first two moments.
    prop:xi-window6-UR-first-return-time-closed-form -/
def xiWindow6UrFirstReturnTimeClosedForm : Prop :=
  (∀ z : ℚ,
      xiWindow6UrFirstReturnPgf z =
        z * (110 * z ^ 3 + 1525 * z ^ 2 - 1221 * z - 10692) /
          (623 * z ^ 3 + 14317 * z ^ 2 + 71010 * z - 96228)) ∧
    xiWindow6UrFirstReturnPgf 1 = 1 ∧
    xiWindow6UrFirstReturnPgfDeriv 1 = 32 / 3 ∧
    xiWindow6UrFirstReturnPgfSecondDeriv 1 = 3284932 / 15417 ∧
    xiWindow6UrFirstReturnMean = 32 / 3 ∧
    xiWindow6UrFirstReturnVariance = 1695268 / 15417

theorem paper_xi_window6_ur_first_return_time_closed_form :
    xiWindow6UrFirstReturnTimeClosedForm := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    simp [xiWindow6UrFirstReturnPgf, xiWindow6UrFirstReturnNumerator,
      xiWindow6UrFirstReturnDenominator]
    congr 1
    ring
  · norm_num [xiWindow6UrFirstReturnPgf, xiWindow6UrFirstReturnNumerator,
      xiWindow6UrFirstReturnDenominator]
  · norm_num [xiWindow6UrFirstReturnPgfDeriv, xiWindow6UrFirstReturnDerivNumerator,
      xiWindow6UrFirstReturnDenominator]
  · norm_num [xiWindow6UrFirstReturnPgfSecondDeriv, xiWindow6UrFirstReturnSecondDerivNumerator,
      xiWindow6UrFirstReturnDenominator]
  · norm_num [xiWindow6UrFirstReturnMean, xiWindow6UrFirstReturnPgfDeriv,
      xiWindow6UrFirstReturnDerivNumerator, xiWindow6UrFirstReturnDenominator]
  · norm_num [xiWindow6UrFirstReturnVariance, xiWindow6UrFirstReturnMean,
      xiWindow6UrFirstReturnPgfSecondDeriv, xiWindow6UrFirstReturnSecondDerivNumerator,
      xiWindow6UrFirstReturnPgfDeriv, xiWindow6UrFirstReturnDerivNumerator,
      xiWindow6UrFirstReturnDenominator]

end Omega.Zeta
