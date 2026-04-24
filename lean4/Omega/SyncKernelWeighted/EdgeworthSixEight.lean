import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Audited variance at the symmetry point. -/
def edgeworthSigmaSq : ℚ := 11 / 102

/-- Audited fourth cumulant. -/
def edgeworthKappa4 : ℚ := 1559 / 58956

/-- Audited sixth cumulant. -/
def edgeworthKappa6 : ℚ := -17123893 / 1635675264

/-- Audited eighth cumulant. -/
def edgeworthKappa8 : ℚ := -122803509253 / 630280201728

/-- Normalized sixth cumulant fingerprint. -/
def edgeworthNormalizedSixth : ℚ :=
  edgeworthKappa6 / edgeworthSigmaSq ^ 3

/-- Normalized eighth cumulant fingerprint. -/
def edgeworthNormalizedEighth : ℚ :=
  edgeworthKappa8 / edgeworthSigmaSq ^ 4

/-- Sixth-cumulant second-order Edgeworth coefficient. -/
def edgeworthSecondOrderSixthCoeff : ℚ :=
  edgeworthKappa6 / (720 * edgeworthSigmaSq ^ 3)

/-- Squared fourth-cumulant second-order Edgeworth coefficient. -/
def edgeworthSecondOrderFourthSqCoeff : ℚ :=
  edgeworthKappa4 ^ 2 / (1152 * edgeworthSigmaSq ^ 4)

/-- Paper label: `cor:edgeworth-six-eight`.
The normalized sixth/eighth cumulants and the two second-order Edgeworth coefficients reduce to
the audited rational fingerprints recorded in the paper. -/
theorem paper_edgeworth_six_eight :
    edgeworthNormalizedSixth = -51371679 / 6154544 ∧
      edgeworthNormalizedEighth = -3315694749831 / 2301799456 ∧
      edgeworthSecondOrderSixthCoeff = -17123893 / 1477090560 ∧
      edgeworthSecondOrderFourthSqCoeff = 2430481 / 541599872 := by
  norm_num [edgeworthNormalizedSixth, edgeworthNormalizedEighth, edgeworthSecondOrderSixthCoeff,
    edgeworthSecondOrderFourthSqCoeff, edgeworthSigmaSq, edgeworthKappa4, edgeworthKappa6,
    edgeworthKappa8]

end Omega.SyncKernelWeighted
