import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete wrapper data for the weight-tripling ramification count. The arithmetic is completely
determined by the fixed `E[3]`-coset and finite-branch packet counts, so no extra parameters are
needed. -/
structure XiEllipticWeightTriplingRamificationCountData where

namespace XiEllipticWeightTriplingRamificationCountData

/-- The nine `3`-torsion preimages above the totally ramified point. -/
def torsionPreimageCount : ℕ := 9

/-- The five finite branch packets pulled back along `[3]`. -/
def finiteBranchPacketCount : ℕ := 5

/-- Each `3`-torsion preimage contributes `4 - 1 = 3` to the ramification divisor. -/
def torsionContributionPerPoint : ℕ := 3

/-- Each point in a finite branch packet contributes `2 - 1 = 1`. -/
def finiteContributionPerPoint : ℕ := 1

/-- Total contribution from the pulled-back `E[3]` locus. -/
def torsionContribution : ℕ :=
  torsionPreimageCount * torsionContributionPerPoint

/-- Total contribution from the five finite branch packets. -/
def finiteBranchContribution : ℕ :=
  finiteBranchPacketCount * torsionPreimageCount * finiteContributionPerPoint

/-- Ramification degree computed directly from the pulled-back divisor. -/
def totalRamificationDegree : ℕ :=
  torsionContribution + finiteBranchContribution

/-- Degree of `y₃ = y ∘ [3]`: degree `4` times degree `9`. -/
def tripledWeightDegree : ℕ := 4 * 9

/-- Hurwitz side for an elliptic source curve: `2 * deg(y₃)`. -/
def hurwitzSide : ℕ := 2 * tripledWeightDegree

/-- Paper-facing package: the pulled-back branch data give degree `72`, and this equals the
Riemann-Hurwitz count `2 * 36 = 72`. -/
def package (_D : XiEllipticWeightTriplingRamificationCountData) : Prop :=
  torsionContribution = 9 * 3 ∧
    finiteBranchContribution = 5 * 9 ∧
    totalRamificationDegree = 72 ∧ hurwitzSide = 72 ∧ totalRamificationDegree = hurwitzSide

end XiEllipticWeightTriplingRamificationCountData

open XiEllipticWeightTriplingRamificationCountData

set_option maxHeartbeats 400000 in
/-- Under multiplication by `3`, the nine `E[3]` preimages of the totally ramified point each
contribute `3`, the five finite branch packets contribute `45`, and the total degree `72`
matches the Hurwitz side `2 * 36 = 72`.
    cor:xi-terminal-zm-elliptic-weight-tripling-ramification-count -/
theorem paper_xi_terminal_zm_elliptic_weight_tripling_ramification_count
    (D : XiEllipticWeightTriplingRamificationCountData) : D.package := by
  unfold XiEllipticWeightTriplingRamificationCountData.package
  unfold torsionContribution finiteBranchContribution totalRamificationDegree hurwitzSide
  unfold torsionPreimageCount finiteBranchPacketCount torsionContributionPerPoint
  unfold finiteContributionPerPoint tripledWeightDegree
  native_decide

end Omega.Zeta
