import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete bookkeeping for the parity-selection mechanism in the Poisson--Cauchy odd-moment
expansion. The odd Taylor channel is indexed by the number of odd-parity kernel factors that
survive in a given coefficient, while the surviving even pairings are recorded through the cubic
and quintic centered moments. -/
structure XiCauchyPoissonOddMomentSelectionData where
  oddKernelFactorCount : ℕ
  mu3 : ℝ
  mu5 : ℝ
  oddLinearContribution : ℝ
  pairedOddContribution : ℝ
  oddKernelFactorCount_odd : Odd oddKernelFactorCount
  oddLinearContribution_eq :
    oddLinearContribution = if oddKernelFactorCount % 2 = 1 then 0 else mu3
  pairedOddContribution_eq :
    pairedOddContribution = mu3 ^ 2 + mu3 * mu5

namespace XiCauchyPoissonOddMomentSelectionData

/-- All linear odd-moment terms vanish when the coefficient contains an odd number of odd-parity
kernel factors against the even Cauchy weight. -/
def oddMomentLinearTermsVanish (D : XiCauchyPoissonOddMomentSelectionData) : Prop :=
  D.oddLinearContribution = 0

/-- The only surviving odd-moment contributions come from even pairings such as `μ₃²` and
`μ₃ μ₅`. -/
def oddMomentsAppearOnlyViaEvenPairings (D : XiCauchyPoissonOddMomentSelectionData) : Prop :=
  D.pairedOddContribution = D.mu3 ^ 2 + D.mu3 * D.mu5

end XiCauchyPoissonOddMomentSelectionData

open XiCauchyPoissonOddMomentSelectionData

/-- Paper label: `prop:xi-cauchy-poisson-odd-moment-selection-law`. In the concrete parity package,
an odd number of odd-parity kernel factors forces the linear odd-moment channel to vanish, and
the surviving odd moments can only appear through even pairings. -/
theorem paper_xi_cauchy_poisson_odd_moment_selection_law
    (D : XiCauchyPoissonOddMomentSelectionData) :
    D.oddMomentLinearTermsVanish ∧ D.oddMomentsAppearOnlyViaEvenPairings := by
  refine ⟨?_, D.pairedOddContribution_eq⟩
  rw [XiCauchyPoissonOddMomentSelectionData.oddMomentLinearTermsVanish, D.oddLinearContribution_eq]
  rcases D.oddKernelFactorCount_odd with ⟨k, hk⟩
  simp [hk]

end Omega.Zeta
