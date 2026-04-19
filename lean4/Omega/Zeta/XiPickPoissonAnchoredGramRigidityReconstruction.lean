import Mathlib.Tactic
import Omega.Zeta.XiGramshiftToeplitzCayleyLogBridge
import Omega.Zeta.XiPickPoissonAnchoredTransverseSeparationInversion

namespace Omega.Zeta

/-- Closed-form recovery of the horizontal separation squared from a Pick--Poisson ratio. -/
noncomputable def xiPickPoissonRecoveredDeltaSq (pj pk rho : ℝ) : ℝ :=
  (rho ^ 2 * (pj + pk) ^ 2 - (pj - pk) ^ 2) / (1 - rho ^ 2)

/-- Each indexed pair recovers its squared horizontal separation from the anchored
Pick--Poisson identity. -/
def xiPickPoissonPairwiseSeparationRecovery
    {pairCount : ℕ} (pj pk rho Delta : Fin pairCount → ℝ) : Prop :=
  ∀ i : Fin pairCount, xiPickPoissonRecoveredDeltaSq (pj i) (pk i) (rho i) = Delta i ^ 2

/-- One-dimensional rigidity: the recovered horizontal coordinates agree with the original ones
up to reflection about the anchored center. -/
def xiPickPoissonRealLineRigidity
    {pointCount : ℕ} (anchor : ℝ) (horizontal recoveredHorizontal : Fin pointCount → ℝ) : Prop :=
  ∀ i : Fin pointCount,
    recoveredHorizontal i = horizontal i ∨ recoveredHorizontal i = 2 * anchor - horizontal i

/-- The Cayley reconstruction of the anchored defect configuration from horizontal and depth
coordinates. -/
noncomputable def xiPickPoissonDiskConfiguration
    {pointCount : ℕ} (horizontal depths : Fin pointCount → ℝ) : Fin pointCount → ℂ :=
  fun i => xiCayley (horizontal i) (depths i)

/-- Pointwise inversion recovers every indexed horizontal separation, any exact equality of the
recovered coordinates with the anchored original coordinates gives rigidity on the real line, and
the same equality transports through the Cayley map to recover the anchored disk configuration.
    thm:xi-pick-poisson-anchored-gram-rigidity-reconstruction -/
theorem paper_xi_pick_poisson_anchored_gram_rigidity_reconstruction
    {pairCount pointCount : ℕ}
    (pj pk rho Delta : Fin pairCount → ℝ)
    (hden : ∀ i : Fin pairCount, Delta i ^ 2 + (pj i + pk i) ^ 2 ≠ 0)
    (hRatio :
      ∀ i : Fin pairCount,
        rho i ^ 2 = (Delta i ^ 2 + (pj i - pk i) ^ 2) / (Delta i ^ 2 + (pj i + pk i) ^ 2))
    (hrho : ∀ i : Fin pairCount, rho i ^ 2 ≠ 1)
    (anchor : ℝ)
    (horizontal recoveredHorizontal depths : Fin pointCount → ℝ)
    (hline :
      ∀ i : Fin pointCount,
        recoveredHorizontal i = horizontal i ∨ recoveredHorizontal i = 2 * anchor - horizontal i)
    (hexact : recoveredHorizontal = horizontal) :
    xiPickPoissonPairwiseSeparationRecovery pj pk rho Delta ∧
      xiPickPoissonRealLineRigidity anchor horizontal recoveredHorizontal ∧
      xiPickPoissonDiskConfiguration recoveredHorizontal depths =
        xiPickPoissonDiskConfiguration horizontal depths := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa [xiPickPoissonRecoveredDeltaSq] using
      (paper_xi_pick_poisson_anchored_transverse_separation_inversion
        (pj i) (pk i) (rho i) (Delta i) (hden i) (hRatio i) (hrho i)).symm
  · simpa [xiPickPoissonRealLineRigidity] using hline
  · ext i
    simp [xiPickPoissonDiskConfiguration, hexact]

end Omega.Zeta
