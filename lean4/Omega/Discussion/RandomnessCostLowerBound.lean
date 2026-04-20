import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Discussion

/-- The chain-rule upper bound used in the Shannon-side discussion:
`I(B₁:B₂ | B₀) ≤ I(B₁:R | B₀) + I(B₁:B₂ | B₀,R)`. -/
def randomnessCostChainUpperBound
    (mutualInfo conditionedRandomness residualMutualInfo : ℝ) : Prop :=
  mutualInfo ≤ conditionedRandomness + residualMutualInfo

/-- The entropy control `I(B₁:R | B₀) ≤ H(R)`. -/
def randomnessEntropyControl (conditionedRandomness entropyR : ℝ) : Prop :=
  conditionedRandomness ≤ entropyR

/-- Paper label: `con:discussion-randomness-cost-lower-bound`.

If the original conditional mutual information is at least the index gap `Γ`, the chain rule
splits it through the extra randomness `R`, and the residual term after conditioning on `R` is at
most `ε`, then the Shannon entropy of `R` must be at least `Γ - ε`. -/
theorem paper_discussion_randomness_cost_lower_bound
    (mutualInfo conditionedRandomness residualMutualInfo entropyR gamma epsilon : ℝ)
    (hChain :
      randomnessCostChainUpperBound mutualInfo conditionedRandomness residualMutualInfo)
    (hEntropy : randomnessEntropyControl conditionedRandomness entropyR)
    (hResidual : residualMutualInfo ≤ epsilon)
    (hGamma : gamma ≤ mutualInfo) :
    gamma - epsilon ≤ entropyR := by
  unfold randomnessCostChainUpperBound at hChain
  unfold randomnessEntropyControl at hEntropy
  linarith

end Omega.Discussion
