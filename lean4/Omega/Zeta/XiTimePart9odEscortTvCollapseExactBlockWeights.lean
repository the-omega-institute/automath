import Omega.Zeta.XiTimePart9odEscortTvCollapseBlockUniform

namespace Omega.Zeta

/-- The exact two-block mixture with block masses `p0` and `p1`. -/
def xiEscortExactBlockWeightsLaw (p0 p1 : ℝ) : Bool → ℝ
  | false => p0
  | true => p1

/-- Paper label: `prop:xi-time-part9od-escort-tv-collapse-exact-block-weights`. Rewriting the
block-uniform approximant with the exact block masses `p_{m,q}(1)` and `p_{m,q}(0)` gives the same
law, so the existing escort-collapse estimate applies unchanged. -/
theorem paper_xi_time_part9od_escort_tv_collapse_exact_block_weights
    (π : ℕ → Bool → ℝ) (blockMass : ℕ → Bool → ℝ) (C : ℝ)
    (hApprox : ∀ m,
      xiEscortTvDistance (π m) (xiEscortExactBlockLaw (fun m => blockMass m true) m) ≤
        C * xiEscortCollapseRate m)
    (hMass : ∀ m, blockMass m false = 1 - blockMass m true) :
    ∀ m,
      xiEscortTvDistance (π m)
        (xiEscortExactBlockWeightsLaw (blockMass m false) (blockMass m true)) ≤
          C * xiEscortCollapseRate m := by
  intro m
  simpa [xiEscortExactBlockWeightsLaw, xiEscortExactBlockLaw, xiEscortBlockLaw, hMass m] using
    hApprox m

end Omega.Zeta
