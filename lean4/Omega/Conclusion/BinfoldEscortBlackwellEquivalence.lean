import Omega.Zeta.XiTimePart9odEscortTvCollapseBlockUniform

namespace Omega.Conclusion

open Omega.Zeta

/-- Concrete finite-scale datum for packaging the bin-fold escort block-uniform approximation as a
Blackwell-style equivalence statement. -/
structure BinfoldEscortBlackwellDatum where
  π : ℕ → Bool → ℝ
  theta_m : ℕ → ℝ
  theta : ℝ
  C1 : ℝ
  C2 : ℝ
  hApprox : ∀ m,
    xiEscortTvDistance (π m) (xiEscortExactBlockLaw theta_m m) ≤ C1 * xiEscortCollapseRate m
  hTheta : ∀ m, |theta_m m - theta| ≤ C2 * xiEscortCollapseRate m

namespace BinfoldEscortBlackwellDatum

/-- The asymptotic equivalence package is the existing block-uniform total-variation comparison
with the two error kernels merged into a single Le Cam-type rate bound. -/
def AsymptoticallyBlackwellEquivalent (D : BinfoldEscortBlackwellDatum) : Prop :=
  xiEscortBlockUniformTvCollapse D.π D.theta (D.C1 + D.C2)

end BinfoldEscortBlackwellDatum

open BinfoldEscortBlackwellDatum

/-- Paper label: `thm:conclusion-binfold-escort-blackwell-equivalence`. The escort experiment is
asymptotically equivalent to its last-bit Bernoulli proxy once the exact block-uniform
approximation and the finite-scale block-mass convergence are combined by the existing two-block
total-variation collapse theorem. -/
theorem paper_conclusion_binfold_escort_blackwell_equivalence
    (D : BinfoldEscortBlackwellDatum) : D.AsymptoticallyBlackwellEquivalent := by
  exact paper_xi_time_part9od_escort_tv_collapse_block_uniform
    D.π D.theta_m D.theta D.C1 D.C2 D.hApprox D.hTheta

end Omega.Conclusion
