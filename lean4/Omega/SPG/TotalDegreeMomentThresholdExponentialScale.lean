import Omega.SPG.LinearMomentHolographyMinimalDimension

namespace Omega.SPG

/-- Paper label: `cor:spg-total-degree-moment-threshold-exponential-scale`. Any injective linear
readout of the `2^(m*n)` dyadic state space needs at least that many coordinates, so any total
degree moment family whose size is bounded by `Nat.choose (n + r) n` must satisfy the same lower
bound. -/
theorem paper_spg_total_degree_moment_threshold_exponential_scale
    (m n r L : Nat) (f : Fin (2 ^ (m * n)) → Fin L) (hf : Function.Injective f)
    (hL : L ≤ Nat.choose (n + r) n) : 2 ^ (m * n) ≤ Nat.choose (n + r) n := by
  exact le_trans (paper_spg_linear_moment_holography_minimal_dimension m n L f hf).1 hL

end Omega.SPG
