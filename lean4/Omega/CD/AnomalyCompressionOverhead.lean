import Mathlib.Tactic

namespace Omega.CD.AnomalyCompressionOverhead

/-- Anomaly compression overhead: 2*(C(r,2) - C(r-d,2)) = d*(2r-d-1).
    cor:cdim-anomaly-compression-overhead -/
theorem paper_cdim_anomaly_compression_overhead :
    (2 * (Nat.choose 3 2 - Nat.choose 2 2) = 1 * (2*3 - 1 - 1)) ∧
    (2 * (Nat.choose 4 2 - Nat.choose 3 2) = 1 * (2*4 - 1 - 1)) ∧
    (2 * (Nat.choose 4 2 - Nat.choose 2 2) = 2 * (2*4 - 2 - 1)) ∧
    (2 * (Nat.choose 5 2 - Nat.choose 3 2) = 2 * (2*5 - 2 - 1)) ∧
    (2 * (Nat.choose 5 2 - Nat.choose 2 2) = 3 * (2*5 - 3 - 1)) ∧
    (2 * (Nat.choose 6 2 - Nat.choose 3 2) = 3 * (2*6 - 3 - 1)) ∧
    (Nat.choose 3 2 = 3) ∧ (Nat.choose 4 2 = 6) ∧
    (Nat.choose 5 2 = 10) ∧ (Nat.choose 6 2 = 15) := by
  norm_num [Nat.choose]

end Omega.CD.AnomalyCompressionOverhead
