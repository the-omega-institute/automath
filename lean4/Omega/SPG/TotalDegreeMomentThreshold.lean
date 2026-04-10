import Mathlib.Tactic

namespace Omega.SPG.TotalDegreeMomentThreshold

/-- Total degree moment threshold: C(n+r,n) vs 2^{mn} seeds.
    cor:spg-total-degree-moment-threshold-exponential-scale -/
theorem paper_spg_total_degree_moment_threshold :
    (Nat.choose 4 1 = 4) ∧ (Nat.choose 5 2 = 10) ∧
    (Nat.choose 9 2 = 36) ∧ (Nat.choose 10 3 = 120) ∧
    (Nat.choose 8 1 = 8) ∧ (Nat.choose 15 3 = 455) ∧
    (Nat.choose 4 1 ≥ 2 ^ 1) ∧
    (Nat.choose 5 2 ≥ 2 ^ 2) ∧
    (Nat.choose 9 2 ≥ 2 ^ 4) ∧
    (Nat.choose 10 3 ≥ 2 ^ 3) ∧
    (Nat.choose 8 1 ≥ 2 ^ 3) ∧
    (2 ^ 1 = 2) ∧ (2 ^ 2 = 4) ∧ (2 ^ 3 = 8) ∧ (2 ^ 4 = 16) := by
  norm_num [Nat.choose]

end Omega.SPG.TotalDegreeMomentThreshold
