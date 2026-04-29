import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Concrete finite-root/tower-count data for the Mellin pole counting wrapper. The determinant has
at most `determinantDegree` nonzero roots, each root contributes at most `perTowerPoleCount` poles
in the height window, and each tower count is bounded by a linear function of the height. -/
structure gm_mellin_pole_count_linear_data where
  determinantDegree : ℝ
  nonzeroRootCount : ℝ
  heightWindow : ℝ
  towerSlope : ℝ
  towerError : ℝ
  perTowerPoleCount : ℝ
  poleCount : ℝ
  determinantDegree_nonneg : 0 ≤ determinantDegree
  perTowerPoleCount_nonneg : 0 ≤ perTowerPoleCount
  nonzeroRootCount_le_degree : nonzeroRootCount ≤ determinantDegree
  perTowerPoleCount_linear :
    perTowerPoleCount ≤ towerSlope * heightWindow + towerError
  poleCount_le_root_towers :
    poleCount ≤ nonzeroRootCount * perTowerPoleCount

namespace gm_mellin_pole_count_linear_data

/-- Linear pole-count bound obtained by multiplying the per-tower `O(T)` bound by the determinant
degree. -/
def pole_count_linear_bound (D : gm_mellin_pole_count_linear_data) : Prop :=
  D.poleCount ≤ D.determinantDegree * (D.towerSlope * D.heightWindow + D.towerError)

end gm_mellin_pole_count_linear_data

open gm_mellin_pole_count_linear_data

/-- Paper label: `cor:gm-mellin-pole-count-linear`. Counting nonzero determinant roots and then
counting the arithmetic pole tower over each root gives a linear height-window bound. -/
theorem paper_gm_mellin_pole_count_linear (D : gm_mellin_pole_count_linear_data) :
    D.pole_count_linear_bound := by
  rw [pole_count_linear_bound]
  have hroot :
      D.nonzeroRootCount * D.perTowerPoleCount ≤
        D.determinantDegree * D.perTowerPoleCount :=
    mul_le_mul_of_nonneg_right D.nonzeroRootCount_le_degree D.perTowerPoleCount_nonneg
  have htower :
      D.determinantDegree * D.perTowerPoleCount ≤
        D.determinantDegree * (D.towerSlope * D.heightWindow + D.towerError) :=
    mul_le_mul_of_nonneg_left D.perTowerPoleCount_linear D.determinantDegree_nonneg
  exact le_trans D.poleCount_le_root_towers (le_trans hroot htower)

end Omega.SyncKernelWeighted
