import Mathlib
import Omega.POM.S5GaloisArithmetic

namespace Omega.POM

/-- The conjugacy-class size attached to a quintic factorization pattern in `S₅`. -/
def pom_s5_chebotarev_splitting_density_class_size : List ℕ → ℕ
  | [1, 1, 1, 1, 1] => 1
  | [2, 1, 1, 1] => 10
  | [2, 2, 1] => 15
  | [3, 1, 1] => 20
  | [3, 2] => 20
  | [4, 1] => 30
  | [5] => 24
  | _ => 0

/-- The Chebotarev density attached to a quintic factorization pattern. -/
def pom_s5_chebotarev_splitting_density_density (pattern : List ℕ) : ℚ :=
  pom_s5_chebotarev_splitting_density_class_size pattern / Nat.factorial 5

/-- Paper label: `cor:pom-s5-chebotarev-splitting-density`. The seven unramified quintic
factorization patterns match the seven `S₅` conjugacy classes, so their Chebotarev densities are
the corresponding class sizes divided by `|S₅| = 120`. -/
theorem paper_pom_s5_chebotarev_splitting_density :
    pom_s5_chebotarev_splitting_density_density [1, 1, 1, 1, 1] = (1 : ℚ) / 120 ∧
      pom_s5_chebotarev_splitting_density_density [2, 1, 1, 1] = (10 : ℚ) / 120 ∧
      pom_s5_chebotarev_splitting_density_density [2, 2, 1] = (15 : ℚ) / 120 ∧
      pom_s5_chebotarev_splitting_density_density [3, 1, 1] = (20 : ℚ) / 120 ∧
      pom_s5_chebotarev_splitting_density_density [3, 2] = (20 : ℚ) / 120 ∧
      pom_s5_chebotarev_splitting_density_density [4, 1] = (30 : ℚ) / 120 ∧
      pom_s5_chebotarev_splitting_density_density [5] = (24 : ℚ) / 120 := by
  have hs5 : Nat.factorial 5 = 120 := Omega.POM.S5GaloisArithmetic.s5_order
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [pom_s5_chebotarev_splitting_density_density,
      pom_s5_chebotarev_splitting_density_class_size, hs5]

end Omega.POM
