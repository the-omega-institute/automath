import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-branch-rh-zero-temp-chebotarev-product-densities`. -/
theorem paper_xi_branch_rh_zero_temp_chebotarev_product_densities :
    ((2 : ℚ) / 6) * ((6 : ℚ) / 24) * ((24 : ℚ) / 120) = 1 / 60 ∧
      ((1 : ℚ) / 6) * ((1 : ℚ) / 24) * ((1 : ℚ) / 120) = 1 / 17280 ∧
        ((2 : ℚ) / 6) * ((8 : ℚ) / 24) * ((24 : ℚ) / 120) = 1 / 45 := by
  norm_num

end Omega.Zeta
