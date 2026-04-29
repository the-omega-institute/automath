import Mathlib.Tactic
import Omega.Folding.KilloLeyangTwoBranchFieldsProductGalois

namespace Omega.Folding

/-- Paper label: `thm:killo-leyang-joint-chebotarev-product-law`. -/
theorem paper_killo_leyang_joint_chebotarev_product_law (Ccard Dcard : Nat) :
    (((Ccard : Rat) / killoLeyangTenBranchFieldOrder) *
        ((Dcard : Rat) / killoLeyangCubicBranchFieldOrder) =
      ((Ccard * Dcard : Nat) : Rat) /
        (killoLeyangTenBranchFieldOrder * killoLeyangCubicBranchFieldOrder)) := by
  have h10 : (killoLeyangTenBranchFieldOrder : Rat) ≠ 0 := by
    norm_num [killoLeyangTenBranchFieldOrder]
  have h3 : (killoLeyangCubicBranchFieldOrder : Rat) ≠ 0 := by
    norm_num [killoLeyangCubicBranchFieldOrder]
  field_simp [h10, h3]
  simp

end Omega.Folding
