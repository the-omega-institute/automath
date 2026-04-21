import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

namespace Omega.RootUnitCharacterPressureTensor

/-- Paper label: `cor:root-unit-s4xs7-chebotarev-product`.
The finite Chebotarev density on `S₄ × S₇` factors as the product of the corresponding densities
on `S₄` and `S₇`. -/
theorem paper_root_unit_s4xs7_chebotarev_product
    (C4 : Finset (Equiv.Perm (Fin 4))) (C7 : Finset (Equiv.Perm (Fin 7))) :
    (((C4.product C7).card : ℚ) /
        ((Fintype.card (Equiv.Perm (Fin 4)) : ℚ) * (Fintype.card (Equiv.Perm (Fin 7)) : ℚ))) =
      ((C4.card : ℚ) / (Fintype.card (Equiv.Perm (Fin 4)) : ℚ)) *
        ((C7.card : ℚ) / (Fintype.card (Equiv.Perm (Fin 7)) : ℚ)) := by
  norm_num [Fintype.card_perm]
  ring

end Omega.RootUnitCharacterPressureTensor
