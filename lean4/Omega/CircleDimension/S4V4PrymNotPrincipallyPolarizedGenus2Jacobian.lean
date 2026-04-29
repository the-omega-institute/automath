import Omega.CircleDimension.S4V4PrymA2PolarizedIsogenyRigidity

namespace Omega.CircleDimension

open S4V4PrymA2PolarizedIsogenyRigidityData

/-- Paper label: `cor:cdim-s4-v4-prym-not-principally-polarized-genus2-jacobian`.
The natural Prym polarization is the `A₂` Cartan form, whose determinant is `3`, hence it is not a
principal polarization. -/
theorem paper_cdim_s4_v4_prym_not_principally_polarized_genus2_jacobian
    (D : S4V4PrymA2PolarizedIsogenyRigidityData) :
    D.naturalPrymPolarizationIsA2 ∧ a2CartanForm.det != 1 := by
  have hrigid := paper_cdim_s4_v4_prym_a2_polarized_isogeny_rigidity D
  refine ⟨hrigid.2.2, ?_⟩
  norm_num [a2CartanForm, Matrix.det_fin_two]

end Omega.CircleDimension
