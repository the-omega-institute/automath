import Omega.Zeta.XiHankelPrimitiveGapVanishingCriterion

namespace Omega.Zeta

open xi_hankel_primitive_gap_vanishing_criterion_data

/-- Paper label: `cor:xi-hankel-null-extra-vectors-one-step-criterion`. -/
theorem paper_xi_hankel_null_extra_vectors_one_step_criterion
    (D : xi_hankel_primitive_gap_vanishing_criterion_data)
    (hker : LinearMap.ker D.hankelMap = D.truncatedMultiples) :
    Module.finrank ℚ D.xi_hankel_primitive_gap_vanishing_criterion_primitive_quotient = 0 := by
  exact D.xi_hankel_primitive_gap_vanishing_criterion_primitive_quotient_finrank_zero_iff.mpr hker

end Omega.Zeta
