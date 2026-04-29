import Omega.Zeta.XiOffsliceRealpartSumLaw

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Paper label: `thm:xi-offslice-blaschke-origin-modulus`. The origin modulus of the finite
Blaschke product is exactly the product of the root moduli, and the logarithmic offslice weight is
the negative log of that modulus. -/
theorem paper_xi_offslice_blaschke_origin_modulus (h : xi_offslice_realpart_sum_law_data) :
    xi_offslice_realpart_sum_law_origin_modulus h = ∏ j, |h.a j| ∧
      xi_offslice_realpart_sum_law_weight h =
        -Real.log (xi_offslice_realpart_sum_law_origin_modulus h) := by
  rcases paper_xi_offslice_realpart_sum_law h with ⟨_, horigin, _⟩
  constructor
  · rfl
  · simpa using horigin.symm

end

end Omega.Zeta
