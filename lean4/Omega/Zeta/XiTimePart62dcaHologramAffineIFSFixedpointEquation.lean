import Omega.Zeta.XiTimePart62dcHologramBernoulliExactDimensional

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `prop:xi-time-part62dca-hologram-affine-ifs-fixedpoint-equation`. In the existing
Bernoulli hologram interface, every hologram ball is definitionally the corresponding cylinder,
whose mass is the finite product of the symbol probabilities. -/
theorem paper_xi_time_part62dca_hologram_affine_ifs_fixedpoint_equation
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) :
    D.exact_dimensional ∧
      (∀ n (w : D.addr_prefix n), D.ball_mass w =
        ∏ i : Fin n,
          D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_probability (w i)) := by
  constructor
  · intro n w
    rfl
  · intro n w
    rfl

end Omega.Zeta
