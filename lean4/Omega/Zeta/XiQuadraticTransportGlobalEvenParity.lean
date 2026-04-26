import Omega.Zeta.XiJGDiscriminantSquareclassInvariance

namespace Omega.Zeta

/-- The transported quadratic discriminant stays in the same squareclass, hence the global parity
class is even in the squareclass quotient. -/
def xi_quadratic_transport_global_even_parity_statement : Prop :=
  ∀ {K : Type*} [Field K] (D : Omega.GU.JoukowskyGodelTransportData K) (discP B : K),
    ∃ u : K,
      xi_jg_discriminant_squareclass_invariance_transport_discriminant D discP B =
        discP * u ^ 2

/-- Paper label: `prop:xi-quadratic-transport-global-even-parity`. -/
theorem paper_xi_quadratic_transport_global_even_parity :
    xi_quadratic_transport_global_even_parity_statement := by
  intro K _ D discP B
  exact paper_xi_jg_discriminant_squareclass_invariance D discP B

end Omega.Zeta
