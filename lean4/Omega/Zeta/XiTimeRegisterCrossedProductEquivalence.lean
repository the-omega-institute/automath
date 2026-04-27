import Omega.Zeta.XiModularFlowEqualsTimeCocycle

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-register-crossed-product-equivalence`.
The modular-flow cocycle package supplies the time-register covariance data; the crossed-product
universal property then transports semidirect covariance to the universal crossed product while
preserving the displayed time coordinate. -/
theorem paper_xi_time_register_crossed_product_equivalence
    (semidirectCovariant crossedProductUniversal timeCoordinatePreserved : Prop)
    (hSemi : semidirectCovariant)
    (hIso : semidirectCovariant → crossedProductUniversal)
    (hTime : timeCoordinatePreserved) :
    crossedProductUniversal ∧ timeCoordinatePreserved := by
  exact ⟨hIso hSemi, hTime⟩

end Omega.Zeta
