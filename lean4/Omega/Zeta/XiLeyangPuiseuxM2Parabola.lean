import Omega.Zeta.XiLeyangSquareRootCollisionLeadingZerosN2

namespace Omega.Zeta

/-- Paper label: `cor:xi-leyang-puiseux-m2-parabola`.
The Puiseux `m = 2` parabola case is the existing square-root collision `n⁻²` package. -/
theorem paper_xi_leyang_puiseux_m2_parabola
    (D : XiLeyangSquareRootCollisionData) : D.hasQuantizedLeadingZerosN2 := by
  exact paper_xi_leyang_square_root_collision_leading_zeros_n2 D

end Omega.Zeta
