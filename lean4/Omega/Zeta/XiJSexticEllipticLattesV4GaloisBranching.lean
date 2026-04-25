import Mathlib.Data.Fintype.Card
import Omega.Zeta.XiJSexticEllipticLattesBelyiNormalization

namespace Omega.Zeta

noncomputable section

/-- Paper label: `cor:xi-j-sextic-elliptic-lattes-v4-galois-branching`. The normalized Belyi
package fixes the `(2,2)` passport at each branch fiber and records the deck-group cardinality
`4`. -/
theorem paper_xi_j_sextic_elliptic_lattes_v4_galois_branching
    (D : xi_j_sextic_elliptic_lattes_belyi_normalization_data) :
    xi_j_sextic_elliptic_lattes_belyi_normalization_passport = [[2, 2], [2, 2], [2, 2]] ∧
      Fintype.card xi_j_sextic_elliptic_lattes_belyi_normalization_deckGroup = 4 := by
  have hNorm := paper_xi_j_sextic_elliptic_lattes_belyi_normalization D
  exact hNorm.2.2.2.2

end

end Omega.Zeta
