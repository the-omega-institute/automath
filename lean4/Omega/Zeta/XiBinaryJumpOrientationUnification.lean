import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Zeta

/-- Any two finite binary orientation objects are equivalent because both are equivalent to
`Fin 2`. This packages the common two-point torsor structure behind the discrete and analytic
binary jumps. -/
theorem paper_xi_binary_jump_orientation_unification
    (discreteOrientation analyticOrientation : Type*) [Fintype discreteOrientation]
    [Fintype analyticOrientation] (hdisc : Fintype.card discreteOrientation = 2)
    (han : Fintype.card analyticOrientation = 2) :
    Nonempty (discreteOrientation ≃ analyticOrientation) := by
  classical
  let edisc : discreteOrientation ≃ Fin 2 := Classical.choice <| Fintype.card_eq.mp hdisc
  let ean : analyticOrientation ≃ Fin 2 := Classical.choice <| Fintype.card_eq.mp han
  exact ⟨edisc.trans ean.symm⟩

end Omega.Zeta
