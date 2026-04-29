import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-window6-commutative-shadow-dimension-lower-bound`. -/
theorem paper_conclusion_window6_commutative_shadow_dimension_lower_bound {B : Type*}
    [Fintype B] (certificate : Fin 21 → B) (hcertificate : Function.Injective certificate) :
    21 ≤ Fintype.card B := by
  simpa [Fintype.card_fin] using Fintype.card_le_of_injective certificate hcertificate

end Omega.Conclusion
