import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-a4t-newman-resultant-curve-intersection`. -/
theorem paper_pom_a4t_newman_resultant_curve_intersection (P4 resultant : Polynomial ℤ)
    (h_resultant : resultant = (Polynomial.X + 1) * P4) (t : ℤ) (ht : t ≠ -1) :
    Polynomial.eval t resultant = 0 ↔ Polynomial.eval t P4 = 0 := by
  rw [h_resultant, Polynomial.eval_mul]
  have ht_add : t + 1 ≠ 0 := by
    intro h
    apply ht
    omega
  constructor
  · intro h
    have hmul : (t + 1) * Polynomial.eval t P4 = 0 := by
      simpa using h
    rcases mul_eq_zero.mp hmul with hzero | hzero
    · exact False.elim (ht_add hzero)
    · exact hzero
  · intro h
    simp [h]

end Omega.POM
