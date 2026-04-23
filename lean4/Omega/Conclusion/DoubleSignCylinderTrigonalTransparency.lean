import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-double-sign-cylinder-trigonal-transparency`. If the conditional
density on each of the four sign boxes is the same value `d σ`, then averaging over any nonempty
subcollection of boxes preserves that value. -/
theorem paper_conclusion_double_sign_cylinder_trigonal_transparency
    (δ : (Bool × Bool) → Fin 3 → ℚ) (d : Fin 3 → ℚ) (hδ : ∀ ε σ, δ ε σ = d σ) :
    ∀ C : Finset (Bool × Bool), C.Nonempty → ∀ σ : Fin 3,
      Finset.sum C (fun ε => (1 / 4 : ℚ) * δ ε σ) / ((C.card : ℚ) / 4) = d σ := by
  intro C hC σ
  have hcard : (C.card : ℚ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hC
  calc
    Finset.sum C (fun ε => (1 / 4 : ℚ) * δ ε σ) / ((C.card : ℚ) / 4)
        = ((C.card : ℚ) * ((1 / 4 : ℚ) * d σ)) / ((C.card : ℚ) / 4) := by
            simp [hδ]
    _ = d σ := by
      field_simp [hcard]

end Omega.Conclusion
