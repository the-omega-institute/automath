import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-disjointness-boolean-witt-sqrt2-criterion`. -/
theorem paper_xi_disjointness_boolean_witt_sqrt2_criterion
    {F : Type} [Field F] [CharZero F] :
    (∃ x y : F, (x ≠ 0 ∨ y ≠ 0) ∧ x ^ 2 - (2 : F) * y ^ 2 = 0) ↔
      ∃ r : F, r ^ 2 = (2 : F) := by
  constructor
  · rintro ⟨x, y, hnonzero, hquad⟩
    have hy : y ≠ 0 := by
      intro hy_zero
      have hx_sq : x ^ 2 = 0 := by
        simpa [hy_zero] using hquad
      have hx_zero : x = 0 := eq_zero_of_pow_eq_zero hx_sq
      exact hnonzero.elim (fun hx => hx hx_zero) (fun hy' => hy' hy_zero)
    refine ⟨x / y, ?_⟩
    have hx_eq : x ^ 2 = (2 : F) * y ^ 2 := sub_eq_zero.mp hquad
    field_simp [hy]
    rw [hx_eq]
    ring
  · rintro ⟨r, hr⟩
    refine ⟨r, 1, Or.inr one_ne_zero, ?_⟩
    rw [hr]
    ring

end Omega.Zeta
