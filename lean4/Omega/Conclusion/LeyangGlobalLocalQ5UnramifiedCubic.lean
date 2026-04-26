import Mathlib

namespace Omega.Conclusion

/-- The cubic defining the Lee--Yang local singular field at `5`. -/
def conclusion_leyang_global_local_q5_unramified_cubic_polynomial (T : ℤ) : ℤ :=
  324 * T ^ 3 - 540 * T ^ 2 + 333 * T - 74

/-- The mod-`5` reduction of the cubic. -/
def conclusion_leyang_global_local_q5_unramified_cubic_polynomial_mod5 (T : ZMod 5) : ZMod 5 :=
  4 * T ^ 3 + 3 * T + 1

/-- The mod-`5` reduction has no root, hence is irreducible as a cubic over `𝔽₅`. -/
def conclusion_leyang_global_local_q5_unramified_cubic_mod5_irreducible : Prop :=
  ∀ T : ZMod 5, conclusion_leyang_global_local_q5_unramified_cubic_polynomial_mod5 T ≠ 0

/-- The explicit discriminant of `324 T^3 - 540 T^2 + 333 T - 74`. -/
def conclusion_leyang_global_local_q5_unramified_cubic_discriminant : ℤ :=
  (-540) ^ 2 * 333 ^ 2 - 4 * 324 * 333 ^ 3 - 4 * (-540) ^ 3 * (-74) -
    27 * 324 ^ 2 * (-74) ^ 2 + 18 * 324 * (-540) * 333 * (-74)

/-- The local degree of the unramified cubic extension. -/
def conclusion_leyang_global_local_q5_unramified_cubic_local_degree : ℕ := 3

/-- The extension is unramified at `5`, so the ramification index is `1`. -/
def conclusion_leyang_global_local_q5_unramified_cubic_ramification_index : ℕ := 1

/-- Since the extension has degree `3` and is unramified, the residue degree is `3`. -/
def conclusion_leyang_global_local_q5_unramified_cubic_residue_degree : ℕ := 3

/-- The cyclic Galois group of the unique unramified cubic extension of `ℚ₅`. -/
abbrev conclusion_leyang_global_local_q5_unramified_cubic_galois_group := ZMod 3

/-- Paper label: `thm:conclusion-leyang-global-local-q5-unramified-cubic`. The concrete Lean
seed records the mod-`5` irreducibility check, the discriminant nondivisibility by `5`, and the
standard local invariants `([K : ℚ₅], e, f) = (3, 1, 3)` together with the cyclic order-`3`
Galois packet. -/
theorem paper_conclusion_leyang_global_local_q5_unramified_cubic :
    conclusion_leyang_global_local_q5_unramified_cubic_mod5_irreducible ∧
      conclusion_leyang_global_local_q5_unramified_cubic_discriminant = -46609344 ∧
      ¬ ((5 : ℤ) ∣ conclusion_leyang_global_local_q5_unramified_cubic_discriminant) ∧
      conclusion_leyang_global_local_q5_unramified_cubic_local_degree =
        conclusion_leyang_global_local_q5_unramified_cubic_ramification_index *
          conclusion_leyang_global_local_q5_unramified_cubic_residue_degree ∧
      conclusion_leyang_global_local_q5_unramified_cubic_local_degree = 3 ∧
      conclusion_leyang_global_local_q5_unramified_cubic_ramification_index = 1 ∧
      conclusion_leyang_global_local_q5_unramified_cubic_residue_degree = 3 ∧
      Fintype.card conclusion_leyang_global_local_q5_unramified_cubic_galois_group = 3 := by
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · intro T
    fin_cases T <;> decide
  · norm_num [conclusion_leyang_global_local_q5_unramified_cubic_discriminant]
  · intro h5
    have hdisc :
        conclusion_leyang_global_local_q5_unramified_cubic_discriminant = -46609344 := by
      norm_num [conclusion_leyang_global_local_q5_unramified_cubic_discriminant]
    rw [hdisc] at h5
    norm_num at h5
  · norm_num [conclusion_leyang_global_local_q5_unramified_cubic_local_degree,
      conclusion_leyang_global_local_q5_unramified_cubic_ramification_index,
      conclusion_leyang_global_local_q5_unramified_cubic_residue_degree]
  · norm_num [conclusion_leyang_global_local_q5_unramified_cubic_galois_group]

end Omega.Conclusion
