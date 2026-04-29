import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- The sum of a coordinate indicator over `Fin m`. -/
lemma conclusion_full_residue_regular_simplex_orbit_sum_indicator {m : ℕ} (r : Fin m) :
    (∑ i : Fin m, (if i = r then (1 : ℚ) else 0)) = 1 := by
  simp

/-- The dot product of two coordinate indicators over `Fin m`. -/
lemma conclusion_full_residue_regular_simplex_orbit_sum_indicator_mul {m : ℕ}
    (r s : Fin m) :
    (∑ i : Fin m,
      (if i = r then (1 : ℚ) else 0) * (if i = s then (1 : ℚ) else 0)) =
      (if r = s then 1 else 0 : ℚ) := by
  by_cases hrs : r = s
  · subst s
    simp
  · simp [hrs, eq_comm]

/-- Paper label: `thm:conclusion-full-residue-regular-simplex-orbit`. -/
theorem paper_conclusion_full_residue_regular_simplex_orbit (m : ℕ) (hm : 0 < m) :
    (∀ r s : Fin m,
      (∑ i : Fin m,
        (((if i = r then 1 else 0 : ℚ) - (1 / (m : ℚ))) *
          ((if i = s then 1 else 0 : ℚ) - (1 / (m : ℚ))))) =
        (if r = s then 1 else 0 : ℚ) - (1 / (m : ℚ))) ∧
    (∀ r : Fin m,
      (∑ i : Fin m, (((if i = r then 1 else 0 : ℚ) - (1 / (m : ℚ))) ^ 2)) =
        ((m : ℚ) - 1) / (m : ℚ)) ∧
    (∀ r s : Fin m, r ≠ s →
      (∑ i : Fin m,
        (((if i = r then 1 else 0 : ℚ) - (if i = s then 1 else 0 : ℚ)) ^ 2)) =
        2) := by
  classical
  have hmQ : (m : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hm)
  have hinner :
      ∀ r s : Fin m,
        (∑ i : Fin m,
          (((if i = r then 1 else 0 : ℚ) - (1 / (m : ℚ))) *
            ((if i = s then 1 else 0 : ℚ) - (1 / (m : ℚ))))) =
          (if r = s then 1 else 0 : ℚ) - (1 / (m : ℚ)) := by
    intro r s
    have hr := conclusion_full_residue_regular_simplex_orbit_sum_indicator (m := m) r
    have hs := conclusion_full_residue_regular_simplex_orbit_sum_indicator (m := m) s
    have hrs := conclusion_full_residue_regular_simplex_orbit_sum_indicator_mul (m := m) r s
    simp [sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp [hmQ]
    by_cases h : r = s
    · subst s
      ring
    · simp [h, eq_comm, mul_comm]
  refine ⟨hinner, ?_, ?_⟩
  · intro r
    calc
      (∑ i : Fin m, (((if i = r then 1 else 0 : ℚ) - (1 / (m : ℚ))) ^ 2)) =
          ∑ i : Fin m,
            (((if i = r then 1 else 0 : ℚ) - (1 / (m : ℚ))) *
              ((if i = r then 1 else 0 : ℚ) - (1 / (m : ℚ)))) := by
        simp [pow_two]
      _ = (if r = r then 1 else 0 : ℚ) - (1 / (m : ℚ)) := hinner r r
      _ = ((m : ℚ) - 1) / (m : ℚ) := by
        field_simp [hmQ]
        norm_num
  · intro r s hne
    simp [pow_two, mul_sub, Finset.sum_sub_distrib]
    simp [hne, eq_comm]
    norm_num

end Omega.Conclusion
