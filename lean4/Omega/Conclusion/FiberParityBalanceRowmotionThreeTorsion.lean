import Mathlib.Tactic

namespace Omega.Conclusion

lemma conclusion_fiber_parity_balance_rowmotion_three_torsion_mod_one_iff_dvd_add_two
    (n : ℕ) : n % 3 = 1 ↔ 3 ∣ n + 2 := by
  constructor
  · intro h
    omega
  · intro h
    omega

/-- Paper label: `cor:conclusion-fiber-parity-balance-rowmotion-three-torsion`. -/
theorem paper_conclusion_fiber_parity_balance_rowmotion_three_torsion {r : ℕ}
    (ell : Fin r → ℕ) (rowOrder : ℕ) (parityBalanced : Prop)
    (hparity : parityBalanced ↔ ∃ i, ell i % 3 = 1)
    (horder : (3 ∣ rowOrder) ↔ ∃ i, 3 ∣ ell i + 2) :
    parityBalanced ↔ 3 ∣ rowOrder := by
  rw [hparity, horder]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i,
      (conclusion_fiber_parity_balance_rowmotion_three_torsion_mod_one_iff_dvd_add_two
        (ell i)).mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i,
      (conclusion_fiber_parity_balance_rowmotion_three_torsion_mod_one_iff_dvd_add_two
        (ell i)).mpr hi⟩

end Omega.Conclusion
