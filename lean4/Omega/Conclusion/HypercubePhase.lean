import Mathlib.Tactic

open Finset

namespace Omega.Conclusion

/-- cor:conclusion-hypercube-phase-d6-only-sqrt2-sqrt5 -/
theorem hypercube_phase_d6_product_values :
    ∀ k : Fin 7, k.val * (6 - k.val) ∈ ({0, 5, 8, 9} : Finset ℕ) := by
  intro k; fin_cases k <;> simp

/-- cor:conclusion-hypercube-phase-d6-only-sqrt2-sqrt5 -/
theorem hypercube_phase_d6_product_surj :
    (Finset.image (fun k : Fin 7 => k.val * (6 - k.val)) Finset.univ)
      = {0, 5, 8, 9} := by
  ext x; simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · rintro ⟨k, rfl⟩; fin_cases k <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩
    · exact ⟨3, by simp⟩

/-- cor:conclusion-hypercube-phase-d6-only-sqrt2-sqrt5 -/
theorem hypercube_phase_d6_sqrt_classification :
    (8 : ℕ) = 2 * 2 ^ 2 ∧ Nat.sqrt 9 = 3 ∧ ¬ ∃ d : ℕ, 1 < d ∧ d ^ 2 ∣ 5 := by
  refine ⟨by norm_num, by native_decide, ?_⟩
  rintro ⟨d, hd, hdiv⟩
  have hle : d ^ 2 ≤ 5 := Nat.le_of_dvd (by norm_num) hdiv
  have hd2 : d ≤ 2 := by nlinarith [sq_nonneg d]
  interval_cases d; omega

end Omega.Conclusion
