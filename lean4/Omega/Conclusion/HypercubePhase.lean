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

/-- d=4 hypercube phase products lie in {0, 3, 4}.
    cor:conclusion-hypercube-phase-d6-only-sqrt2-sqrt5 -/
theorem hypercube_phase_d4_product_values :
    ∀ k : Fin 5, k.val * (4 - k.val) ∈ ({0, 3, 4} : Finset ℕ) := by
  intro k; fin_cases k <;> simp

/-- d=8 hypercube phase products lie in {0, 7, 12, 15, 16}.
    cor:conclusion-hypercube-phase-d6-only-sqrt2-sqrt5 -/
theorem hypercube_phase_d8_product_values :
    ∀ k : Fin 9, k.val * (8 - k.val) ∈ ({0, 7, 12, 15, 16} : Finset ℕ) := by
  intro k; fin_cases k <;> simp

/-- d=4 image of phase product map equals {0, 3, 4}.
    cor:conclusion-hypercube-phase-d6-only-sqrt2-sqrt5 -/
theorem hypercube_phase_d4_product_surj :
    (Finset.image (fun k : Fin 5 => k.val * (4 - k.val)) Finset.univ)
      = {0, 3, 4} := by
  ext x; simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · rintro ⟨k, rfl⟩; fin_cases k <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩

/-- d=8 image of phase product map equals {0, 7, 12, 15, 16}.
    cor:conclusion-hypercube-phase-d6-only-sqrt2-sqrt5 -/
theorem hypercube_phase_d8_product_surj :
    (Finset.image (fun k : Fin 9 => k.val * (8 - k.val)) Finset.univ)
      = {0, 7, 12, 15, 16} := by
  ext x; simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · rintro ⟨k, rfl⟩; fin_cases k <;> simp
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩
    · exact ⟨3, by simp⟩
    · exact ⟨4, by simp⟩

/-- Complete d=4/6/8 hypercube phase package.
    cor:conclusion-hypercube-phase-d6-only-sqrt2-sqrt5 -/
theorem paper_hypercube_phase_package_d4_d6_d8 :
    (∀ k : Fin 5, k.val * (4 - k.val) ∈ ({0, 3, 4} : Finset ℕ)) ∧
    (∀ k : Fin 7, k.val * (6 - k.val) ∈ ({0, 5, 8, 9} : Finset ℕ)) ∧
    (∀ k : Fin 9, k.val * (8 - k.val) ∈ ({0, 7, 12, 15, 16} : Finset ℕ)) ∧
    (Finset.image (fun k : Fin 5 => k.val * (4 - k.val)) Finset.univ = {0, 3, 4}) ∧
    (Finset.image (fun k : Fin 7 => k.val * (6 - k.val)) Finset.univ = {0, 5, 8, 9}) ∧
    (Finset.image (fun k : Fin 9 => k.val * (8 - k.val)) Finset.univ = {0, 7, 12, 15, 16}) :=
  ⟨hypercube_phase_d4_product_values,
   hypercube_phase_d6_product_values,
   hypercube_phase_d8_product_values,
   hypercube_phase_d4_product_surj,
   hypercube_phase_d6_product_surj,
   hypercube_phase_d8_product_surj⟩

/-- d=10 hypercube phase products lie in {0, 9, 16, 21, 24, 25}.
    cor:conclusion-hypercube-phase-d6-only-sqrt2-sqrt5 -/
theorem hypercube_phase_d10_product_values :
    ∀ k : Fin 11, k.val * (10 - k.val) ∈ ({0, 9, 16, 21, 24, 25} : Finset ℕ) := by
  intro k; fin_cases k <;> simp

/-- d=12 hypercube phase products lie in {0, 11, 20, 27, 32, 35, 36}.
    cor:conclusion-hypercube-phase-d6-only-sqrt2-sqrt5 -/
theorem hypercube_phase_d12_product_values :
    ∀ k : Fin 13, k.val * (12 - k.val) ∈ ({0, 11, 20, 27, 32, 35, 36} : Finset ℕ) := by
  intro k; fin_cases k <;> simp

/-- d=10 image of phase product map equals {0, 9, 16, 21, 24, 25}.
    cor:conclusion-hypercube-phase-d6-only-sqrt2-sqrt5 -/
theorem hypercube_phase_d10_product_surj :
    (Finset.image (fun k : Fin 11 => k.val * (10 - k.val)) Finset.univ)
      = {0, 9, 16, 21, 24, 25} := by
  ext x; simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · rintro ⟨k, rfl⟩; fin_cases k <;> simp
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩
    · exact ⟨3, by simp⟩
    · exact ⟨4, by simp⟩
    · exact ⟨5, by simp⟩

/-- Complete d=4..12 hypercube phase product-value package.
    cor:conclusion-hypercube-phase-d6-only-sqrt2-sqrt5 -/
theorem paper_hypercube_phase_package_d4_to_d12 :
    (∀ k : Fin 5, k.val * (4 - k.val) ∈ ({0, 3, 4} : Finset ℕ)) ∧
    (∀ k : Fin 7, k.val * (6 - k.val) ∈ ({0, 5, 8, 9} : Finset ℕ)) ∧
    (∀ k : Fin 9, k.val * (8 - k.val) ∈ ({0, 7, 12, 15, 16} : Finset ℕ)) ∧
    (∀ k : Fin 11, k.val * (10 - k.val) ∈ ({0, 9, 16, 21, 24, 25} : Finset ℕ)) ∧
    (∀ k : Fin 13, k.val * (12 - k.val) ∈ ({0, 11, 20, 27, 32, 35, 36} : Finset ℕ)) :=
  ⟨hypercube_phase_d4_product_values,
   hypercube_phase_d6_product_values,
   hypercube_phase_d8_product_values,
   hypercube_phase_d10_product_values,
   hypercube_phase_d12_product_values⟩

end Omega.Conclusion
