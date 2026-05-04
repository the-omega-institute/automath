import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9x-visible-condexp-finite-index-spectrum`. -/
theorem paper_xi_time_part9x_visible_condexp_finite_index_spectrum
    (fiberSize : Fin 21 → ℕ)
    (hvals : ∀ w, fiberSize w = 2 ∨ fiberSize w = 3 ∨ fiberSize w = 4)
    (h2 : (Finset.univ.filter (fun w : Fin 21 => fiberSize w = 2)).card = 8)
    (h3 : (Finset.univ.filter (fun w : Fin 21 => fiberSize w = 3)).card = 4)
    (h4 : (Finset.univ.filter (fun w : Fin 21 => fiberSize w = 4)).card = 9) :
    (∑ w : Fin 21, fiberSize w = 64) ∧
      (∑ w : Fin 21, fiberSize w ^ 2 = 212) ∧
        (((∑ w : Fin 21, fiberSize w ^ 2 : ℕ) : ℚ) / 64 = 53 / 16) := by
  classical
  let s2 : Finset (Fin 21) := Finset.univ.filter (fun w : Fin 21 => fiberSize w = 2)
  let s3 : Finset (Fin 21) := Finset.univ.filter (fun w : Fin 21 => fiberSize w = 3)
  let s4 : Finset (Fin 21) := Finset.univ.filter (fun w : Fin 21 => fiberSize w = 4)
  have hsum :
      (∑ w : Fin 21, fiberSize w) =
        ∑ w : Fin 21,
          ((if fiberSize w = 2 then 2 else 0) +
            (if fiberSize w = 3 then 3 else 0) +
              (if fiberSize w = 4 then 4 else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro w _
    rcases hvals w with h | h | h <;> simp [h]
  have hsq :
      (∑ w : Fin 21, fiberSize w ^ 2) =
        ∑ w : Fin 21,
          ((if fiberSize w = 2 then 4 else 0) +
            (if fiberSize w = 3 then 9 else 0) +
              (if fiberSize w = 4 then 16 else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro w _
    rcases hvals w with h | h | h <;> simp [h]
  have htwo : (∑ w : Fin 21, if fiberSize w = 2 then 2 else 0) = 16 := by
    rw [← Finset.sum_filter]
    simp [h2]
  have hthree : (∑ w : Fin 21, if fiberSize w = 3 then 3 else 0) = 12 := by
    rw [← Finset.sum_filter]
    simp [h3]
  have hfour : (∑ w : Fin 21, if fiberSize w = 4 then 4 else 0) = 36 := by
    rw [← Finset.sum_filter]
    simp [h4]
  have htwo_sq : (∑ w : Fin 21, if fiberSize w = 2 then 4 else 0) = 32 := by
    rw [← Finset.sum_filter]
    simp [h2]
  have hthree_sq : (∑ w : Fin 21, if fiberSize w = 3 then 9 else 0) = 36 := by
    rw [← Finset.sum_filter]
    simp [h3]
  have hfour_sq : (∑ w : Fin 21, if fiberSize w = 4 then 16 else 0) = 144 := by
    rw [← Finset.sum_filter]
    simp [h4]
  have hsum_eval : (∑ w : Fin 21, fiberSize w) = 64 := by
    rw [hsum]
    simp only [Finset.sum_add_distrib]
    rw [htwo, hthree, hfour]
  have hsq_eval : (∑ w : Fin 21, fiberSize w ^ 2) = 212 := by
    rw [hsq]
    simp only [Finset.sum_add_distrib]
    rw [htwo_sq, hthree_sq, hfour_sq]
  refine ⟨hsum_eval, hsq_eval, ?_⟩
  rw [hsq_eval]
  norm_num

end Omega.Zeta
