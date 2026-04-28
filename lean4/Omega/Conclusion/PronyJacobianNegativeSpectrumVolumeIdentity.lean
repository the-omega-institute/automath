import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-prony-jacobian-negative-spectrum-volume-identity`. -/
theorem paper_conclusion_prony_jacobian_negative_spectrum_volume_identity {κ : Nat}
    (w lambda : Fin κ → ℝ) (jac : ℝ)
    (hpos : ∀ j, 0 < w j)
    (hdet :
      |jac| =
        (∏ i, |lambda i|) / ((4 * Real.pi) ^ κ * ∏ j, w j)) :
    (∏ i, |lambda i|) = (4 * Real.pi) ^ κ * (∏ j, w j) * |jac| := by
  have hfourpi_pos : 0 < (4 : ℝ) * Real.pi := by positivity
  have hden_pos : 0 < (4 * Real.pi) ^ κ * ∏ j, w j := by
    exact mul_pos (pow_pos hfourpi_pos κ) (Finset.prod_pos (fun j _ => hpos j))
  let A : ℝ := ∏ i, |lambda i|
  let D : ℝ := (4 * Real.pi) ^ κ * ∏ j, w j
  have hD_ne : D ≠ 0 := by
    exact ne_of_gt (by simpa [D] using hden_pos)
  have hdet' : |jac| = A / D := by
    simpa [A, D] using hdet
  change A = D * |jac|
  rw [hdet']
  field_simp [hD_ne]

end Omega.Conclusion
