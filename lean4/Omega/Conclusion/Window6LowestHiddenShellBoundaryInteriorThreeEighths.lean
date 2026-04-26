import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`cor:conclusion-window6-lowest-hidden-shell-boundary-interior-three-eighths`.

The lowest hidden shell is modeled as the direct sum of three boundary sign lines and five
interior sign lines. The dimension count gives total dimension `8`, hence faithful-visible
boundary ratio `3 / 8`. -/
theorem paper_conclusion_window6_lowest_hidden_shell_boundary_interior_three_eighths :
    Module.finrank ℚ (Fin 3 → ℚ) = 3 ∧
      Module.finrank ℚ (Fin 5 → ℚ) = 5 ∧
      Module.finrank ℚ ((Fin 3 ⊕ Fin 5) → ℚ) = 8 ∧
      ((Module.finrank ℚ (Fin 3 → ℚ) : ℚ) /
          (Module.finrank ℚ ((Fin 3 ⊕ Fin 5) → ℚ) : ℚ) = 3 / 8) := by
  have hboundary : Module.finrank ℚ (Fin 3 → ℚ) = 3 := by
    simp
  have hinterior : Module.finrank ℚ (Fin 5 → ℚ) = 5 := by
    simp
  have htotal : Module.finrank ℚ ((Fin 3 ⊕ Fin 5) → ℚ) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  refine ⟨hboundary, hinterior, htotal, ?_⟩
  rw [hboundary, htotal]
  norm_num

end Omega.Conclusion
