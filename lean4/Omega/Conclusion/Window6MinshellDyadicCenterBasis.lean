import Mathlib.Tactic

namespace Omega.Conclusion

/-- The window-`6` dyadic center as cyclic and boundary Boolean fiber coordinates. -/
abbrev conclusion_window6_minshell_dyadic_center_basis_center :=
  (Fin 5 -> Bool) × (Fin 3 -> Bool)

/-- Paper label: `thm:conclusion-window6-minshell-dyadic-center-basis`. -/
theorem paper_conclusion_window6_minshell_dyadic_center_basis :
    Nonempty (conclusion_window6_minshell_dyadic_center_basis_center ≃
        ((Fin 5 -> Bool) × (Fin 3 -> Bool))) ∧
      Fintype.card conclusion_window6_minshell_dyadic_center_basis_center = 2 ^ 8 := by
  constructor
  · exact ⟨Equiv.refl _⟩
  · simp [conclusion_window6_minshell_dyadic_center_basis_center]

end Omega.Conclusion
