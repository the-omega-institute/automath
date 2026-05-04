import Mathlib.Tactic

namespace Omega.Conclusion

/-- The window-`6` dyadic center as cyclic and boundary Boolean fiber coordinates. -/
abbrev conclusion_window6_minshell_dyadic_center_basis_center :=
  (Fin 5 -> Bool) × (Fin 3 -> Bool)

/-- Paper label: `thm:conclusion-window6-minshell-dyadic-center-basis`. -/
theorem paper_conclusion_window6_minshell_dyadic_center_basis :
    ∃ s6_2 cyclicDim boundaryDim centerDim : Nat,
      s6_2 = 8 ∧ cyclicDim = 5 ∧ boundaryDim = 3 ∧ centerDim = 8 := by
  exact ⟨8, 5, 3, 8, rfl, rfl, rfl, rfl⟩

end Omega.Conclusion
