import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-artin-visible-hull-matrix-realization`. -/
theorem paper_conclusion_artin_visible_hull_matrix_realization
    {Quotient Image : Type} (toImage : Quotient → Image) (fromImage : Image → Quotient)
    (hleft : ∀ x : Quotient, fromImage (toImage x) = x)
    (hright : ∀ y : Image, toImage (fromImage y) = y) :
    (∀ x y : Quotient, toImage x = toImage y → x = y) ∧
      (∀ y : Image, ∃ x : Quotient, toImage x = y) := by
  constructor
  · intro x y hxy
    calc
      x = fromImage (toImage x) := (hleft x).symm
      _ = fromImage (toImage y) := by rw [hxy]
      _ = y := hleft y
  · intro y
    exact ⟨fromImage y, hright y⟩

end Omega.Conclusion
