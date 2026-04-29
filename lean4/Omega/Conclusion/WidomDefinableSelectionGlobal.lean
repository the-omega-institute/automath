import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-widom-definable-selection-global`. -/
theorem paper_conclusion_widom_definable_selection_global {P : Type*}
    {W : P -> Real × Real -> Prop}
    {continuousOnCells nashOnRegularCells : (P -> Real × Real) -> Prop}
    (hChoice : ∃ sigma : P -> Real × Real, (∀ T, W T (sigma T)) ∧ continuousOnCells sigma)
    (hNash : ∀ sigma, (∀ T, W T (sigma T)) -> continuousOnCells sigma ->
      nashOnRegularCells sigma) :
    ∃ sigma : P -> Real × Real,
      (∀ T, W T (sigma T)) ∧ continuousOnCells sigma ∧ nashOnRegularCells sigma := by
  rcases hChoice with ⟨sigma, hW, hContinuous⟩
  exact ⟨sigma, hW, hContinuous, hNash sigma hW hContinuous⟩

end Omega.Conclusion
