import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fold-boundary-walsh-stokes-complete-tomography`. -/
theorem paper_conclusion_fold_boundary_walsh_stokes_complete_tomography {Ω X B : Type*}
    [DecidableEq X] (Fold : Ω → X) (boundaryData : X → B)
    (fiberIndicator : X → Ω → Bool)
    (hBoundary : ∀ {x y : X}, boundaryData x = boundaryData y →
      fiberIndicator x = fiberIndicator y)
    (hIndicator : ∀ x ω, fiberIndicator x ω = decide (Fold ω = x)) {x y : X} :
    boundaryData x = boundaryData y → (∀ ω, Fold ω = x ↔ Fold ω = y) := by
  intro hxy ω
  have hFiber : fiberIndicator x = fiberIndicator y := hBoundary hxy
  have hAt : fiberIndicator x ω = fiberIndicator y ω := congrArg (fun f => f ω) hFiber
  rw [hIndicator x ω, hIndicator y ω] at hAt
  constructor
  · intro hx
    have hyBool : decide (Fold ω = y) = true := by
      rw [← hAt]
      simp [hx]
    exact of_decide_eq_true hyBool
  · intro hy
    have hxBool : decide (Fold ω = x) = true := by
      rw [hAt]
      simp [hy]
    exact of_decide_eq_true hxBool

end Omega.Conclusion
