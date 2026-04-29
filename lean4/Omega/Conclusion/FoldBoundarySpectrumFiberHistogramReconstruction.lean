import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fold-boundary-spectrum-fiber-histogram-reconstruction`.
Boundary spectra determine fibers, and degree preservation along fibers then determines degrees. -/
theorem paper_conclusion_fold_boundary_spectrum_fiber_histogram_reconstruction
    {X Spectrum Fiber : Type} (B : X → Spectrum) (F : X → Fiber) (d : X → ℕ)
    (hFiber : ∀ x y : X, B x = B y → F x = F y)
    (hDegree : ∀ x y : X, F x = F y → d x = d y) :
    (∀ x y : X, B x = B y → F x = F y) ∧
      (∀ x y : X, B x = B y → d x = d y) := by
  refine ⟨hFiber, ?_⟩
  intro x y hB
  exact hDegree x y (hFiber x y hB)

end Omega.Conclusion
