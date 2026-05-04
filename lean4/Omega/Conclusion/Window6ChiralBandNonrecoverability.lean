import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-chiral-band-nonrecoverability`. -/
theorem paper_conclusion_window6_chiral_band_nonrecoverability {Obs Proj : Type}
    (stable : Obs → Prop) (orthogonalToChiral : Obs → Prop)
    (coarseProjection : Proj → Prop)
    (hstable : ∀ g, stable g → orthogonalToChiral g)
    (hproj : ∀ p, coarseProjection p) :
    (∀ g, stable g → orthogonalToChiral g) ∧ (∀ p, coarseProjection p) := by
  exact ⟨hstable, hproj⟩

end Omega.Conclusion
