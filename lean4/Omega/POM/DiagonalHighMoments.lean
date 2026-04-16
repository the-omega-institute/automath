namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the diagonal high-moment law in
    `2026_projection_ontological_mathematics_core_tams`.
    thm:diagonal-high-moments -/
theorem paper_projection_diagonal_high_moments
    (divergingTilt maxFiberBounds maxFiberGrowth diagonalHighMomentLaw diagonalSelfMoment : Prop)
    (hGrowth : divergingTilt → maxFiberBounds → maxFiberGrowth)
    (hLaw : maxFiberGrowth → diagonalHighMomentLaw)
    (hSelf : diagonalHighMomentLaw → diagonalSelfMoment)
    (hTilt : divergingTilt)
    (hBounds : maxFiberBounds) :
    diagonalHighMomentLaw ∧ diagonalSelfMoment := by
  have hAsymptotic : maxFiberGrowth := hGrowth hTilt hBounds
  have hDiagonal : diagonalHighMomentLaw := hLaw hAsymptotic
  exact ⟨hDiagonal, hSelf hDiagonal⟩

end Omega.POM
