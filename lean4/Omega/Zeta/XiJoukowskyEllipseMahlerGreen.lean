namespace Omega.Zeta

/-- Paper label: `thm:xi-joukowsky-ellipse-mahler-green`. -/
theorem paper_xi_joukowsky_ellipse_mahler_green
    (mahlerJensenIdentity ellipseAverageClosedForm greenNonnegativeCriterion : Prop)
    (hJensen : mahlerJensenIdentity)
    (hClosed : mahlerJensenIdentity → ellipseAverageClosedForm)
    (hGreen : ellipseAverageClosedForm → greenNonnegativeCriterion) :
    ellipseAverageClosedForm ∧ greenNonnegativeCriterion := by
  exact ⟨hClosed hJensen, hGreen (hClosed hJensen)⟩

end Omega.Zeta
