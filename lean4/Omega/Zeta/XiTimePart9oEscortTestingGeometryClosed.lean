namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9o-escort-testing-geometry-closed`. -/
theorem paper_xi_time_part9o_escort_testing_geometry_closed
    (tvClosed bhattacharyyaClosed hellingerClosed bayesClosed : Prop) :
    tvClosed ->
      bhattacharyyaClosed ->
        hellingerClosed ->
          bayesClosed -> tvClosed ∧ bhattacharyyaClosed ∧ hellingerClosed ∧ bayesClosed := by
  intro htv hbh hh hb
  exact ⟨htv, hbh, hh, hb⟩

end Omega.Zeta
