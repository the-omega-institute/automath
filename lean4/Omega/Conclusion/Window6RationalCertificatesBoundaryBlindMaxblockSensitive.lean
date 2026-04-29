import Mathlib.Tactic
import Omega.Conclusion.Window6BoundaryParityDirectSummandRationalBlindness
import Omega.Conclusion.Window6RationalHomotopyDeterminesGaugeVolume

namespace Omega.Conclusion

/-- Paper label:
`cor:conclusion-window6-rational-certificates-boundary-blind-maxblock-sensitive`.
The degree-`7` rational homotopy audit forces the window-`6` maximal `4 × 4` block count to be
`9`, while the boundary-parity direct summand stays invisible to positive-degree rational
continuous certificates. -/
theorem paper_conclusion_window6_rational_certificates_boundary_blind_maxblock_sensitive
    (n2 n3 n4 : ℕ) (hr3 : 21 = n2 + n3 + n4) (hr5 : 13 = n3 + n4) (hr7 : 9 = n4) :
    n2 = 8 ∧
      n3 = 4 ∧
      n4 = 9 ∧
      Function.LeftInverse Omega.GU.window6BoundaryCartanProjection
        Omega.GU.window6BoundaryCartanInclusion ∧
      Fintype.card Omega.GU.Window6BoundaryParityBlock = 3 ∧
      (∀ n : ℕ, 0 < n → window6BoundaryPositiveDegreeRationalCohomology n = 0) ∧
      (∀ n : ℕ, 0 < n → window6ConnectedLieRationalBlindness n = 0) := by
  rcases
      paper_conclusion_window6_rational_homotopy_determines_gauge_volume
        n2 n3 n4 hr3 hr5 hr7 with
    ⟨hn2, hn3, hn4, _, _, _, _, _, _, _⟩
  rcases paper_conclusion_window6_boundary_parity_directsummand_rational_blindness with
    ⟨hLeftInv, hCard, hRat, hLie⟩
  exact ⟨hn2, hn3, hn4, hLeftInv, hCard, hRat, hLie⟩

end Omega.Conclusion
