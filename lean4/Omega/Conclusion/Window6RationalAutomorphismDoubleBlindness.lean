import Omega.Conclusion.BoundaryPinningMemoryGap
import Omega.Conclusion.Window6BoundaryParityDirectSummandRationalBlindness

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-rational-automorphism-double-blindness`.
The boundary parity package gives the two rational blindness statements, while the boundary
pinning audit supplies the Grassmann orbit count bounds for `97155`. -/
theorem paper_conclusion_window6_rational_automorphism_double_blindness :
    (∀ n : ℕ, 0 < n → window6BoundaryPositiveDegreeRationalCohomology n = 0) ∧
      (∀ n : ℕ, 0 < n → window6ConnectedLieRationalBlindness n = 0) ∧
      (2 ^ 16 < 97155 ∧ 97155 ≤ 2 ^ 17) ∧
      97155 - 1 = 97154 := by
  rcases paper_conclusion_window6_boundary_parity_directsummand_rational_blindness with
    ⟨_hProjection, _hCard, hBoundaryBlind, hLieBlind⟩
  exact
    ⟨hBoundaryBlind, hLieBlind,
      ⟨BoundaryPinningMemoryGap.two_pow_16_lt_gaussian,
        BoundaryPinningMemoryGap.gaussian_le_two_pow_17⟩,
      by omega⟩

end Omega.Conclusion
