import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The audited fiber-gauge Laplacian spectrum for window-`6`. -/
def conclusion_window6_visible_cubic_spectral_certificate_spectrum : Multiset ℕ :=
  Multiset.replicate 21 0 + Multiset.replicate 8 2 + Multiset.replicate 8 3 +
    Multiset.replicate 27 4

/-- The cubic Lagrange-interpolation polynomial cutting out the visible projector. -/
def conclusion_window6_visible_cubic_spectral_certificate_projectorPolynomial (l : ℚ) : ℚ :=
  -((1 : ℚ) / 24) * (l - 2) * (l - 3) * (l - 4)

/-- Paper label: `cor:conclusion-window6-visible-cubic-spectral-certificate`. The spectrum
`{0^(21), 2^(8), 3^(8), 4^(27)}` recovers the degeneration histogram by dividing by the per-fiber
zero-sum multiplicity `d - 1`, and the visible projector is the cubic interpolation polynomial
equal to `1` at `0` and `0` at `2, 3, 4`. -/
theorem paper_conclusion_window6_visible_cubic_spectral_certificate :
    conclusion_window6_visible_cubic_spectral_certificate_spectrum.count 0 = 21 ∧
      conclusion_window6_visible_cubic_spectral_certificate_spectrum.count 2 = 8 ∧
      conclusion_window6_visible_cubic_spectral_certificate_spectrum.count 3 = 8 ∧
      conclusion_window6_visible_cubic_spectral_certificate_spectrum.count 4 = 27 ∧
      conclusion_window6_visible_cubic_spectral_certificate_spectrum.count 2 / (2 - 1) = 8 ∧
      conclusion_window6_visible_cubic_spectral_certificate_spectrum.count 3 / (3 - 1) = 4 ∧
      conclusion_window6_visible_cubic_spectral_certificate_spectrum.count 4 / (4 - 1) = 9 ∧
      conclusion_window6_visible_cubic_spectral_certificate_projectorPolynomial 0 = 1 ∧
      conclusion_window6_visible_cubic_spectral_certificate_projectorPolynomial 2 = 0 ∧
      conclusion_window6_visible_cubic_spectral_certificate_projectorPolynomial 3 = 0 ∧
      conclusion_window6_visible_cubic_spectral_certificate_projectorPolynomial 4 = 0 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, ?_, ?_, ?_, ?_⟩
  · norm_num [conclusion_window6_visible_cubic_spectral_certificate_projectorPolynomial]
  · norm_num [conclusion_window6_visible_cubic_spectral_certificate_projectorPolynomial]
  · norm_num [conclusion_window6_visible_cubic_spectral_certificate_projectorPolynomial]
  · norm_num [conclusion_window6_visible_cubic_spectral_certificate_projectorPolynomial]

end Omega.Conclusion
