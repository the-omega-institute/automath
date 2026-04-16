import Omega.GU.TerminalWindow6PushforwardCommutantMasa
import Omega.GU.TerminalWindow6PushforwardNoNonabelianCompactSymmetry

namespace Omega.GU

/-- Paper-facing wrapper for the torus-valued commutant audit: simple spectrum yields the
    polynomial commutant, hence the coordinate algebra and unitary torus; therefore every
    commuting compact symmetry image is abelian, and any faithful such image forces the source
    compact symmetry group to be abelian.
    cor:terminal-window-pushforward-commutant-torus -/
theorem paper_terminal_window_pushforward_commutant_torus
    (simpleSpectrum commutantIsPolynomial commutantIsC21 unitaryIsTorus21 masa
      imageInU1pow21 imageAbelian faithful groupAbelian : Prop)
    (hPoly : simpleSpectrum -> commutantIsPolynomial)
    (hC21 : commutantIsPolynomial -> commutantIsC21)
    (hTorus : commutantIsC21 -> unitaryIsTorus21)
    (hMasa : simpleSpectrum -> masa)
    (hImage : unitaryIsTorus21 -> imageInU1pow21)
    (hAbelian : imageInU1pow21 -> imageAbelian)
    (hFaithful : faithful -> imageAbelian -> groupAbelian)
    (hSimple : simpleSpectrum) :
    commutantIsPolynomial ∧ commutantIsC21 ∧ unitaryIsTorus21 ∧ masa ∧
      imageAbelian ∧ (faithful -> groupAbelian) := by
  rcases
      paper_terminal_window6_pushforward_commutant_masa simpleSpectrum commutantIsPolynomial
        commutantIsC21 unitaryIsTorus21 masa hPoly hC21 hTorus hMasa hSimple
    with ⟨hPolynomial, hC21', hTorus21, hMasa'⟩
  have hImageInU1pow21 : imageInU1pow21 := hImage hTorus21
  rcases
      paper_terminal_window6_pushforward_no_nonabelian_compact_symmetry imageInU1pow21 faithful
        imageAbelian groupAbelian hAbelian hFaithful hImageInU1pow21
    with ⟨hImageAbelian, hGroupAbelian⟩
  exact ⟨hPolynomial, hC21', hTorus21, hMasa', hImageAbelian, hGroupAbelian⟩

end Omega.GU
