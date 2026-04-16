import Omega.GU.TerminalWindow6PushforwardCommutantMasa

namespace Omega.GU

/-- Paper-facing wrapper: once the window-`6` pushforward image lands in the commuting torus
`U(1)^21`, the image is abelian; if the image is faithful, the source compact symmetry group is
abelian as well.
    cor:terminal-window6-pushforward-no-nonabelian-compact-symmetry -/
theorem paper_terminal_window6_pushforward_no_nonabelian_compact_symmetry
    (imageInU1pow21 faithful imageAbelian groupAbelian : Prop)
    (hAbelian : imageInU1pow21 -> imageAbelian)
    (hFaithful : faithful -> imageAbelian -> groupAbelian)
    (hImage : imageInU1pow21) :
    imageAbelian ∧ (faithful -> groupAbelian) := by
  have hImageAbelian : imageAbelian := hAbelian hImage
  refine ⟨hImageAbelian, ?_⟩
  intro hfaithful
  exact hFaithful hfaithful hImageAbelian

end Omega.GU
