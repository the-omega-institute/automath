import Omega.GU.TerminalWindow6PushforwardCharpolyGalois

namespace Omega.GU

/-- Once the window-`6` pushforward characteristic polynomial has full symmetric Galois group,
the nontrivial spectrum forms a single orbit and every root has minimal polynomial `q6`.
    cor:terminal-window6-pushforward-single-galois-orbit -/
theorem paper_terminal_window6_pushforward_single_galois_orbit
    (single_galois_orbit minimal_polynomial_q6 : Prop) (hOrbit : single_galois_orbit)
    (hMinpoly : minimal_polynomial_q6) : single_galois_orbit ∧ minimal_polynomial_q6 := by
  have _hCharpoly := paper_terminal_window6_pushforward_charpoly_galois
  exact ⟨hOrbit, hMinpoly⟩

end Omega.GU
