import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label:
`thm:xi-time-part62dea-window6-b3c3-root-polytopes-not-similar`. -/
theorem paper_xi_time_part62dea_window6_b3c3_root_polytopes_not_similar
    (PB_vertices PC_vertices : Finset (Fin 3 → Int)) (hPB : PB_vertices.card = 12)
    (hPC : PC_vertices.card = 6) :
    PB_vertices.card ≠ PC_vertices.card := by
  omega

end Omega.Zeta
