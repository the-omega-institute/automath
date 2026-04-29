import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-terminal-zm-b2-kappa2-rational-interconstruction`. -/
theorem paper_xi_terminal_zm_b2_kappa2_rational_interconstruction
    (u b lambda : ℚ)
    (hlden : 4 * (3 * u - 2) ≠ 0)
    (hbden : 3 * (1831 * lambda ^ 2 + 144 * lambda - 175) ≠ 0)
    (huden : 51084 * u ^ 2 - 44412 * u + 8735 ≠ 0)
    (hlambda : lambda = (3 * (2 * u - 1)) / (4 * (3 * u - 2)))
    (hb :
      b =
        (2 * (1113 * lambda ^ 2 - 2192 * lambda + 303)) /
          (3 * (1831 * lambda ^ 2 + 144 * lambda - 175))) :
    b =
      -2 * ((24708 * u ^ 2 - 28628 * u + 7733) /
        (51084 * u ^ 2 - 44412 * u + 8735)) := by
  have _ : 3 * (1831 * lambda ^ 2 + 144 * lambda - 175) ≠ 0 := hbden
  have _ : 51084 * u ^ 2 - 44412 * u + 8735 ≠ 0 := huden
  have hden0 : 3 * u - 2 ≠ 0 := by
    intro h
    exact hlden (by simp [h])
  have hnum :
      2 *
          (1113 * ((3 * (2 * u - 1)) / (4 * (3 * u - 2))) ^ 2 -
            2192 * ((3 * (2 * u - 1)) / (4 * (3 * u - 2))) + 303) =
        -3 * (24708 * u ^ 2 - 28628 * u + 7733) / (8 * (3 * u - 2) ^ 2) := by
    field_simp [hden0]
    ring_nf
  have hden :
      3 *
          (1831 * ((3 * (2 * u - 1)) / (4 * (3 * u - 2))) ^ 2 +
            144 * ((3 * (2 * u - 1)) / (4 * (3 * u - 2))) - 175) =
        3 * (51084 * u ^ 2 - 44412 * u + 8735) / (16 * (3 * u - 2) ^ 2) := by
    field_simp [hden0]
    ring_nf
  rw [hb, hlambda, hnum, hden]
  field_simp [hden0, huden]
  ring_nf

end Omega.Zeta
