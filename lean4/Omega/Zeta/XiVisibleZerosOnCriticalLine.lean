import Omega.Zeta.XiOffsetNullTypeSafety

namespace Omega.Zeta

/-- Paper label: `cor:xi-visible-zeros-on-critical-line`. Any point that remains addressable in
the Peter-Weyl closure must lie on the critical line, since off-critical points are forced into the
`NULL` branch by `paper_xi_offset_null_type_safety`. -/
theorem paper_xi_visible_zeros_on_critical_line {L : Real} {s : Complex} (hL : 1 < L)
    (hAddr : xiOffsetPwClosureAddressable L s) : s.re = 1 / 2 := by
  by_contra hs
  exact (paper_xi_offset_null_type_safety hL hs).2.2 hAddr

end Omega.Zeta
