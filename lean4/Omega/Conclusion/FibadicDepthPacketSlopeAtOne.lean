import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-fibadic-depth-packet-slope-at-one`. -/
theorem paper_conclusion_fibadic_depth_packet_slope_at_one
    (d : ℕ) (hd : 1 < d) (Pi PiDeriv a : ℚ) (hPi : Pi ≠ 0)
    (hlogSlope : PiDeriv / Pi = a / 2) :
    2 * PiDeriv = a * Pi := by
  have _ : 1 < d := hd
  have hscaled := congrArg (fun x : ℚ => x * (2 * Pi)) hlogSlope
  have hleft : PiDeriv / Pi * (2 * Pi) = 2 * PiDeriv := by
    field_simp [hPi]
  have hright : a / 2 * (2 * Pi) = a * Pi := by
    ring
  simpa [hleft, hright] using hscaled

end Omega.Conclusion
