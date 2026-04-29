import Mathlib.Tactic
import Omega.Conclusion.FibadicDepthPacketBernoulliMobiusJet
import Omega.Conclusion.FibadicDepthPacketSlopeAtOne

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fibadic-bernoulli-jet-oldnew-budget-reciprocity`. -/
theorem paper_conclusion_fibadic_bernoulli_jet_oldnew_budget_reciprocity
    (d : Nat) (hd : 1 < d) (Qd Fd ad Pi PiDeriv PiSecond : ℚ) (hQd : Qd ≠ 0)
    (hPi_ne : Pi ≠ 0) (hConductor : Qd * Pi = Fd) (hSlope : 2 * PiDeriv = ad * Pi)
    (hSecondLog :
      PiDeriv / Pi + PiSecond / Pi - (PiDeriv / Pi) ^ 2 =
        conclusion_fibadic_depth_packet_bernoulli_mobius_jet_power_sum d 2 / 12) :
    2 * Qd * PiDeriv = ad * Fd ∧
      12 * Qd * PiSecond =
        (conclusion_fibadic_depth_packet_bernoulli_mobius_jet_power_sum d 2 +
            3 * ad * (ad - 2)) * Fd := by
  have _ : 1 < d := hd
  have _ : Qd ≠ 0 := hQd
  set S : ℚ := conclusion_fibadic_depth_packet_bernoulli_mobius_jet_power_sum d 2
  have hderiv_div : PiDeriv / Pi = ad / 2 := by
    have h := congrArg (fun x : ℚ => x / (2 * Pi)) hSlope
    have hleft : (2 * PiDeriv) / (2 * Pi) = PiDeriv / Pi := by
      field_simp [hPi_ne]
    have hright : (ad * Pi) / (2 * Pi) = ad / 2 := by
      field_simp [hPi_ne]
    simpa [hleft, hright] using h
  constructor
  · calc
      2 * Qd * PiDeriv = Qd * (2 * PiDeriv) := by ring
      _ = Qd * (ad * Pi) := by rw [hSlope]
      _ = ad * (Qd * Pi) := by ring
      _ = ad * Fd := by rw [hConductor]
  · have hsecond := hSecondLog
    rw [hderiv_div] at hsecond
    change ad / 2 + PiSecond / Pi - (ad / 2) ^ 2 = S / 12 at hsecond
    have hsecond_div : PiSecond / Pi = (S + 3 * ad * (ad - 2)) / 12 := by
      nlinarith
    change 12 * Qd * PiSecond = (S + 3 * ad * (ad - 2)) * Fd
    calc
      12 * Qd * PiSecond = 12 * Qd * Pi * (PiSecond / Pi) := by
        field_simp [hPi_ne]
      _ = 12 * Qd * Pi * ((S + 3 * ad * (ad - 2)) / 12) := by
        rw [hsecond_div]
      _ = (S + 3 * ad * (ad - 2)) * Fd := by
        rw [← hConductor]
        ring

end Omega.Conclusion
