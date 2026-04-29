import Mathlib.Data.Nat.Basic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fibadic-depth-packet-onepoint-jet-certificate`. -/
theorem paper_conclusion_fibadic_depth_packet_onepoint_jet_certificate
    (d : ℕ)
    (primePowerDetected firstJetLocksMass secondJetRecoversS2 asymptoticMassRatio : Prop)
    (hdetect : 1 < d -> primePowerDetected)
    (hfirst : 1 < d -> firstJetLocksMass)
    (hsecond : 1 < d -> secondJetRecoversS2)
    (hasymp : asymptoticMassRatio) (hd : 1 < d) :
    primePowerDetected ∧ firstJetLocksMass ∧ secondJetRecoversS2 ∧ asymptoticMassRatio := by
  exact ⟨hdetect hd, hfirst hd, hsecond hd, hasymp⟩

end Omega.Conclusion
