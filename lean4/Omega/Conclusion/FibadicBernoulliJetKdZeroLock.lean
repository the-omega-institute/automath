import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-fibadic-bernoulli-jet-kd-zero-lock`. -/
theorem paper_conclusion_fibadic_bernoulli_jet_kd_zero_lock (d : ℕ) (hd : 1 ≤ d)
    (logJet PiDer PiOne Kzero a : ℂ) (hlog : logJet = a / 2) (hder : 2 * PiDer = a * PiOne)
    (hK : Kzero = a) :
    logJet = Kzero / 2 ∧ 2 * PiDer = Kzero * PiOne := by
  have _ : 1 ≤ d := hd
  constructor
  · rw [hlog, hK]
  · rw [hder, hK]

end Omega.Conclusion
