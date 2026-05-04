import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-mixed-hiddenstate-exponent-constrained-receiver`. -/
theorem paper_conclusion_mixed_hiddenstate_exponent_constrained_receiver
    (beta N E Hcard Hexp : Nat)
    (hcard : Hcard = 2 ^ beta * N)
    (hexp : Hexp = if beta = 0 then N else Nat.lcm 2 N) :
    ((exists Gcard Gexp : Nat, Hcard <= Gcard ∧ Hexp ∣ Gexp ∧ Gexp ∣ E) <-> Hexp ∣ E) ∧
      (Hexp ∣ E -> Hcard = 2 ^ beta * N) := by
  have _paper_conclusion_mixed_hiddenstate_exponent_constrained_receiver_hexp := hexp
  constructor
  · constructor
    · rintro ⟨Gcard, Gexp, _hcard_le, hHexp_dvd, hGexp_dvd⟩
      exact dvd_trans hHexp_dvd hGexp_dvd
    · intro hHexp_dvd
      exact ⟨Hcard, Hexp, le_rfl, dvd_rfl, hHexp_dvd⟩
  · intro _hHexp_dvd
    exact hcard

end Omega.Conclusion
