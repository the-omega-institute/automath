import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-reversekl-zero-plateau-recovers-frequency`. -/
theorem paper_conclusion_reversekl_zero_plateau_recovers_frequency
    {Prime : Type*} (zeroPlateau valuation : Prime → Nat)
    (h : ∀ p, zeroPlateau p = valuation p) :
    zeroPlateau = valuation := by
  funext p
  exact h p

end Omega.Conclusion
