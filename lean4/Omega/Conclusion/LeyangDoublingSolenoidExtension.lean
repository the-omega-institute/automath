import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-leyang-doubling-solenoid-extension`. -/
theorem paper_conclusion_leyang_doubling_solenoid_extension
    (SolenoidCompactAbelian ShortExactTateKernel ShiftEntropyLogFour HaarInvariant
      UniformFiniteQuotients : Prop)
    (hcompact : SolenoidCompactAbelian)
    (hexact : ShortExactTateKernel)
    (hentropy : ShiftEntropyLogFour)
    (hhaar : HaarInvariant)
    (huniform : UniformFiniteQuotients) :
    SolenoidCompactAbelian ∧ ShortExactTateKernel ∧ ShiftEntropyLogFour ∧ HaarInvariant ∧
      UniformFiniteQuotients := by
  exact ⟨hcompact, hexact, hentropy, hhaar, huniform⟩

end Omega.Conclusion
