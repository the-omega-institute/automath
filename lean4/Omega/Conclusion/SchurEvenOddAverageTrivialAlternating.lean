import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-schur-even-odd-average-trivial-alternating`. -/
theorem paper_conclusion_schur_even_odd_average_trivial_alternating
    {Ttriv Talt Aplus Aminus : ℝ} (hplus : Aplus = Ttriv + Talt)
    (hminus : Aminus = Ttriv - Talt) (hAplus : 0 ≤ Aplus) (hAminus : 0 ≤ Aminus) :
    Talt = (Aplus - Aminus) / 2 ∧
      Ttriv = (Aplus + Aminus) / 2 ∧
      |Talt| ≤ Ttriv := by
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · linarith
  · exact abs_le.mpr ⟨by linarith, by linarith⟩

end Omega.Conclusion
